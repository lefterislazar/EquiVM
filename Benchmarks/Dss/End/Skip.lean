import Benchmarks.Dss.End.SnipAfterYank
import Benchmarks.Dss.End.RuntimeBlocks_007
import Benchmarks.Dss.End.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)` -/

abbrev endSkipStore (I : ExecutionEnv) : Store :=
  endSnipStore I

abbrev endSkipTagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  endSnipTagWord evm I

abbrev endSkipTagWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSnipTagWorldWord σ I

abbrev endSkipCatTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endCageSlotTarget σ I (UInt256.ofNat 2)

theorem endDecode_legacyBytes32_uint256_skip_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
        (skipTransition.params.map Param.name) (transitionSignature skipTransition).paramTypes
        I.calldata =
      some (endSkipStore I) := by
  simpa [config, skipTransition, transitionSignature, bytes32, uint256, endSkipStore] using
    endDecode_legacyBytes32_uint256_snip_ok (I := I) hsz68

theorem endDecode_legacyBytes32_uint256_skip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode
        (skipTransition.params.map Param.name) (transitionSignature skipTransition).paramTypes
        I.calldata = none := by
  simpa [config, skipTransition, transitionSignature, bytes32, uint256] using
    endDecode_legacyBytes32_uint256_snip_none_short (I := I) hsz4 hshort

theorem endSkipCatTarget_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) :
    UInt256.land
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨2⟩)
        solcAddrMask =
      endSkipCatTarget σ I := by
  rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 by rfl]
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, Batteries.RBMap.findD, endSkipCatTarget, endCageSlotTarget,
    storageRead_eq, u256_land_comm]

theorem endSkipCatTarget_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    endSkipCatTarget σ I = endSkipCatTarget τ I := by
  have hCatRead :
      storageRead I.codeOwner σ (UInt256.ofNat 2) =
        storageRead I.codeOwner τ (UInt256.ofNat 2) := by
    simpa [storageRead_eq] using
      accountMapEquiv_storage_findD hστ I.codeOwner (UInt256.ofNat 2) (default : UInt256)
  unfold endSkipCatTarget endCageSlotTarget
  rw [hCatRead]

theorem endSkipCatCodeSize_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    extCodeSizeWord σ (endSkipCatTarget σ I) =
      extCodeSizeWord τ (endSkipCatTarget τ I) := by
  have htarget := endSkipCatTarget_accountMapEquiv (I := I) hστ
  rw [htarget]
  exact extCodeSizeWord_accountMapEquiv hστ (endSkipCatTarget τ I)

theorem endSkipStore_get_cat_none (I : ExecutionEnv) :
    (endSkipStore I).get? "cat" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))).get? "cat") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "cat") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "cat")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalCatAddress_skip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.storage catRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := endSkipStore I) (evm := evm) (slot := catRef)
    (er := { base := "cat", steps := [] }) (wordSlot := UInt256.ofNat 2)
    (by simpa [catRef] using endSkipStore_get_cat_none I)
    (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind])
    (by decide)
    (by
      rw [show (UInt256.ofNat 2) = (⟨2⟩ : UInt256) from by native_decide]
      exact endConfig_storage_cat)

theorem endEvalCatCodeGuard_skip_false (evm : EVM.State) (I : ExecutionEnv)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := endSkipStore I) (evm := evm) (receiver := .storage catRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask)
    (endEvalCatAddress_skip evm I) hnocode

theorem endEvalCatCodeGuard_skip_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := endSkipStore I) (evm := evm) (receiver := .storage catRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask)
    (endEvalCatAddress_skip evm I) hcode

theorem endEvalSkipCatIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endSkipStore I } evm
      [.var "ilk"] = .ok [endArg0Bytes32Value I] := by
  simpa [endSkipStore] using endEvalSnipDogIlksArgs evm I

theorem endSkipBodyTagFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSkipStore I) skipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skipTransition, checkedExternalCallStmts, nonpayable, endSkipStore,
    endSkipTagWord] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalTagGuard_snip_false evm I hsz68 htag)))

theorem endSkipBodyCatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord evm I ≠ ⟨0⟩)
    (hcatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSkipStore I) skipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skipTransition, checkedExternalCallStmts, nonpayable, endSkipStore,
    endSkipTagWord] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_snip_true evm I hsz68 htag)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalCatCodeGuard_skip_false evm I hcatNoCode)))

theorem endSkipBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord evm I ≠ ⟨0⟩)
    (hcatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkipStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endSkipStore I } evm) := by
  simpa [nonpayable, endSkipStore, endSkipTagWord] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_snip_true evm I hsz68 htag)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalCatCodeGuard_skip_true evm I hcatCode)) <|
      ExecBlock.nil)

theorem endX_skip_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd690 := endRuntimeBlocks.endRuntime_block_672_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_690
    (R := endRuntimeBlocks.endRuntime_block_672_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_672_fallthrough_stack])
    (by simpa using rd690)

theorem endX_skip_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3224⟩
      [endArg1Word I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd694 := endRuntimeBlocks.endRuntime_block_672_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd3224 := endRuntimeBlocks.endRuntime_block_694
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_672_taken_stack] using rd694)
  have hoff4 : (UInt256.ofNat 4).toNat = 4 := by native_decide
  have hoff36 : ((UInt256.ofNat 32) + (UInt256.ofNat 4)).toNat = 36 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_694_stack, endArg1Word, endArg0Word,
      calldataWord, hoff4, hoff36] using rd3224⟩

theorem endX_skip_tag_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkipTagWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_skip_to_body (g := g) hsz68 hsize hreach
  have hcond :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) =
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkipTagWorldWord σ I = ⟨0⟩
    exact htag
  obtain ⟨_, _, rd3244⟩ := endRuntimeBlocks.endRuntime_block_3224_fallthrough
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcond (by simpa using rdBody)
  exact endRuntimeBlocks.endRuntime_block_3244
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_3224_fallthrough_memory] using rd3244)

theorem endX_skip_cat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkipTagWorldWord σ I ≠ ⟨0⟩)
    (hcatNoCode : extCodeSizeWord σ (endSkipCatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_skip_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkipTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw3314, k3314, C3314, rd3314⟩ :=
    endRuntimeBlocks.endRuntime_block_3224_taken_packed
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondTag (by jump_dest) (by simpa using rdBody)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ (UInt256.ofNat 2)) =
        endSkipCatTarget σ I := by
    rw [hmaskGenerated]
    unfold endSkipCatTarget endCageSlotTarget
    rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 2))]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 2))))) =
        UInt256.ofNat 0 := by
    rw [htarget, hcatNoCode]
    native_decide
  obtain ⟨_, _, _, rd3387⟩ :=
    endRuntimeBlocks.endRuntime_block_3314_fallthrough_packed
      (mem := endSkimVatIlksBaseMem I)
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode
      (by simpa [endSkimVatIlksBaseMem,
        endRuntimeBlocks.endRuntime_block_3224_taken_memory,
        endRuntimeBlocks.endRuntime_block_6705_taken_memory] using rd3314)
  exact endRuntimeBlocks.endRuntime_block_3387
    (R := endRuntimeBlocks.endRuntime_block_3314_fallthrough_stack
      (ee := I) (mem := endSkimVatIlksBaseMem I) (σ := σ)
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_3314_fallthrough_stack])
    rd3387

abbrev endSkipCatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  endSkimVatIlksBaseMem I

abbrev endSkipCatIlksCallMem (I : ExecutionEnv) : ByteArray :=
  endSkimVatIlksCallMem I

abbrev endSkipCatIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endSkipCatTarget σ I, ⟨0⟩,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipCatIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endSkipCatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨96⟩] ++
    endSkipCatIlksCallRest σ I sel

abbrev endSkipCatIlksCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) :
    Cursor :=
  { pc := ⟨3393⟩, stack := endSkipCatIlksCallStack σ I sel,
    mem := endSkipCatIlksCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endSkipCatIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨96⟩ : UInt256).toNat)

abbrev endSkipCatIlksReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endSkipCatIlksCallMem I) 128
    (min (⟨96⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endSkipAfterCatIlksAw (aw : UInt256) : UInt256 :=
  M (endSkipCatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSkipCatIlksFlipWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endSkipCatIlksWord1 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endSkipCatIlksWord2 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endSkipCatIlksValues (out : ByteArray) : List Value :=
  [.address (AccountAddress.ofNat (endSkipCatIlksFlipWord out).toNat),
    endUIntValue (endSkipCatIlksWord1 out),
    endUIntValue (endSkipCatIlksWord2 out)]

abbrev endSkipAfterCatIlksFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkipStore I).insert "catIlk" (collapseReturns (endSkipCatIlksValues out)) }

abbrev endSkipAfterCatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨3433⟩,
    stack := [UInt256.ofNat out.size,
      memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I out),
      ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSkipCatIlksReturnMem I out,
    aw := endSkipAfterCatIlksAw aw,
    rdata := out,
    world := world }

abbrev endSkipFlipValue (out : ByteArray) : Value :=
  .address (AccountAddress.ofNat (endSkipCatIlksFlipWord out).toNat)

abbrev endSkipAfterFlipFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkipAfterCatIlksFrame I out).locals.insert "flip"
      (endSkipFlipValue out) }

theorem endExternalEncode_catIlks (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "catIlks" [endArg0Bytes32Value I] =
      some (endFlowVatIlksEncodedCall I) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "catIlks" = "cage")]
  rw [if_neg (by decide : ¬ "catIlks" = "vatIlks")]
  rw [if_pos (by decide : "catIlks" = "catIlks")]
  exact endEncodeCallWithSelector_vatIlks I hsz36

theorem endSkipDecodeScalarWordsWithMode_legacy_addr_uint256x2_ok {out : ByteArray}
    (h96 : 96 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256] out.toList 0 =
      some (endSkipCatIlksValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
        some (.address (AccountAddress.ofNat (endSkipCatIlksFlipWord out).toNat),
          0 + 32) := by
    simpa [addr, abiAddress, endSkipCatIlksFlipWord, List.drop_zero] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endUIntValue (endSkipCatIlksWord1 out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSkipCatIlksWord1, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
        some (endUIntValue (endSkipCatIlksWord2 out), 64 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSkipCatIlksWord2, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]

theorem endSkipDecodeScalarWordsWithMode_legacy_addr_uint256x2_none_short
    {out : ByteArray} (hshort : out.size < 96) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256] out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          some (.address (AccountAddress.ofNat (endSkipCatIlksFlipWord out).toNat),
            0 + 32) := by
      simpa [addr, abiAddress, endSkipCatIlksFlipWord, List.drop_zero] using
        (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endUIntValue (endSkipCatIlksWord1 out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endSkipCatIlksWord1, endUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind, Nat.reduceAdd]
      have h64 : ¬ ((out.toList.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hlen]
        omega
      have hnone64 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
            none := by
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList)
            (start := 64) h64)
      rw [hnone64]
    · have hnone32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            none := by
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList)
            (start := 32) h32)
      rw [hnone32]
  · have hnone0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 = none := by
      simpa [addr, abiAddress] using
        (decodeScalarWord_legacyAddress_none_short
          (bytes := out.toList) (start := 0) h0)
    rw [hnone0]
    rfl

theorem endSkipDecodeReturnValues_legacy_catIlks_ok {out : ByteArray}
    (h96 : 96 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256, uint256] out =
      some (endSkipCatIlksValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256, uint256] = some 96 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 96)
    (by decide) (by decide)]
  rw [endSkipDecodeScalarWordsWithMode_legacy_addr_uint256x2_ok h96]

theorem endSkipDecodeReturnValues_legacy_catIlks_none_short {out : ByteArray}
    (hshort : out.size < 96) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256, uint256] out =
      none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256, uint256] = some 96 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 96)
    (by decide) (by decide)]
  rw [endSkipDecodeScalarWordsWithMode_legacy_addr_uint256x2_none_short hshort]

theorem endExternalDecode_catIlks_ok {out : ByteArray} (h96 : 96 ≤ out.size) :
    config.externalABI.decode? "catIlks" out = some (endSkipCatIlksValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "catIlks" = "cage")]
  rw [if_neg (by decide : ¬ "catIlks" = "vatIlks")]
  rw [if_pos (by decide : "catIlks" = "catIlks")]
  exact endSkipDecodeReturnValues_legacy_catIlks_ok h96

theorem endExternalDecode_catIlks_none_short {out : ByteArray}
    (hshort : out.size < 96) :
    config.externalABI.decode? "catIlks" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "catIlks" = "cage")]
  rw [if_neg (by decide : ¬ "catIlks" = "vatIlks")]
  rw [if_pos (by decide : "catIlks" = "catIlks")]
  exact endSkipDecodeReturnValues_legacy_catIlks_none_short hshort

theorem endX_skip_to_cat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkipTagWorldWord σ I ≠ ⟨0⟩)
    (hcatCode : extCodeSizeWord σ (endSkipCatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3393⟩
      (endSkipCatIlksCallStack σ I sel) (endSkipCatIlksCallMem I) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_skip_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkipTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw3314, k3314, C3314, rd3314⟩ :=
    endRuntimeBlocks.endRuntime_block_3224_taken_packed
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondTag (by jump_dest) (by simpa using rdBody)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ (UInt256.ofNat 2)) =
        endSkipCatTarget σ I := by
    rw [hmaskGenerated]
    unfold endSkipCatTarget endCageSlotTarget
    rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 2))]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 2))))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner σ (UInt256.ofNat 2))) ≠ UInt256.ofNat 0 := by
      rw [htarget]
      exact hcatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw3391, k3391, C3391, rd3391⟩ :=
    endRuntimeBlocks.endRuntime_block_3314_taken_packed
      (mem := endSkipCatIlksBaseMem I)
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSkipCatIlksBaseMem, endSkimVatIlksBaseMem,
        endRuntimeBlocks.endRuntime_block_3224_taken_memory,
        endRuntimeBlocks.endRuntime_block_6705_taken_memory] using rd3314)
  have hbase : memLoad (UInt256.ofNat 64) (endSkipCatIlksBaseMem I) = ⟨128⟩ := by
    simpa [endSkipCatIlksBaseMem] using endSkimVatIlksBaseMem_mload64 I
  have hcall :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_3314_taken_memory
          (mem := endSkipCatIlksBaseMem I) (x1 := endArg0Word I)) = ⟨128⟩ := by
    simpa [endSkipCatIlksBaseMem, endSkipCatIlksCallMem, endSkimVatIlksCallMem,
      endRuntimeBlocks.endRuntime_block_3314_taken_memory,
      endRuntimeBlocks.endRuntime_block_6795_taken_memory] using
      endSkimVatIlksCallMem_mload64 I
  have hcallAfterBase :
      memLoad (UInt256.ofNat 64)
        ((endArg0Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write
            0 (endSkipCatIlksBaseMem I) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_3314_taken_memory, hbase] using hcall
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_3314_taken_stack (ee := I)
          (mem := endSkipCatIlksBaseMem I) (σ := σ)
          (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord σ (endSkipCatTarget σ I)) ::
          endSkipCatIlksCallStack σ I sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_3314_taken_stack,
      endSkipCatIlksCallStack, endSkipCatIlksCallRest, endSkipCatTarget,
      endCageSlotTarget, endFlowVatIlksSelectorWord]
    rw [hbase, hcallAfterBase, hlen, hend, hmaskGenerated]
    rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 2))]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 96 = (⟨96⟩ : UInt256) from by native_decide]
  have rd3391' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3391⟩
        (UInt256.isZero (extCodeSizeWord σ (endSkipCatTarget σ I)) ::
          endSkipCatIlksCallStack σ I sel)
        (endSkipCatIlksCallMem I) aw3391 ByteArray.empty (cA, σ) k3391 C3391 := by
    simpa [hstackTaken, endSkipCatIlksCallMem, endSkipCatIlksBaseMem,
      endSkimVatIlksCallMem, endRuntimeBlocks.endRuntime_block_3314_taken_memory,
      endRuntimeBlocks.endRuntime_block_6795_taken_memory] using rd3391
  have rd3393 := endRuntimeBlocks.endRuntime_block_3391
    (x0 := UInt256.isZero (extCodeSizeWord σ (endSkipCatTarget σ I)))
    (R := endSkipCatIlksCallStack σ I sel)
    (by simp [endSkipCatIlksCallStack, endSkipCatIlksCallRest]) rd3391'
  exact ⟨aw3391, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3391_stack] using rd3393⟩

theorem endSkipCatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipCatIlksCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endSkipStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"] "catIlk" ]
      (sequenceExit ⟨3433⟩
        (fun cur frame e =>
          frame = endSkipAfterCatIlksFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          96 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I cur.rdata),
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSkipCatIlksReturnMem I cur.rdata ∧
          cur.aw = endSkipAfterCatIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨3393⟩ = some (.GAS, .none); decide)
    (by simp [endSkipCatIlksCallStack, endSkipCatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endSkipCatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨3394⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipCatIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 2)
    rw [h.env] at hload
    rw [endEvalCatAddress_skip]
    rw [h.env]
    rw [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 from by native_decide]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 2))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endSkipCatTarget σ I).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkipCatIlksArgs evm I
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endSkipCatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endSkipCatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_catIlks I (by omega : 36 ≤ I.calldata.size)]
    change some (endFlowVatIlksEncodedCall I) =
      some ((endSkipCatIlksCallMem I).readWithPadding 128 36)
    rw [show endSkipCatIlksCallMem I = endSkimVatIlksCallMem I from rfl]
    rw [endSkimVatIlksCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h96 : 96 ≤ out.size
    · rw [endExternalDecode_catIlks_ok h96]
      intro rd hrel
      have rd3395 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
            ((⟨1⟩ : UInt256) :: endSkipCatIlksCallRest σ I sel)
            (endSkipCatIlksReturnMem I out) (endSkipCatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipCatIlksCallStack, endSkipCatIlksCallRest,
          endSkipCatIlksCallAw, endSkipCatIlksReturnMem] using rd
      have rd3411 := endRuntimeBlocks.endRuntime_block_3395_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipCatIlksCallRest σ I sel)
        (by simp [endSkipCatIlksCallRest]) (by native_decide) (by jump_dest) rd3395
      have rd3411' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3411⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endSkipCatTarget σ I,
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipCatIlksReturnMem I out) (endSkipCatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3395_taken_stack,
          endSkipCatIlksCallRest] using rd3411
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 96) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 96).toNat = 96 from by native_decide,
          ulit_toNat' out.size hout]
        exact h96
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 96)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3433 := endRuntimeBlocks.endRuntime_block_3411_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endSkipCatTarget σ I)
        (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd3411'
      refine ⟨.ok (endSkipAfterCatIlksFrame I out) evm',
        Endpoint.reached (endSkipAfterCatIlksCursor I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSkipAfterCatIlksCursor, endSkipAfterCatIlksAw,
            endRuntimeBlocks.endRuntime_block_3411_taken_stack] using rd3433⟩
      · exact ⟨rfl, rfl, hrel, hout, h96, rfl, rfl, rfl⟩
    · have hshort : out.size < 96 := by omega
      rw [endExternalDecode_catIlks_none_short hshort]
      intro rd
      have rd3395 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
            ((⟨1⟩ : UInt256) :: endSkipCatIlksCallRest σ I sel)
            (endSkipCatIlksReturnMem I out) (endSkipCatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipCatIlksCallStack, endSkipCatIlksCallRest,
          endSkipCatIlksCallAw, endSkipCatIlksReturnMem] using rd
      have rd3411 := endRuntimeBlocks.endRuntime_block_3395_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipCatIlksCallRest σ I sel)
        (by simp [endSkipCatIlksCallRest]) (by native_decide) (by jump_dest) rd3395
      have rd3411' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3411⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endSkipCatTarget σ I,
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipCatIlksReturnMem I out) (endSkipCatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3395_taken_stack,
          endSkipCatIlksCallRest] using rd3411
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 96) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 96).toNat = 96 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 96)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3429 := endRuntimeBlocks.endRuntime_block_3411_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endSkipCatTarget σ I)
        (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd3411'
      exact endRuntimeBlocks.endRuntime_block_3429
        (R := endRuntimeBlocks.endRuntime_block_3411_fallthrough_stack
          (mem := endSkipCatIlksReturnMem I out) (rdata := out)
          (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_3411_fallthrough_stack])
        rd3429
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd3395 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
          ((⟨0⟩ : UInt256) :: endSkipCatIlksCallRest σ I sel)
          (endSkipCatIlksReturnMem I out) (endSkipCatIlksCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSkipCatIlksCallStack, endSkipCatIlksCallRest,
        endSkipCatIlksCallAw, endSkipCatIlksReturnMem] using rd
    have rd3402 := endRuntimeBlocks.endRuntime_block_3395_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipCatIlksCallRest σ I sel)
      (by simp [endSkipCatIlksCallRest]) (by native_decide) rd3395
    exact endRuntimeBlocks.endRuntime_block_3402
      (R := endRuntimeBlocks.endRuntime_block_3395_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipCatIlksCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_3395_fallthrough_stack,
        endSkipCatIlksCallRest])
      rd3402

abbrev endSkipVatIlksCallMem (I : ExecutionEnv) (outCat : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_3433_taken_memory
    (mem := endSkipCatIlksReturnMem I outCat) (x4 := endArg0Word I)

abbrev endSkipVatIlksCallRest (σ : AccountMap) (I : ExecutionEnv)
    (outCat : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I, ⟨0⟩,
    endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipVatIlksCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outCat : ByteArray) (sel : UInt256) : List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨160⟩] ++
    endSkipVatIlksCallRest σ I outCat sel

abbrev endSkipVatIlksCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outCat rdata : ByteArray) :
    Cursor :=
  { pc := ⟨3519⟩, stack := endSkipVatIlksCallStack world.2 I outCat sel,
    mem := endSkipVatIlksCallMem I outCat, aw := aw, rdata := rdata,
    world := world }

abbrev endSkipVatIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat)

abbrev endSkipVatIlksReturnMem (I : ExecutionEnv) (outCat outVat : ByteArray) :
    ByteArray :=
  outVat.write 0 (endSkipVatIlksCallMem I outCat) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat

abbrev endSkipAfterVatIlksAw (aw : UInt256) : UInt256 :=
  M (endSkipVatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSkipAfterVatIlksFrame (I : ExecutionEnv) (outCat outVat : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat)) }

abbrev endSkipAfterVatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outCat outVat : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨3559⟩,
    stack := [UInt256.ofNat outVat.size,
      memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat),
      ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSkipVatIlksReturnMem I outCat outVat,
    aw := endSkipAfterVatIlksAw aw,
    rdata := outVat,
    world := world }

abbrev endSkipAfterRateFrame (I : ExecutionEnv) (outCat outVat : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterVatIlksFrame I outCat outVat).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat)) }

abbrev endSkipFlipTarget (outCat : ByteArray) : UInt256 :=
  UInt256.land (endSkipCatIlksFlipWord outCat) solcAddrMask

abbrev endSkipBidsSelectorWord : UInt256 :=
  UInt256.ofNat 1143195121

abbrev endSkipBidsSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft endSkipBidsSelectorWord (UInt256.ofNat 224)

def endSkipBidsPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg1Word I)

def endSkipBidsEncodedCall (I : ExecutionEnv) : ByteArray :=
  bidsSelector ++ ⟨(endSkipBidsPayloadBytes I).toArray⟩

abbrev endSkipBidsCallMem (I : ExecutionEnv) (outCat outVat : ByteArray) :
    ByteArray :=
  endRuntimeBlocks.endRuntime_block_3559_memory
    (mem := endSkipVatIlksReturnMem I outCat outVat) (x5 := endArg1Word I)

abbrev endSkipBidsCallRest (I : ExecutionEnv) (outCat outVat : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endSkipBidsSelectorWord, endSkipFlipTarget outCat, ⟨0⟩, ⟨0⟩,
    ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
    endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipBidsCallStack (I : ExecutionEnv) (outCat outVat : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [endSkipFlipTarget outCat, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨256⟩] ++
    endSkipBidsCallRest I outCat outVat sel

abbrev endSkipBidsCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outCat outVat rdata : ByteArray) :
    Cursor :=
  { pc := ⟨3651⟩, stack := endSkipBidsCallStack I outCat outVat sel,
    mem := endSkipBidsCallMem I outCat outVat, aw := aw, rdata := rdata,
    world := world }

abbrev endSkipBidsCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨256⟩ : UInt256).toNat)

abbrev endSkipBidsReturnMem (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    ByteArray :=
  outBids.write 0 (endSkipBidsCallMem I outCat outVat) 128
    (min (⟨256⟩ : UInt256) (UInt256.ofNat outBids.size)).toNat

abbrev endSkipAfterBidsAw (aw : UInt256) : UInt256 :=
  M (endSkipBidsCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSkipBidsBidWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endSkipBidsLotWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endSkipBidsWord2 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endSkipBidsWord3 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 96).take 32)

abbrev endSkipBidsWord4 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 128).take 32)

abbrev endSkipBidsUsrWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 160).take 32)

abbrev endSkipBidsWord6 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 192).take 32)

abbrev endSkipBidsTabWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 224).take 32)

abbrev endSkipBidsUint48Value (w : UInt256) : Value :=
  .int (Int.ofNat (w.toNat % EVM.twoPow 48))

abbrev endSkipBidsValues (out : ByteArray) : List Value :=
  [endUIntValue (endSkipBidsBidWord out), endUIntValue (endSkipBidsLotWord out),
    .address (AccountAddress.ofNat (endSkipBidsWord2 out).toNat),
    endSkipBidsUint48Value (endSkipBidsWord3 out),
    endSkipBidsUint48Value (endSkipBidsWord4 out),
    .address (AccountAddress.ofNat (endSkipBidsUsrWord out).toNat),
    .address (AccountAddress.ofNat (endSkipBidsWord6 out).toNat),
    endUIntValue (endSkipBidsTabWord out)]

abbrev endSkipAfterBidsFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids)) }

abbrev endSkipAfterBidsCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outCat outVat outBids : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨3692⟩,
    stack := [UInt256.ofNat outBids.size,
      memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids),
      ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
      endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSkipBidsReturnMem I outCat outVat outBids,
    aw := endSkipAfterBidsAw aw,
    rdata := outBids,
    world := world }

theorem endSkipCatIlksCallMem_read64 (I : ExecutionEnv) :
    (endSkipCatIlksCallMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  simpa [endSkipCatIlksCallMem] using endSkimVatIlksCallMem_read64 I

theorem endSkipCatIlksCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endSkipCatIlksCallMem I) = ⟨128⟩ := by
  simpa [endSkipCatIlksCallMem] using endSkimVatIlksCallMem_mload64 I

theorem endSkipCatIlksCallMem_size (I : ExecutionEnv) :
    (endSkipCatIlksCallMem I).size = 164 := by
  simpa [endSkipCatIlksCallMem] using endSkimVatIlksCallMem_size I

theorem endSkipCatIlksReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h96 : 96 ≤ out.size) :
    (endSkipCatIlksReturnMem I out).size = 224 := by
  have hcopy :
      (min (⟨96⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 96 := by
    rw [callCopyLength_toNat out (⟨96⟩ : UInt256) hout]
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by native_decide]
    exact Nat.min_eq_left h96
  unfold endSkipCatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSkipCatIlksCallMem I) 128 96
    (by decide) h96
    (by rw [endSkipCatIlksCallMem_size I]; omega)
    (by rw [endSkipCatIlksCallMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSkipCatIlksCallMem_size I]
  omega

theorem endSkipCatIlksReturnMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h96 : 96 ≤ out.size) :
    (endSkipCatIlksReturnMem I out).readWithPadding 64 32 =
      (endSkipCatIlksCallMem I).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨96⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 96 := by
    rw [callCopyLength_toNat out (⟨96⟩ : UInt256) hout]
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by native_decide]
    exact Nat.min_eq_left h96
  unfold endSkipCatIlksReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend out (endSkipCatIlksCallMem I) 128 96 64
    (by decide) h96
    (by rw [endSkipCatIlksCallMem_size I]; omega)
    (by omega)

theorem endSkipCatIlksReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h96 : 96 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I out) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipCatIlksReturnMem I out)
    (by rw [endSkipCatIlksReturnMem_size I out hout h96]; omega)
    (by rw [endSkipCatIlksReturnMem_read64 I out hout h96,
      endSkipCatIlksCallMem_read64 I])

theorem endSkipCatIlksReturnMem_read128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h96 : 96 ≤ out.size) :
    (endSkipCatIlksReturnMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  have hcopy :
      (min (⟨96⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 96 := by
    rw [callCopyLength_toNat out (⟨96⟩ : UInt256) hout]
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by native_decide]
    exact Nat.min_eq_left h96
  unfold endSkipCatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSkipCatIlksCallMem I) 128 96
    (by decide) h96
    (by rw [endSkipCatIlksCallMem_size I]; omega)
    (by rw [endSkipCatIlksCallMem_size I]; omega)]
  have hpre : ((endSkipCatIlksCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipCatIlksCallMem_size I]
    omega
  have hcopySize : (out.extract 0 96).size = 96 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [hpre]), hpre]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 96 = 32 by omega]

theorem endSkipCatIlksReturnMem_mload128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h96 : 96 ≤ out.size) :
    memLoad (UInt256.ofNat 128) (endSkipCatIlksReturnMem I out) =
      endSkipCatIlksFlipWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endSkipCatIlksReturnMem_size I out hout h96]
    omega)]
  rw [endSkipCatIlksReturnMem_read128 I out hout h96]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) =
    ABI.bytesToWord (out.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endSkipVatIlksCallMem_eq_full (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    endSkipVatIlksCallMem I outCat =
      (endArg0Word I).toByteArray.write 0
        (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
          (endSkipCatIlksReturnMem I outCat) 128 32)
        132 32 := by
  unfold endSkipVatIlksCallMem endFlowVatIlksSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_3433_taken_memory]
  rw [endSkipCatIlksReturnMem_mload64 I outCat houtCat h96]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]

theorem endSkipVatIlksMemSel_size_ge160 (I : ExecutionEnv) (outCat : ByteArray) :
    160 ≤ (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkipCatIlksReturnMem I outCat) 128

theorem endSkipVatIlksCallMem_size_ge164 (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    164 ≤ (endSkipVatIlksCallMem I outCat).size := by
  rw [endSkipVatIlksCallMem_eq_full I outCat houtCat h96]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32)
    132

theorem endSkipVatIlksCallMem_read64 (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endSkipVatIlksCallMem I outCat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipVatIlksCallMem_eq_full I outCat houtCat h96]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32)
    132 64
    (by have hge := endSkipVatIlksMemSel_size_ge160 I outCat; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkipCatIlksReturnMem I outCat) 128 64
    (by rw [endSkipCatIlksReturnMem_size I outCat houtCat h96]; omega)
    (by omega)]
  rw [endSkipCatIlksReturnMem_read64 I outCat houtCat h96,
    endSkipCatIlksCallMem_read64 I]

theorem endSkipVatIlksCallMem_mload64 (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    memLoad (UInt256.ofNat 64) (endSkipVatIlksCallMem I outCat) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipVatIlksCallMem I outCat)
    (by have := endSkipVatIlksCallMem_size_ge164 I outCat houtCat h96; omega)
    (endSkipVatIlksCallMem_read64 I outCat houtCat h96)

theorem endSkipVatIlksCallMem_readSelector (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endSkipVatIlksCallMem I outCat).readWithPadding 128 4 = ilksSelector := by
  rw [endSkipVatIlksCallMem_eq_full I outCat houtCat h96]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have hge := endSkipVatIlksMemSel_size_ge160 I outCat; omega) (by omega)
    (by have hge := endSkipVatIlksMemSel_size_ge160 I outCat; omega) (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkipCatIlksReturnMem I outCat) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFlowVatIlksSelectorEncodedWord_prefix]

theorem endSkipVatIlksCallMem_readIlk (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endSkipVatIlksCallMem I outCat).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSkipVatIlksCallMem_eq_full I outCat houtCat h96]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32)
    132

theorem endSkipVatIlksCallMem_readCallData (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endSkipVatIlksCallMem I outCat).readWithPadding 128 36 =
      endFlowVatIlksEncodedCall I := by
  have hsize := endSkipVatIlksCallMem_size_ge164 I outCat houtCat h96
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSkipVatIlksCallMem I outCat) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSkipVatIlksCallMem_readSelector I outCat houtCat h96,
    endSkipVatIlksCallMem_readIlk I outCat houtCat h96]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFlowVatIlksEncodedCall, endFlowVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

theorem endSkipVatIlksMemSel_size (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32).size = 224 := by
  exact toByteArray_write32_size_of_le
    (endSkipCatIlksReturnMem I outCat) endFlowVatIlksSelectorEncodedWord 128 224 224
    (endSkipCatIlksReturnMem_size I outCat houtCat h96)
    (by rw [endSkipCatIlksReturnMem_size I outCat houtCat h96]; omega)
    (by omega)

theorem endSkipVatIlksCallMem_size (I : ExecutionEnv) (outCat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    (endSkipVatIlksCallMem I outCat).size = 224 := by
  rw [endSkipVatIlksCallMem_eq_full I outCat houtCat h96]
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkipCatIlksReturnMem I outCat) 128 32)
    (endArg0Word I) 132 224 224
    (endSkipVatIlksMemSel_size I outCat houtCat h96)
    (by rw [endSkipVatIlksMemSel_size I outCat houtCat h96]; omega)
    (by omega)

theorem endSkipVatIlksReturnMem_size (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipVatIlksReturnMem I outCat outVat).size = 288 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkipVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outVat (endSkipVatIlksCallMem I outCat) 128 160
    (by decide) h160
    (by rw [endSkipVatIlksCallMem_size I outCat houtCat h96]; omega)
    (by rw [endSkipVatIlksCallMem_size I outCat houtCat h96]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSkipVatIlksCallMem_size I outCat houtCat h96]
  omega

theorem endSkipVatIlksReturnMem_read64 (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipVatIlksReturnMem I outCat outVat).readWithPadding 64 32 =
      (endSkipVatIlksCallMem I outCat).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkipVatIlksReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend outVat (endSkipVatIlksCallMem I outCat) 128 160 64
    (by decide) h160
    (by rw [endSkipVatIlksCallMem_size I outCat houtCat h96]; omega)
    (by omega)

theorem endSkipVatIlksReturnMem_mload64 (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipVatIlksReturnMem I outCat outVat)
    (by rw [endSkipVatIlksReturnMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by rw [endSkipVatIlksReturnMem_read64 I outCat outVat houtCat h96 houtVat h160,
      endSkipVatIlksCallMem_read64 I outCat houtCat h96])

theorem endSkipVatIlksReturnMem_read160 (I : ExecutionEnv)
    (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipVatIlksReturnMem I outCat outVat).readWithPadding 160 32 =
      outVat.extract 32 64 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkipVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outVat (endSkipVatIlksCallMem I outCat) 128 160
    (by decide) h160
    (by rw [endSkipVatIlksCallMem_size I outCat houtCat h96]; omega)
    (by rw [endSkipVatIlksCallMem_size I outCat houtCat h96]; omega)]
  have hpre : ((endSkipVatIlksCallMem I outCat).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipVatIlksCallMem_size I outCat houtCat h96]
    omega
  have hcopySize : (outVat.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 160 = 64 by omega]

theorem endSkipVatIlksReturnMem_mload160 (I : ExecutionEnv)
    (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 160) (endSkipVatIlksReturnMem I outCat outVat) =
      endFlowVatIlksRateWord outVat := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSkipVatIlksReturnMem_size I outCat outVat houtCat h96 houtVat h160]
    omega)]
  rw [endSkipVatIlksReturnMem_read160 I outCat outVat houtCat h96 houtVat h160]
  change UInt256.ofNat (fromByteArrayBigEndian (outVat.extract 32 64)) =
    ABI.bytesToWord ((outVat.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

theorem endEvalSkipCatIlkFlip (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray) :
    evalExpr? config (endSkipAfterCatIlksFrame I outCat) evm
      (.tupleGet (.var "catIlk") 0) =
      .ok (endSkipFlipValue outCat) := by
  simp [evalExpr?, endSkipAfterCatIlksFrame, collapseReturns, tupleGetValue?,
    endSkipCatIlksValues, endSkipFlipValue, EvalResult.ofOption, EvalResult.bind, bind]

theorem endLetSkipFlip (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray) :
    ExecStmt config (endSkipAfterCatIlksFrame I outCat) evm
      (.letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0))
      (.ok (endSkipAfterFlipFrame I outCat) evm) := by
  simpa [endSkipAfterFlipFrame] using
    ExecStmt.letDecl (endEvalSkipCatIlkFlip evm I outCat)

theorem endSkipAfterFlipFrame_get_vat_none (I : ExecutionEnv) (outCat : ByteArray) :
    (endSkipAfterFlipFrame I outCat).locals.get? "vat" = none := by
  change (((endSkipAfterCatIlksFrame I outCat).locals.insert "flip"
      (endSkipFlipValue outCat)).get? "vat") = none
  rw [store_get_ne (endSkipAfterCatIlksFrame I outCat).locals
    (k := "flip") (a := "vat") (endSkipFlipValue outCat) (by decide)]
  change (((endSkipStore I).insert "catIlk"
      (collapseReturns (endSkipCatIlksValues outCat))).get? "vat") = none
  rw [store_get_ne (endSkipStore I) (k := "catIlk") (a := "vat")
    (collapseReturns (endSkipCatIlksValues outCat)) (by decide)]
  simp [endSkipStore]

theorem endEvalVatAddress_skipAfterFlip (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray) :
    evalExpr? config (endSkipAfterFlipFrame I outCat) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterFlipFrame I outCat).locals) (evm := evm) (slot := vatRef)
    (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSkipAfterFlipFrame_get_vat_none I outCat)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVatCodeGuard_skipAfterFlip_false (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkipAfterFlipFrame I outCat) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterFlipFrame I outCat).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterFlip evm I outCat) hnocode

theorem endEvalVatCodeGuard_skipAfterFlip_true (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterFlipFrame I outCat) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterFlipFrame I outCat).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterFlip evm I outCat) hcode

theorem endSkipAfterFlipFrame_get_ilk (I : ExecutionEnv) (outCat : ByteArray) :
    (endSkipAfterFlipFrame I outCat).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkipAfterCatIlksFrame I outCat).locals.insert "flip"
      (endSkipFlipValue outCat)).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterCatIlksFrame I outCat).locals
    (k := "flip") (a := "ilk") (endSkipFlipValue outCat) (by decide)]
  change (((endSkipStore I).insert "catIlk"
      (collapseReturns (endSkipCatIlksValues outCat))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipStore I) (k := "catIlk")
    (a := "ilk") (collapseReturns (endSkipCatIlksValues outCat)) (by decide)]
  exact endSnipStore_get_ilk I

theorem endSkipAfterFlipFrame_getElem_ilk (I : ExecutionEnv) (outCat : ByteArray) :
    (endSkipAfterFlipFrame I outCat).locals["ilk"] = endArg0Bytes32Value I := by
  have hopt :
      (endSkipAfterFlipFrame I outCat).locals["ilk"]? =
        some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSkipAfterFlipFrame_get_ilk I outCat
  have hpos := getElem?_pos (endSkipAfterFlipFrame I outCat).locals "ilk" (by
    simp [endSkipAfterFlipFrame, endSkipAfterCatIlksFrame, endSkipStore,
      Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalSkipVatIlksArgsAfterFlip (evm : EVM.State) (I : ExecutionEnv)
    (outCat : ByteArray) :
    evalExprs? config (endSkipAfterFlipFrame I outCat) evm [.var "ilk"] =
      .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endSkipAfterFlipFrame_getElem_ilk I outCat]

theorem endEvalSkipRateFromVatIlk (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    evalExpr? config (endSkipAfterVatIlksFrame I outCat outVat) evm
      (.tupleGet (.var "vatIlk") 1) =
      .ok (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  simp [evalExpr?, endSkipAfterVatIlksFrame, collapseReturns, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind, endUIntValue]

theorem endLetSkipRate (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    ExecStmt config (endSkipAfterVatIlksFrame I outCat outVat) evm
      (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok (endSkipAfterRateFrame I outCat outVat) evm) := by
  simpa [endSkipAfterRateFrame] using
    ExecStmt.letDecl (endEvalSkipRateFromVatIlk evm I outCat outVat)

theorem endSkipAfterRateFrame_get_flip (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    (endSkipAfterRateFrame I outCat outVat).locals.get? "flip" =
      some (endSkipFlipValue outCat) := by
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "flip") =
    some (endSkipFlipValue outCat)
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "flip")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "flip") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact store_get_self (endSkipAfterCatIlksFrame I outCat).locals "flip"
    (endSkipFlipValue outCat)

theorem endSkipAfterRateFrame_get_id (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    (endSkipAfterRateFrame I outCat outVat).locals.get? "id" =
      some (endUIntValue (endArg1Word I)) := by
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "id")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "id") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSkipAfterCatIlksFrame I outCat).locals.insert "flip"
      (endSkipFlipValue outCat)).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterCatIlksFrame I outCat).locals
    (k := "flip") (a := "id") (endSkipFlipValue outCat) (by decide)]
  change (((endSkipStore I).insert "catIlk"
      (collapseReturns (endSkipCatIlksValues outCat))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipStore I) (k := "catIlk") (a := "id")
    (collapseReturns (endSkipCatIlksValues outCat)) (by decide)]
  exact endSnipStore_get_id I

theorem endSkipFlipAddress_eq_mask (outCat : ByteArray) :
    AccountAddress.ofNat (endSkipCatIlksFlipWord outCat).toNat =
      AccountAddress.ofNat (endSkipFlipTarget outCat).toNat := by
  apply Fin.ext
  unfold AccountAddress.ofNat endSkipFlipTarget
  change (endSkipCatIlksFlipWord outCat).toNat % AccountAddress.size =
    (UInt256.land (endSkipCatIlksFlipWord outCat) solcAddrMask).toNat %
      AccountAddress.size
  rw [u256_land_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (by norm_num [UInt256.size]))]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))]

theorem endEvalFlipAddress_skipAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    evalExpr? config (endSkipAfterRateFrame I outCat outVat) evm (.var "flip") =
      .ok (endSkipFlipValue outCat) := by
  simp [evalExpr?, EvalResult.ofOption]
  have hget := endSkipAfterRateFrame_get_flip I outCat outVat
  have hmem : "flip" ∈ (endSkipAfterRateFrame I outCat outVat).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSkipAfterRateFrame I outCat outVat).locals["flip"]? =
        some (endSkipFlipValue outCat) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSkipAfterRateFrame I outCat outVat).locals "flip" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalFlipAddress_skipAfterRate_masked (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    evalExpr? config (endSkipAfterRateFrame I outCat outVat) evm (.var "flip") =
      .ok (.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)) := by
  rw [endEvalFlipAddress_skipAfterRate evm I outCat outVat]
  simp [endSkipFlipValue, endSkipFlipAddress_eq_mask outCat]

theorem endEvalFlipCodeGuard_skipAfterRate_false (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) = ⟨0⟩) :
    evalExpr? config (endSkipAfterRateFrame I outCat outVat) evm
      (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterRateFrame I outCat outVat).locals) (evm := evm)
    (receiver := .var "flip") (target := endSkipFlipTarget outCat)
    (endEvalFlipAddress_skipAfterRate_masked evm I outCat outVat) hnocode

theorem endEvalFlipCodeGuard_skipAfterRate_true (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterRateFrame I outCat outVat) evm
      (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterRateFrame I outCat outVat).locals) (evm := evm)
    (receiver := .var "flip") (target := endSkipFlipTarget outCat)
    (endEvalFlipAddress_skipAfterRate_masked evm I outCat outVat) hcode

theorem endEvalSkipBidsArgsAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat : ByteArray) :
    evalExprs? config (endSkipAfterRateFrame I outCat outVat) evm [.var "id"] =
      .ok [endUIntValue (endArg1Word I)] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hget := endSkipAfterRateFrame_get_id I outCat outVat
  have hmem : "id" ∈ (endSkipAfterRateFrame I outCat outVat).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSkipAfterRateFrame I outCat outVat).locals["id"]? =
        some (endUIntValue (endArg1Word I)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSkipAfterRateFrame I outCat outVat).locals "id" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endX_skip_vat_no_code_after_cat {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3433⟩
      (endSkipAfterCatIlksCursor I sel aw outCat world).stack
      (endSkipCatIlksReturnMem I outCat) (endSkipAfterCatIlksAw aw) outCat
      world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner world.2 (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    rw [hmaskGenerated]
    change UInt256.isZero
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) =
      UInt256.ofNat 0
    rw [hvatNoCode]
    native_decide
  obtain ⟨aw3513, k3513, C3513, rd3513⟩ :=
    endRuntimeBlocks.endRuntime_block_3433_fallthrough_packed
      (x0 := UInt256.ofNat outCat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1Word I) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hcondCode
      (by simpa [endSkipAfterCatIlksCursor] using rd)
  exact endRuntimeBlocks.endRuntime_block_3513
    (R := endRuntimeBlocks.endRuntime_block_3433_fallthrough_stack (ee := I)
      (mem := endSkipCatIlksReturnMem I outCat) (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat))
      (x3 := endArg1Word I) (x4 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_3433_fallthrough_stack])
    rd3513

set_option maxHeartbeats 12000000 in
theorem endX_skip_after_cat_to_vat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3433⟩
      (endSkipAfterCatIlksCursor I sel aw outCat world).stack
      (endSkipCatIlksReturnMem I outCat) (endSkipAfterCatIlksAw aw) outCat
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3519⟩
      (endSkipVatIlksCallStack world.2 I outCat sel) (endSkipVatIlksCallMem I outCat)
      aw' outCat world k' C' := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner world.2 (UInt256.ofNat 1))))) ≠
        UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner world.2 (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hmaskGenerated]
      simpa [endPackVatTarget] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw3517, k3517, C3517, rd3517⟩ :=
    endRuntimeBlocks.endRuntime_block_3433_taken_packed
      (x0 := UInt256.ofNat outCat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1Word I) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSkipAfterCatIlksCursor] using rd)
  have hret64 := endSkipCatIlksReturnMem_mload64 I outCat houtCat h96
  have hflip := endSkipCatIlksReturnMem_mload128 I outCat houtCat h96
  have hflipLit :
      memLoad (⟨128⟩ : UInt256) (endSkipCatIlksReturnMem I outCat) =
        endSkipCatIlksFlipWord outCat := by
    simpa [show UInt256.ofNat 128 = (⟨128⟩ : UInt256) from by native_decide] using hflip
  have hcall64 := endSkipVatIlksCallMem_mload64 I outCat houtCat h96
  have hcall64Generated :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_3433_taken_memory
          (mem := endSkipCatIlksReturnMem I outCat) (x4 := endArg0Word I)) =
        ⟨128⟩ := by
    simpa [endSkipVatIlksCallMem] using hcall64
  have hcallAfterRet :
      memLoad (UInt256.ofNat 64)
        ((endArg0Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write
            0 (endSkipCatIlksReturnMem I outCat) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_3433_taken_memory, hret64] using
      hcall64Generated
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_3433_taken_stack (ee := I)
          (mem := endSkipCatIlksReturnMem I outCat) (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat))
          (x3 := endArg1Word I) (x4 := endArg0Word I) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipVatIlksCallStack world.2 I outCat sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_3433_taken_stack,
      endSkipVatIlksCallStack, endSkipVatIlksCallRest, endFlowVatIlksSelectorWord,
      endPackVatTarget]
    rw [hret64, hcallAfterRet, hflipLit, hlen, hend, hmaskGenerated]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 160 = (⟨160⟩ : UInt256) from by native_decide]
  have rd3517' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3517⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipVatIlksCallStack world.2 I outCat sel)
        (endSkipVatIlksCallMem I outCat) aw3517 outCat world k3517 C3517 := by
    simpa [hstackTaken, endSkipVatIlksCallMem] using rd3517
  have rd3519 := endRuntimeBlocks.endRuntime_block_3517
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSkipVatIlksCallStack world.2 I outCat sel)
    (by simp [endSkipVatIlksCallStack, endSkipVatIlksCallRest]) rd3517'
  exact ⟨aw3517, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3517_stack] using rd3519⟩

set_option maxHeartbeats 12000000 in
theorem endSkipVatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipVatIlksCallCursor world I sel aw outCat rdata)
      k C (endSkipAfterFlipFrame I outCat) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
      (sequenceExit ⟨3559⟩
        (fun cur frame e =>
          frame = endSkipAfterVatIlksFrame I outCat cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          160 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat cur.rdata),
              ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSkipVatIlksReturnMem I outCat cur.rdata ∧
          cur.aw = endSkipAfterVatIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨3519⟩ = some (.GAS, .none); decide)
    (by simp [endSkipVatIlksCallStack, endSkipVatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨3520⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipVatIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skipAfterFlip evm I outCat]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat
          (endPackVatTarget world.2 I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkipVatIlksArgsAfterFlip evm I outCat
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_vatIlks I (by omega : 36 ≤ I.calldata.size)]
    change some (endFlowVatIlksEncodedCall I) =
      some ((endSkipVatIlksCallMem I outCat).readWithPadding 128 36)
    rw [endSkipVatIlksCallMem_readCallData I outCat houtCat h96]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h160 : 160 ≤ out.size
    · rw [endExternalDecode_vatIlks_ok h160]
      intro rd hrel
      have rd3521 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
            ((⟨1⟩ : UInt256) :: endSkipVatIlksCallRest world.2 I outCat sel)
            (endSkipVatIlksReturnMem I outCat out) (endSkipVatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipVatIlksCallStack, endSkipVatIlksCallRest,
          endSkipVatIlksCallAw, endSkipVatIlksReturnMem] using rd
      have rd3537 := endRuntimeBlocks.endRuntime_block_3521_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipVatIlksCallRest world.2 I outCat sel)
        (by simp [endSkipVatIlksCallRest]) (by native_decide) (by jump_dest) rd3521
      have rd3537' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3537⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipVatIlksReturnMem I outCat out) (endSkipVatIlksCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3521_taken_stack,
          endSkipVatIlksCallRest] using rd3537
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide,
          ulit_toNat' out.size hout]
        exact h160
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3559 := endRuntimeBlocks.endRuntime_block_3537_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd3537'
      refine ⟨.ok (endSkipAfterVatIlksFrame I outCat out) evm',
        Endpoint.reached (endSkipAfterVatIlksCursor I sel aw outCat out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSkipAfterVatIlksCursor, endSkipAfterVatIlksAw,
            endRuntimeBlocks.endRuntime_block_3537_taken_stack] using rd3559⟩
      · exact ⟨rfl, rfl, hrel, hout, h160, rfl, rfl, rfl⟩
    · have hshort : out.size < 160 := by omega
      rw [endExternalDecode_vatIlks_none_short hshort]
      intro rd
      have rd3521 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
            ((⟨1⟩ : UInt256) :: endSkipVatIlksCallRest world.2 I outCat sel)
            (endSkipVatIlksReturnMem I outCat out) (endSkipVatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipVatIlksCallStack, endSkipVatIlksCallRest,
          endSkipVatIlksCallAw, endSkipVatIlksReturnMem] using rd
      have rd3537 := endRuntimeBlocks.endRuntime_block_3521_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipVatIlksCallRest world.2 I outCat sel)
        (by simp [endSkipVatIlksCallRest]) (by native_decide) (by jump_dest) rd3521
      have rd3537' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3537⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipVatIlksReturnMem I outCat out) (endSkipVatIlksCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3521_taken_stack,
          endSkipVatIlksCallRest] using rd3537
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3555 := endRuntimeBlocks.endRuntime_block_3537_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd3537'
      exact endRuntimeBlocks.endRuntime_block_3555
        (R := endRuntimeBlocks.endRuntime_block_3537_fallthrough_stack
          (mem := endSkipVatIlksReturnMem I outCat out) (rdata := out)
          (R := [⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_3537_fallthrough_stack])
        rd3555
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd3521 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
          ((⟨0⟩ : UInt256) :: endSkipVatIlksCallRest world.2 I outCat sel)
          (endSkipVatIlksReturnMem I outCat out) (endSkipVatIlksCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSkipVatIlksCallStack, endSkipVatIlksCallRest,
        endSkipVatIlksCallAw, endSkipVatIlksReturnMem] using rd
    have rd3528 := endRuntimeBlocks.endRuntime_block_3521_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipVatIlksCallRest world.2 I outCat sel)
      (by simp [endSkipVatIlksCallRest]) (by native_decide) rd3521
    exact endRuntimeBlocks.endRuntime_block_3528
      (R := endRuntimeBlocks.endRuntime_block_3521_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipVatIlksCallRest world.2 I outCat sel))
      (by simp [endRuntimeBlocks.endRuntime_block_3521_fallthrough_stack,
        endSkipVatIlksCallRest])
      rd3528

theorem endSkipBidsSelectorEncodedWord_prefix :
    (endSkipBidsSelectorEncodedWord.toByteArray).extract 0 4 = bidsSelector := by
  native_decide

theorem endSkipBidsCallMem_eq_full (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    endSkipBidsCallMem I outCat outVat =
      (endArg1Word I).toByteArray.write 0
        (endSkipBidsSelectorEncodedWord.toByteArray.write 0
          (endSkipVatIlksReturnMem I outCat outVat) 128 32)
        132 32 := by
  unfold endSkipBidsCallMem endSkipBidsSelectorEncodedWord endSkipBidsSelectorWord
  dsimp [endRuntimeBlocks.endRuntime_block_3559_memory]
  rw [endSkipVatIlksReturnMem_mload64 I outCat outVat houtCat h96 houtVat h160]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]

theorem endSkipBidsMemSel_size (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsSelectorEncodedWord.toByteArray.write 0
      (endSkipVatIlksReturnMem I outCat outVat) 128 32).size = 288 := by
  exact toByteArray_write32_size_of_le
    (endSkipVatIlksReturnMem I outCat outVat) endSkipBidsSelectorEncodedWord 128 288 288
    (endSkipVatIlksReturnMem_size I outCat outVat houtCat h96 houtVat h160)
    (by rw [endSkipVatIlksReturnMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)

theorem endSkipBidsCallMem_size (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsCallMem I outCat outVat).size = 288 := by
  rw [endSkipBidsCallMem_eq_full I outCat outVat houtCat h96 houtVat h160]
  exact toByteArray_write32_size_of_le
    (endSkipBidsSelectorEncodedWord.toByteArray.write 0
      (endSkipVatIlksReturnMem I outCat outVat) 128 32)
    (endArg1Word I) 132 288 288
    (endSkipBidsMemSel_size I outCat outVat houtCat h96 houtVat h160)
    (by rw [endSkipBidsMemSel_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)

theorem endSkipBidsCallMem_read64 (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsCallMem I outCat outVat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipBidsCallMem_eq_full I outCat outVat houtCat h96 houtVat h160]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1Word I)
    (endSkipBidsSelectorEncodedWord.toByteArray.write 0
      (endSkipVatIlksReturnMem I outCat outVat) 128 32)
    132 64
    (by rw [endSkipBidsMemSel_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSkipBidsSelectorEncodedWord (endSkipVatIlksReturnMem I outCat outVat) 128 64
    (by rw [endSkipVatIlksReturnMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)]
  rw [endSkipVatIlksReturnMem_read64 I outCat outVat houtCat h96 houtVat h160,
    endSkipVatIlksCallMem_read64 I outCat houtCat h96]

theorem endSkipBidsCallMem_mload64 (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 64) (endSkipBidsCallMem I outCat outVat) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipBidsCallMem I outCat outVat)
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (endSkipBidsCallMem_read64 I outCat outVat houtCat h96 houtVat h160)

theorem endSkipBidsCallMem_readSelector (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsCallMem I outCat outVat).readWithPadding 128 4 = bidsSelector := by
  rw [endSkipBidsCallMem_eq_full I outCat outVat houtCat h96 houtVat h160]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endSkipBidsMemSel_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)
    (by rw [endSkipBidsMemSel_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipBidsSelectorEncodedWord (endSkipVatIlksReturnMem I outCat outVat) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipBidsSelectorEncodedWord_prefix]

theorem endSkipBidsCallMem_readId (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsCallMem I outCat outVat).readWithPadding 132 32 =
      (endArg1Word I).toByteArray := by
  rw [endSkipBidsCallMem_eq_full I outCat outVat houtCat h96 houtVat h160]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg1Word I)
    (endSkipBidsSelectorEncodedWord.toByteArray.write 0
      (endSkipVatIlksReturnMem I outCat outVat) 128 32)
    132

theorem endSkipBidsCallMem_readCallData (I : ExecutionEnv) (outCat outVat : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSkipBidsCallMem I outCat outVat).readWithPadding 128 36 =
      endSkipBidsEncodedCall I := by
  have hsize : 164 ≤ (endSkipBidsCallMem I outCat outVat).size := by
    rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]
    omega
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSkipBidsCallMem I outCat outVat) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSkipBidsCallMem_readSelector I outCat outVat houtCat h96 houtVat h160,
    endSkipBidsCallMem_readId I outCat outVat houtCat h96 houtVat h160]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSkipBidsEncodedCall, endSkipBidsPayloadBytes, toByteArray_eq_toBytesBE]

theorem endSkipBidsReturnMem_size (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipBidsReturnMem I outCat outVat outBids).size = 384 := by
  have hcopy :
      (min (⟨256⟩ : UInt256) (UInt256.ofNat outBids.size)).toNat = 256 := by
    rw [callCopyLength_toNat outBids (⟨256⟩ : UInt256) houtBids]
    rw [show (⟨256⟩ : UInt256).toNat = 256 from by native_decide]
    exact Nat.min_eq_left h256
  unfold endSkipBidsReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outBids (endSkipBidsCallMem I outCat outVat) 128 256
    (by decide) h256
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]
  omega

theorem endSkipBidsReturnMem_read64 (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipBidsReturnMem I outCat outVat outBids).readWithPadding 64 32 =
      (endSkipBidsCallMem I outCat outVat).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨256⟩ : UInt256) (UInt256.ofNat outBids.size)).toNat = 256 := by
    rw [callCopyLength_toNat outBids (⟨256⟩ : UInt256) houtBids]
    rw [show (⟨256⟩ : UInt256).toNat = 256 from by native_decide]
    exact Nat.min_eq_left h256
  unfold endSkipBidsReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend outBids (endSkipBidsCallMem I outCat outVat) 128 256 64
    (by decide) h256
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by omega)

theorem endSkipBidsReturnMem_mload64 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipBidsReturnMem I outCat outVat outBids)
    (by
      rw [endSkipBidsReturnMem_size I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by
      rw [endSkipBidsReturnMem_read64 I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256,
        endSkipBidsCallMem_read64 I outCat outVat houtCat h96 houtVat h160])

theorem endEncodeABIValues_bids_skip (I : ExecutionEnv) :
    encodeABIValues? [uint256] [endUIntValue (endArg1Word I)] =
      some (endSkipBidsPayloadBytes I) := by
  simpa [endSkipBidsPayloadBytes, endSnipSalesPayloadBytes] using
    endEncodeABIValues_sales_snip I

theorem endEncodeCallWithSelector_bids_skip (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? bidsSelector [uint256]
      [endUIntValue (endArg1Word I)] =
      some (endSkipBidsEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_bids_skip I]
  simp [endSkipBidsEncodedCall, endSkipBidsPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_bids_branch (args : List Value) :
    config.externalABI.encode? "bids" args =
      ABI.encodeCallWithSelector? bidsSelector [uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "bids" = "cage")]
  rw [if_neg (by decide : ¬ "bids" = "vatIlks")]
  rw [if_neg (by decide : ¬ "bids" = "catIlks")]
  rw [if_neg (by decide : ¬ "bids" = "dogIlks")]
  rw [if_neg (by decide : ¬ "bids" = "spotIlks")]
  rw [if_neg (by decide : ¬ "bids" = "urns")]
  rw [if_neg (by decide : ¬ "bids" = "dai")]
  rw [if_neg (by decide : ¬ "bids" = "debt")]
  rw [if_neg (by decide : ¬ "bids" = "move")]
  rw [if_neg (by decide : ¬ "bids" = "hope")]
  rw [if_neg (by decide : ¬ "bids" = "flux")]
  rw [if_neg (by decide : ¬ "bids" = "grab")]
  rw [if_neg (by decide : ¬ "bids" = "suck")]
  rw [if_neg (by decide : ¬ "bids" = "par")]
  rw [if_neg (by decide : ¬ "bids" = "tell")]
  rw [if_pos (by decide : "bids" = "bids")]

theorem endExternalEncode_bids_skip (I : ExecutionEnv) :
    config.externalABI.encode? "bids" [endUIntValue (endArg1Word I)] =
      some (endSkipBidsEncodedCall I) := by
  rw [endExternalEncode_bids_branch]
  exact endEncodeCallWithSelector_bids_skip I

theorem endDecodeScalarWordWithMode_legacy_uint48_ok {bytes : List UInt8}
    {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 bytes start =
      some (.int (Int.ofNat
        ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 48)),
        start + 32) := by
  simp only [decodeScalarWordWithMode?, readWord?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  simp [uint48, uint48Int, decodeABIWord?, UInt256.toNat]

theorem endDecodeScalarWordWithMode_legacy_uint48_none_short {bytes : List UInt8}
    {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 bytes start = none := by
  simp only [decodeScalarWordWithMode?, readWord?, readBytes?, bind, Option.bind]
  rw [if_neg hshort]

theorem endSkipDecodeScalarWordsWithMode_legacy_bids_ok {out : ByteArray}
    (h256 : 256 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, addr, uint48, uint48, addr, addr, uint256]
        out.toList 0 =
      some (endSkipBidsValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake160 : ((out.toList.drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake192 : ((out.toList.drop 192).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake224 : ((out.toList.drop 224).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (endUIntValue (endSkipBidsBidWord out), 0 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSkipBidsBidWord, endUIntValue,
      List.drop_zero] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endUIntValue (endSkipBidsLotWord out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSkipBidsLotWord, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 64 =
        some (.address (AccountAddress.ofNat (endSkipBidsWord2 out).toNat), 64 + 32) := by
    simpa [addr, abiAddress, endSkipBidsWord2] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 96 =
        some (endSkipBidsUint48Value (endSkipBidsWord3 out), 96 + 32) := by
    simpa [endSkipBidsUint48Value, endSkipBidsWord3] using
      (endDecodeScalarWordWithMode_legacy_uint48_ok
        (bytes := out.toList) (start := 96) htake96)
  rw [hdec96]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 128 =
        some (endSkipBidsUint48Value (endSkipBidsWord4 out), 128 + 32) := by
    simpa [endSkipBidsUint48Value, endSkipBidsWord4] using
      (endDecodeScalarWordWithMode_legacy_uint48_ok
        (bytes := out.toList) (start := 128) htake128)
  rw [hdec128]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 160 =
        some (.address (AccountAddress.ofNat (endSkipBidsUsrWord out).toNat), 160 + 32) := by
    simpa [addr, abiAddress, endSkipBidsUsrWord] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 160) htake160)
  rw [hdec160]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec192 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 192 =
        some (.address (AccountAddress.ofNat (endSkipBidsWord6 out).toNat), 192 + 32) := by
    simpa [addr, abiAddress, endSkipBidsWord6] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 192) htake192)
  rw [hdec192]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec224 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 224 =
        some (endUIntValue (endSkipBidsTabWord out), 224 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSkipBidsTabWord, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 224) htake224)
  rw [hdec224]

theorem endSkipDecodeReturnValues_legacy_bids_ok {out : ByteArray}
    (h256 : 256 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out =
      some (endSkipBidsValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, addr, uint48, uint48, addr, addr,
      uint256] = some 256 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (bytes := out.toList) (cursor := 0) (total := 256)
    (by decide) (by decide)]
  rw [endSkipDecodeScalarWordsWithMode_legacy_bids_ok h256]

theorem endExternalDecode_bids_ok {out : ByteArray} (h256 : 256 ≤ out.size) :
    config.externalABI.decode? "bids" out = some (endSkipBidsValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "bids" = "cage")]
  rw [if_neg (by decide : ¬ "bids" = "vatIlks")]
  rw [if_neg (by decide : ¬ "bids" = "catIlks")]
  rw [if_neg (by decide : ¬ "bids" = "dogIlks")]
  rw [if_neg (by decide : ¬ "bids" = "spotIlks")]
  rw [if_neg (by decide : ¬ "bids" = "urns")]
  rw [if_neg (by decide : ¬ "bids" = "dai")]
  rw [if_neg (by decide : ¬ "bids" = "debt")]
  rw [if_neg (by decide : ¬ "bids" = "par")]
  rw [if_neg (by decide : ¬ "bids" = "tell")]
  rw [if_neg (by decide : ¬ "bids" = "read")]
  rw [if_pos (by decide : "bids" = "bids")]
  exact endSkipDecodeReturnValues_legacy_bids_ok h256

theorem endSkipDecodeScalarWordsWithMode_legacy_bids_none_short {out : ByteArray}
    (hshort : out.size < 256) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, addr, uint48, uint48, addr, addr, uint256]
        out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          some (endUIntValue (endSkipBidsBidWord out), 0 + 32) := by
      simpa [uint256, uint256Int, abiUInt256, endSkipBidsBidWord, endUIntValue,
        List.drop_zero] using
        (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endUIntValue (endSkipBidsLotWord out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endSkipBidsLotWord, endUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind, Nat.reduceAdd]
      by_cases h64 : ((out.toList.drop 64).take 32).length = 32
      · have hdec64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 64 =
              some (.address (AccountAddress.ofNat (endSkipBidsWord2 out).toNat),
                64 + 32) := by
          simpa [addr, abiAddress, endSkipBidsWord2] using
            (decodeScalarWord_legacyAddress_ok (bytes := out.toList)
              (start := 64) h64)
        rw [hdec64]
        simp only [Option.bind, bind, Nat.reduceAdd]
        by_cases h96 : ((out.toList.drop 96).take 32).length = 32
        · have hdec96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 96 =
                some (endSkipBidsUint48Value (endSkipBidsWord3 out), 96 + 32) := by
            simpa [endSkipBidsUint48Value, endSkipBidsWord3] using
              (endDecodeScalarWordWithMode_legacy_uint48_ok
                (bytes := out.toList) (start := 96) h96)
          rw [hdec96]
          simp only [Option.bind, bind, Nat.reduceAdd]
          by_cases h128 : ((out.toList.drop 128).take 32).length = 32
          · have hdec128 :
                decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 128 =
                  some (endSkipBidsUint48Value (endSkipBidsWord4 out), 128 + 32) := by
              simpa [endSkipBidsUint48Value, endSkipBidsWord4] using
                (endDecodeScalarWordWithMode_legacy_uint48_ok
                  (bytes := out.toList) (start := 128) h128)
            rw [hdec128]
            simp only [Option.bind, bind, Nat.reduceAdd]
            by_cases h160 : ((out.toList.drop 160).take 32).length = 32
            · have hdec160 :
                  decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 160 =
                    some (.address (AccountAddress.ofNat
                      (endSkipBidsUsrWord out).toNat), 160 + 32) := by
                simpa [addr, abiAddress, endSkipBidsUsrWord] using
                  (decodeScalarWord_legacyAddress_ok (bytes := out.toList)
                    (start := 160) h160)
              rw [hdec160]
              simp only [Option.bind, bind, Nat.reduceAdd]
              by_cases h192 : ((out.toList.drop 192).take 32).length = 32
              · have hdec192 :
                    decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 192 =
                      some (.address (AccountAddress.ofNat
                        (endSkipBidsWord6 out).toNat), 192 + 32) := by
                  simpa [addr, abiAddress, endSkipBidsWord6] using
                    (decodeScalarWord_legacyAddress_ok (bytes := out.toList)
                      (start := 192) h192)
                rw [hdec192]
                simp only [Option.bind, bind, Nat.reduceAdd]
                by_cases h224 : ((out.toList.drop 224).take 32).length = 32
                · have hge : 256 ≤ out.size := by
                    rw [List.length_take, List.length_drop, hlen] at h224
                    omega
                  omega
                · have hnone224 :
                      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256
                        out.toList 224 = none := by
                    simpa [uint256, uint256Int, abiUInt256] using
                      (decodeScalarWordWithMode_uint256_none_short
                        (mode := DecodeMode.legacySolc05) (bytes := out.toList)
                        (start := 224) h224)
                  rw [hnone224]
              · have hnone192 :
                    decodeScalarWordWithMode? DecodeMode.legacySolc05 addr
                      out.toList 192 = none := by
                  simpa [addr, abiAddress] using
                    (decodeScalarWord_legacyAddress_none_short
                      (bytes := out.toList) (start := 192) h192)
                rw [hnone192]
            · have hnone160 :
                  decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 160 =
                    none := by
                simpa [addr, abiAddress] using
                  (decodeScalarWord_legacyAddress_none_short
                    (bytes := out.toList) (start := 160) h160)
              rw [hnone160]
          · have hnone128 :
                decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 128 =
                  none := by
              exact endDecodeScalarWordWithMode_legacy_uint48_none_short
                (bytes := out.toList) (start := 128) h128
            rw [hnone128]
        · have hnone96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 out.toList 96 =
                none := by
            exact endDecodeScalarWordWithMode_legacy_uint48_none_short
              (bytes := out.toList) (start := 96) h96
          rw [hnone96]
      · have hnone64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 64 = none := by
          simpa [addr, abiAddress] using
            (decodeScalarWord_legacyAddress_none_short
              (bytes := out.toList) (start := 64) h64)
        rw [hnone64]
    · have hnone32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            none := by
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList)
            (start := 32) h32)
      rw [hnone32]
  · have hnone0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          none := by
      simpa [uint256, uint256Int, abiUInt256] using
        (decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (bytes := out.toList)
          (start := 0) h0)
    rw [hnone0]
    rfl

theorem endSkipDecodeReturnValues_legacy_bids_none_short {out : ByteArray}
    (hshort : out.size < 256) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out =
      none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, addr, uint48, uint48, addr, addr,
      uint256] = some 256 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (bytes := out.toList) (cursor := 0) (total := 256)
    (by decide) (by decide)]
  rw [endSkipDecodeScalarWordsWithMode_legacy_bids_none_short hshort]

theorem endExternalDecode_bids_none_short {out : ByteArray} (hshort : out.size < 256) :
    config.externalABI.decode? "bids" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "bids" = "cage")]
  rw [if_neg (by decide : ¬ "bids" = "vatIlks")]
  rw [if_neg (by decide : ¬ "bids" = "catIlks")]
  rw [if_neg (by decide : ¬ "bids" = "dogIlks")]
  rw [if_neg (by decide : ¬ "bids" = "spotIlks")]
  rw [if_neg (by decide : ¬ "bids" = "urns")]
  rw [if_neg (by decide : ¬ "bids" = "dai")]
  rw [if_neg (by decide : ¬ "bids" = "debt")]
  rw [if_neg (by decide : ¬ "bids" = "par")]
  rw [if_neg (by decide : ¬ "bids" = "tell")]
  rw [if_neg (by decide : ¬ "bids" = "read")]
  rw [if_pos (by decide : "bids" = "bids")]
  exact endSkipDecodeReturnValues_legacy_bids_none_short hshort

theorem endX_skip_flip_no_code_after_vat {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (hflipNoCode : extCodeSizeWord world.2 (endSkipFlipTarget outCat) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3559⟩
      (endSkipAfterVatIlksCursor I sel aw outCat outVat world).stack
      (endSkipVatIlksReturnMem I outCat outVat) (endSkipAfterVatIlksAw aw) outVat
      world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (endSkipCatIlksFlipWord outCat)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endSkipFlipTarget outCat := by
    rw [hmaskGenerated]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (endSkipCatIlksFlipWord outCat)
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    rw [htarget, hflipNoCode]
    native_decide
  obtain ⟨aw3644, k3644, C3644, rd3644⟩ :=
    endRuntimeBlocks.endRuntime_block_3559_packed
      (x0 := UInt256.ofNat outVat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSkipCatIlksFlipWord outCat)
      (x4 := endSkipCatIlksFlipWord outCat) (x5 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSkipAfterVatIlksCursor] using rd)
  have hret64 := endSkipVatIlksReturnMem_mload64 I outCat outVat
    houtCat h96 houtVat h160
  have hrate := endSkipVatIlksReturnMem_mload160 I outCat outVat
    houtCat h96 houtVat h160
  have hcall64 := endSkipBidsCallMem_mload64 I outCat outVat
    houtCat h96 houtVat h160
  have hcall64Generated :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_3559_memory
          (mem := endSkipVatIlksReturnMem I outCat outVat) (x5 := endArg1Word I)) =
        ⟨128⟩ := by
    simpa [endSkipBidsCallMem] using hcall64
  have hcallAfterRet :
      memLoad (UInt256.ofNat 64)
        ((endArg1Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write
            0 (endSkipVatIlksReturnMem I outCat outVat) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_3559_memory, hret64] using
      hcall64Generated
  have hrateAt160 :
      memLoad ((UInt256.ofNat 32) + (⟨128⟩ : UInt256))
        (endSkipVatIlksReturnMem I outCat outVat) =
      endFlowVatIlksRateWord outVat := by
    simpa [show (UInt256.ofNat 32) + (⟨128⟩ : UInt256) =
        UInt256.ofNat 160 from by native_decide] using hrate
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackSetup :
      endRuntimeBlocks.endRuntime_block_3559_stack
          (mem := endSkipVatIlksReturnMem I outCat outVat) (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat))
          (x3 := endSkipCatIlksFlipWord outCat)
          (x4 := endSkipCatIlksFlipWord outCat) (x5 := endArg1Word I)
          (R := [endArg0Word I, ⟨562⟩, sel]) =
        [⟨3649⟩,
          UInt256.isZero
            (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))),
          UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))] ++
          endSkipBidsCallStack I outCat outVat sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_3559_stack, endSkipBidsCallStack,
      endSkipBidsCallRest, endSkipFlipTarget, endSkipBidsSelectorWord]
    rw [hret64, hcallAfterRet, hrateAt160, hlen, hend, htarget]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 256 = (⟨256⟩ : UInt256) from by native_decide]
    rfl
  have rd3644' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3644⟩
        ([⟨3649⟩,
          UInt256.isZero
            (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))),
          UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))] ++
          endSkipBidsCallStack I outCat outVat sel)
        (endSkipBidsCallMem I outCat outVat) aw3644 outVat world k3644 C3644 := by
    simpa [hstackSetup, endSkipBidsCallMem] using rd3644
  have rd3645 := endRuntimeBlocks.endRuntime_block_3644_fallthrough
    (x0 := (⟨3649⟩ : UInt256))
    (x1 := UInt256.isZero
      (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))))
    (R := UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
      endSkipBidsCallStack I outCat outVat sel)
    (by simp [endSkipBidsCallStack, endSkipBidsCallRest]) hcondCode
    (by simpa using rd3644')
  exact endRuntimeBlocks.endRuntime_block_3645
    (R := endRuntimeBlocks.endRuntime_block_3644_fallthrough_stack
      (R := UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
        endSkipBidsCallStack I outCat outVat sel))
    (by simp [endRuntimeBlocks.endRuntime_block_3644_fallthrough_stack,
      endSkipBidsCallStack, endSkipBidsCallRest])
    rd3645

set_option maxHeartbeats 12000000 in
theorem endX_skip_after_vat_to_bids_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (hflipCode : extCodeSizeWord world.2 (endSkipFlipTarget outCat) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3559⟩
      (endSkipAfterVatIlksCursor I sel aw outCat outVat world).stack
      (endSkipVatIlksReturnMem I outCat outVat) (endSkipAfterVatIlksAw aw) outVat
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3651⟩
      (endSkipBidsCallStack I outCat outVat sel) (endSkipBidsCallMem I outCat outVat)
      aw' outVat world k' C' := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (endSkipCatIlksFlipWord outCat)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endSkipFlipTarget outCat := by
    rw [hmaskGenerated]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (endSkipCatIlksFlipWord outCat)
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠
        UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord world.2
            (UInt256.land (endSkipCatIlksFlipWord outCat)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [htarget]
      exact hflipCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw3644, k3644, C3644, rd3644⟩ :=
    endRuntimeBlocks.endRuntime_block_3559_packed
      (x0 := UInt256.ofNat outVat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSkipCatIlksFlipWord outCat)
      (x4 := endSkipCatIlksFlipWord outCat) (x5 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSkipAfterVatIlksCursor] using rd)
  have hret64 := endSkipVatIlksReturnMem_mload64 I outCat outVat
    houtCat h96 houtVat h160
  have hrate := endSkipVatIlksReturnMem_mload160 I outCat outVat
    houtCat h96 houtVat h160
  have hcall64 := endSkipBidsCallMem_mload64 I outCat outVat
    houtCat h96 houtVat h160
  have hcall64Generated :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_3559_memory
          (mem := endSkipVatIlksReturnMem I outCat outVat) (x5 := endArg1Word I)) =
        ⟨128⟩ := by
    simpa [endSkipBidsCallMem] using hcall64
  have hcallAfterRet :
      memLoad (UInt256.ofNat 64)
        ((endArg1Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write
            0 (endSkipVatIlksReturnMem I outCat outVat) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_3559_memory, hret64] using
      hcall64Generated
  have hrateAt160 :
      memLoad ((UInt256.ofNat 32) + (⟨128⟩ : UInt256))
        (endSkipVatIlksReturnMem I outCat outVat) =
      endFlowVatIlksRateWord outVat := by
    simpa [show (UInt256.ofNat 32) + (⟨128⟩ : UInt256) =
        UInt256.ofNat 160 from by native_decide] using hrate
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackSetup :
      endRuntimeBlocks.endRuntime_block_3559_stack
          (mem := endSkipVatIlksReturnMem I outCat outVat) (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat outVat))
          (x3 := endSkipCatIlksFlipWord outCat)
          (x4 := endSkipCatIlksFlipWord outCat) (x5 := endArg1Word I)
          (R := [endArg0Word I, ⟨562⟩, sel]) =
        [⟨3649⟩,
          UInt256.isZero
            (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))),
          UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))] ++
          endSkipBidsCallStack I outCat outVat sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_3559_stack, endSkipBidsCallStack,
      endSkipBidsCallRest, endSkipFlipTarget, endSkipBidsSelectorWord]
    rw [hret64, hcallAfterRet, hrateAt160, hlen, hend, htarget]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 256 = (⟨256⟩ : UInt256) from by native_decide]
    rfl
  have rd3644' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3644⟩
        ([⟨3649⟩,
          UInt256.isZero
            (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))),
          UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))] ++
          endSkipBidsCallStack I outCat outVat sel)
        (endSkipBidsCallMem I outCat outVat) aw3644 outVat world k3644 C3644 := by
    simpa [hstackSetup, endSkipBidsCallMem] using rd3644
  have rd3649 := endRuntimeBlocks.endRuntime_block_3644_taken
    (x0 := (⟨3649⟩ : UInt256))
    (x1 := UInt256.isZero
      (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat))))
    (R := UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
      endSkipBidsCallStack I outCat outVat sel)
    (by simp [endSkipBidsCallStack, endSkipBidsCallRest]) hcondCode
    (by jump_dest) (by simpa using rd3644')
  have rd3649' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3649⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
          endSkipBidsCallStack I outCat outVat sel)
        (endSkipBidsCallMem I outCat outVat) aw3644 outVat world (k3644 + 1)
        (C3644 + 10) := by
    simpa [endRuntimeBlocks.endRuntime_block_3644_taken_stack] using rd3649
  have rd3651 := endRuntimeBlocks.endRuntime_block_3649
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)))
    (R := endSkipBidsCallStack I outCat outVat sel)
    (by simp [endSkipBidsCallStack, endSkipBidsCallRest]) rd3649'
  exact ⟨aw3644, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3649_stack] using rd3651⟩

set_option maxHeartbeats 12000000 in
theorem endSkipBidsExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipBidsCallCursor world I sel aw outCat outVat rdata)
      k C (endSkipAfterRateFrame I outCat outVat) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
          (perm := false) ]
      (sequenceExit ⟨3692⟩
        (fun cur frame e =>
          frame = endSkipAfterBidsFrame I outCat outVat cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          256 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endSkipBidsReturnMem I outCat outVat cur.rdata),
              ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSkipBidsReturnMem I outCat outVat cur.rdata ∧
          cur.aw = endSkipAfterBidsAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨3651⟩ = some (.GAS, .none); decide)
    (by simp [endSkipBidsCallCursor, endSkipBidsCallStack, endSkipBidsCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)
    (argVals := [endUIntValue (endArg1Word I)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨3652⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endSkipBidsCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro _
    exact endEvalFlipAddress_skipAfterRate_masked evm I outCat outVat
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkipBidsArgsAfterRate evm I outCat outVat
  · intro _
    apply Fin.ext
    show (endSkipFlipTarget outCat).toNat % EVM.addressModulus % AccountAddress.size =
      (endSkipFlipTarget outCat).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_bids_skip I]
    change some (endSkipBidsEncodedCall I) =
      some ((endSkipBidsCallMem I outCat outVat).readWithPadding 128 36)
    rw [endSkipBidsCallMem_readCallData I outCat outVat houtCat h96 houtVat h160]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h256 : 256 ≤ out.size
    · rw [endExternalDecode_bids_ok h256]
      intro rd hrel
      have rd3653 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
            ((⟨1⟩ : UInt256) :: endSkipBidsCallRest I outCat outVat sel)
            (endSkipBidsReturnMem I outCat outVat out) (endSkipBidsCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipBidsCallCursor, endSkipBidsCallStack,
          endSkipBidsCallRest, endSkipBidsCallAw, endSkipBidsReturnMem] using rd
      have rd3669 := endRuntimeBlocks.endRuntime_block_3653_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipBidsCallRest I outCat outVat sel)
        (by simp [endSkipBidsCallRest]) (by native_decide) (by jump_dest) rd3653
      have rd3669' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3669⟩
            [⟨0⟩, ⟨164⟩, endSkipBidsSelectorWord, endSkipFlipTarget outCat,
              ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipBidsReturnMem I outCat outVat out) (endSkipBidsCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3653_taken_stack,
          endSkipBidsCallRest] using rd3669
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 256) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 256).toNat = 256 from by native_decide,
          ulit_toNat' out.size hout]
        exact h256
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 256)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3692 := endRuntimeBlocks.endRuntime_block_3669_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endSkipBidsSelectorWord) (x3 := endSkipFlipTarget outCat)
        (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd3669'
      refine ⟨.ok (endSkipAfterBidsFrame I outCat outVat out) evm',
        Endpoint.reached (endSkipAfterBidsCursor I sel aw outCat outVat out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSkipAfterBidsCursor, endSkipAfterBidsAw,
            endRuntimeBlocks.endRuntime_block_3669_taken_stack] using rd3692⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h256, rfl, rfl, rfl⟩
    · have hshort : out.size < 256 := by omega
      rw [endExternalDecode_bids_none_short hshort]
      intro rd
      have rd3653 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
            ((⟨1⟩ : UInt256) :: endSkipBidsCallRest I outCat outVat sel)
            (endSkipBidsReturnMem I outCat outVat out) (endSkipBidsCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkipBidsCallCursor, endSkipBidsCallStack,
          endSkipBidsCallRest, endSkipBidsCallAw, endSkipBidsReturnMem] using rd
      have rd3669 := endRuntimeBlocks.endRuntime_block_3653_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkipBidsCallRest I outCat outVat sel)
        (by simp [endSkipBidsCallRest]) (by native_decide) (by jump_dest) rd3653
      have rd3669' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3669⟩
            [⟨0⟩, ⟨164⟩, endSkipBidsSelectorWord, endSkipFlipTarget outCat,
              ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSkipBidsReturnMem I outCat outVat out) (endSkipBidsCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_3653_taken_stack,
          endSkipBidsCallRest] using rd3669
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 256) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 256).toNat = 256 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 256)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3688 := endRuntimeBlocks.endRuntime_block_3669_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endSkipBidsSelectorWord) (x3 := endSkipFlipTarget outCat)
        (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd3669'
      exact endRuntimeBlocks.endRuntime_block_3688
        (R := endRuntimeBlocks.endRuntime_block_3669_fallthrough_stack
          (mem := endSkipBidsReturnMem I outCat outVat out) (rdata := out)
          (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
            endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_3669_fallthrough_stack])
        rd3688
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd3653 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
          ((⟨0⟩ : UInt256) :: endSkipBidsCallRest I outCat outVat sel)
          (endSkipBidsReturnMem I outCat outVat out) (endSkipBidsCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSkipBidsCallCursor, endSkipBidsCallStack,
        endSkipBidsCallRest, endSkipBidsCallAw, endSkipBidsReturnMem] using rd
    have rd3660 := endRuntimeBlocks.endRuntime_block_3653_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipBidsCallRest I outCat outVat sel)
      (by simp [endSkipBidsCallRest]) (by native_decide) rd3653
    exact endRuntimeBlocks.endRuntime_block_3660
      (R := endRuntimeBlocks.endRuntime_block_3653_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipBidsCallRest I outCat outVat sel))
      (by simp [endRuntimeBlocks.endRuntime_block_3653_fallthrough_stack,
        endSkipBidsCallRest])
      rd3660

abbrev endSkipAfterBidsRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outCat : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ outVat awBids,
      frame = endSkipAfterBidsFrame I outCat outVat cur.rdata ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      cur.rdata.size < UInt256.size ∧
      256 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat cur.rdata),
          ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endSkipBidsReturnMem I outCat outVat cur.rdata ∧
      cur.aw = endSkipAfterBidsAw awBids

set_option maxHeartbeats 12000000 in
theorem endSkipAfterVatIlksToBidsRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3559⟩
      (fun cur frame e =>
        frame = endSkipAfterVatIlksFrame I outCat cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        160 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat cur.rdata),
            ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSkipVatIlksReturnMem I outCat cur.rdata ∧
        cur.aw = endSkipAfterVatIlksAw aw)
      ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false))
      (sequenceExit ⟨3692⟩
        (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, houtVat, h160, hstack, hmem, haw⟩
  cases hframe
  have rd3559 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3559⟩
        [UInt256.ofNat cur0.rdata.size,
          memLoad (UInt256.ofNat 64) (endSkipVatIlksReturnMem I outCat cur0.rdata),
          ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipVatIlksReturnMem I outCat cur0.rdata) (endSkipAfterVatIlksAw aw)
        cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsourceRate :
      ExecBlock config (endSkipAfterVatIlksFrame I outCat cur0.rdata) evm
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok (endSkipAfterRateFrame I outCat cur0.rdata) evm) :=
    ExecBlock.consNormal (endLetSkipRate evm I outCat cur0.rdata) ExecBlock.nil
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) =
        extCodeSizeWord cur0.world.2 (endSkipFlipTarget outCat) :=
    (extCodeSizeWord_accountMapEquiv hrel.accounts (endSkipFlipTarget outCat)).symm
  by_cases hflipNoCode :
      extCodeSizeWord cur0.world.2 (endSkipFlipTarget outCat) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) = ⟨0⟩ := by
      rw [hsrcCodeEq, hflipNoCode]
    have hsourceChecked :
        ExecBlock config (endSkipAfterRateFrame I outCat cur0.rdata) evm
          (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
            "flipBid" (perm := false))
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalFlipCodeGuard_skipAfterRate_false evm I outCat cur0.rdata
              hsrcNoCode)))
    have hsourceFull :
        ExecBlock config (endSkipAfterVatIlksFrame I outCat cur0.rdata) evm
          ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
            checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
              "flipBid" (perm := false))
          .reverted :=
      Reasoning.Theory.execBlock_append hsourceRate hsourceChecked
    have hrev := endX_skip_flip_no_code_after_vat
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      (outVat := cur0.rdata) (k := k) (C := C) (world := cur0.world)
      houtCat h96 houtVat h160 hflipNoCode rd3559
    exact ⟨.reverted, .reverted, hsourceFull, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) ≠ ⟨0⟩ := by
      intro hzero
      exact hflipNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkipAfterRateFrame I outCat cur0.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) ]
          (.ok (endSkipAfterRateFrame I outCat cur0.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalFlipCodeGuard_skipAfterRate_true evm I outCat cur0.rdata hsrcCode))
        ExecBlock.nil
    obtain ⟨aw3651, k3651, C3651, rd3651⟩ :=
      endX_skip_after_vat_to_bids_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
        (outVat := cur0.rdata) (k := k) (C := C) (world := cur0.world)
        houtCat h96 houtVat h160 hflipNoCode rd3559
    have htailExact :=
      (endSkipBidsExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw3651) (outCat := outCat)
        (outVat := cur0.rdata) (rdata := cur0.rdata) (k := k3651) (C := C3651)
        (evm := evm) (world := cur0.world)
        houtCat h96 houtVat h160)
        (by simpa [endSkipBidsCallCursor] using rd3651) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterRateFrame I outCat cur0.rdata) evm
          [ .externalCall (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
              (perm := false) ]
          (sequenceExit ⟨3692⟩
            (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with
                ⟨hpcQ, hframeQ, hrelQ, _hstatic, houtBids, h256, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, cur0.rdata, aw3651, hframeQ, hrelQ, houtVat, h160,
                houtBids, h256, hstackQ, hmemQ, hawQ⟩
          | returned worldOut outOut =>
              exact hQ
          | reverted =>
              exact hQ
      | returned frameOut evmOut ret =>
          exact hQ
      | «break» frameOut evmOut =>
          exact hQ
      | «continue» frameOut evmOut =>
          exact hQ
      | reverted =>
          exact hQ
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterRateFrame I outCat cur0.rdata) evm
          (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
            "flipBid" (perm := false))
          (sequenceExit ⟨3692⟩
            (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa using BlockProgress.prepend hsourceRate hcheckedProgress

abbrev endSkipBidValue (outBids : ByteArray) : Value :=
  endUIntValue (endSkipBidsBidWord outBids)

abbrev endSkipLotValue (outBids : ByteArray) : Value :=
  endUIntValue (endSkipBidsLotWord outBids)

abbrev endSkipUsrValue (outBids : ByteArray) : Value :=
  .address (AccountAddress.ofNat (endSkipBidsUsrWord outBids).toNat)

abbrev endSkipTabValue (outBids : ByteArray) : Value :=
  endUIntValue (endSkipBidsTabWord outBids)

abbrev endSkipAfterBidFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids) }

abbrev endSkipAfterLotFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids) }

abbrev endSkipAfterUsrFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids) }

abbrev endSkipAfterTabFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterUsrFrame I outCat outVat outBids).locals.insert "tab"
      (endSkipTabValue outBids) }

abbrev endSkipSuckSelectorWord : UInt256 :=
  UInt256.ofNat 4065207275

abbrev endSkipSuckSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft endSkipSuckSelectorWord (UInt256.ofNat 224)

def endSkipSuck1PayloadBytes (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) : List UInt8 :=
  (EVM.Word.toBytesBE (endPackVowTarget σ I) ++
    EVM.Word.toBytesBE (endPackVowTarget σ I)) ++
    EVM.Word.toBytesBE (endSkipBidsTabWord outBids)

def endSkipSuck1EncodedCall (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) : ByteArray :=
  suckSelector ++ ⟨(endSkipSuck1PayloadBytes σ I outBids).toArray⟩

abbrev endSkipSuck1MemSel (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    ByteArray :=
  endSkipSuckSelectorEncodedWord.toByteArray.write 0
    (endSkipBidsReturnMem I outCat outVat outBids) 128 32

abbrev endSkipSuck1MemVow0 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endPackVowTarget σ I).toByteArray.write 0
    (endSkipSuck1MemSel I outCat outVat outBids) 132 32

abbrev endSkipSuck1MemVow1 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endPackVowTarget σ I).toByteArray.write 0
    (endSkipSuck1MemVow0 σ I outCat outVat outBids) 164 32

abbrev endSkipSuck1CallMem (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endSkipBidsTabWord outBids).toByteArray.write 0
    (endSkipSuck1MemVow1 σ I outCat outVat outBids) 196 32

abbrev endSkipSuck1CallRest (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨228⟩, endSkipSuckSelectorWord, endPackVatTarget σ I,
    endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
    endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
    endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
    endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipSuck1CallStack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩] ++
    endSkipSuck1CallRest σ I outCat outVat outBids sel

abbrev endSkipSuck1CallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outCat outVat outBids rdata : ByteArray) :
    Cursor :=
  { pc := ⟨3819⟩,
    stack := endSkipSuck1CallStack world.2 I outCat outVat outBids sel,
    mem := endSkipSuck1CallMem world.2 I outCat outVat outBids,
    aw := aw, rdata := rdata, world := world }

abbrev endSkipSuck1CallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨100⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSkipAfterSuck1Frame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns []) }

abbrev endSkipAfterSuck1Stack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSkipSuck1CallRest σ I outCat outVat outBids sel

abbrev endSkipAfterSuck1Cursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outCat outVat outBids out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨3837⟩,
    stack := endSkipAfterSuck1Stack σ I outCat outVat outBids sel,
    mem := endSkipSuck1CallMem σ I outCat outVat outBids,
    aw := endSkipSuck1CallAw aw, rdata := out, world := world }

theorem endEvalSkipBidFromFlipBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterBidsFrame I outCat outVat outBids) evm
      (.tupleGet (.var "flipBid") 0) =
      .ok (endSkipBidValue outBids) := by
  simp [evalExpr?, endSkipAfterBidsFrame, collapseReturns, tupleGetValue?,
    endSkipBidsValues, endSkipBidValue, EvalResult.ofOption, EvalResult.bind, bind,
    endUIntValue]

theorem endLetSkipBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    ExecStmt config (endSkipAfterBidsFrame I outCat outVat outBids) evm
      (.letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0))
      (.ok (endSkipAfterBidFrame I outCat outVat outBids) evm) := by
  simpa [endSkipAfterBidFrame] using
    ExecStmt.letDecl (endEvalSkipBidFromFlipBid evm I outCat outVat outBids)

theorem endSkipAfterBidFrame_get_flipBid (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterBidFrame I outCat outVat outBids).locals.get? "flipBid" =
      some (collapseReturns (endSkipBidsValues outBids)) := by
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "flipBid") =
    some (collapseReturns (endSkipBidsValues outBids))
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "flipBid") (endSkipBidValue outBids) (by decide)]
  exact store_get_self (endSkipAfterRateFrame I outCat outVat).locals
    "flipBid" (collapseReturns (endSkipBidsValues outBids))

theorem endEvalSkipFlipBidAfterBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterBidFrame I outCat outVat outBids) evm
      (.var "flipBid") =
      .ok (collapseReturns (endSkipBidsValues outBids)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterBidFrame_get_flipBid I outCat outVat outBids

theorem endEvalSkipLotFromFlipBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterBidFrame I outCat outVat outBids) evm
      (.tupleGet (.var "flipBid") 1) =
      .ok (endSkipLotValue outBids) := by
  rw [evalExpr?]
  rw [endEvalSkipFlipBidAfterBid evm I outCat outVat outBids]
  simp [tupleGetValue?, collapseReturns, endSkipBidsValues, endSkipLotValue,
    EvalResult.bind, bind, endUIntValue]

theorem endLetSkipLot (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    ExecStmt config (endSkipAfterBidFrame I outCat outVat outBids) evm
      (.letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1))
      (.ok (endSkipAfterLotFrame I outCat outVat outBids) evm) := by
  simpa [endSkipAfterLotFrame] using
    ExecStmt.letDecl (endEvalSkipLotFromFlipBid evm I outCat outVat outBids)

theorem endSkipAfterLotFrame_get_flipBid (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterLotFrame I outCat outVat outBids).locals.get? "flipBid" =
      some (collapseReturns (endSkipBidsValues outBids)) := by
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "flipBid") =
    some (collapseReturns (endSkipBidsValues outBids))
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "flipBid") (endSkipLotValue outBids) (by decide)]
  exact endSkipAfterBidFrame_get_flipBid I outCat outVat outBids

theorem endEvalSkipFlipBidAfterLot (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterLotFrame I outCat outVat outBids) evm
      (.var "flipBid") =
      .ok (collapseReturns (endSkipBidsValues outBids)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterLotFrame_get_flipBid I outCat outVat outBids

theorem endEvalSkipUsrFromFlipBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterLotFrame I outCat outVat outBids) evm
      (.tupleGet (.var "flipBid") 5) =
      .ok (endSkipUsrValue outBids) := by
  rw [evalExpr?]
  rw [endEvalSkipFlipBidAfterLot evm I outCat outVat outBids]
  simp [tupleGetValue?, collapseReturns, endSkipBidsValues, endSkipUsrValue,
    EvalResult.bind, bind]

theorem endLetSkipUsr (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    ExecStmt config (endSkipAfterLotFrame I outCat outVat outBids) evm
      (.letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5))
      (.ok (endSkipAfterUsrFrame I outCat outVat outBids) evm) := by
  simpa [endSkipAfterUsrFrame] using
    ExecStmt.letDecl (endEvalSkipUsrFromFlipBid evm I outCat outVat outBids)

theorem endSkipAfterUsrFrame_get_flipBid (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterUsrFrame I outCat outVat outBids).locals.get? "flipBid" =
      some (collapseReturns (endSkipBidsValues outBids)) := by
  change (((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).get? "flipBid") =
    some (collapseReturns (endSkipBidsValues outBids))
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "flipBid") (endSkipUsrValue outBids) (by decide)]
  exact endSkipAfterLotFrame_get_flipBid I outCat outVat outBids

theorem endEvalSkipFlipBidAfterUsr (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterUsrFrame I outCat outVat outBids) evm
      (.var "flipBid") =
      .ok (collapseReturns (endSkipBidsValues outBids)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterUsrFrame_get_flipBid I outCat outVat outBids

theorem endEvalSkipTabFromFlipBid (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterUsrFrame I outCat outVat outBids) evm
      (.tupleGet (.var "flipBid") 7) =
      .ok (endSkipTabValue outBids) := by
  rw [evalExpr?]
  rw [endEvalSkipFlipBidAfterUsr evm I outCat outVat outBids]
  simp [tupleGetValue?, collapseReturns, endSkipBidsValues, endSkipTabValue,
    EvalResult.bind, bind, endUIntValue]

theorem endLetSkipTab (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    ExecStmt config (endSkipAfterUsrFrame I outCat outVat outBids) evm
      (.letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7))
      (.ok (endSkipAfterTabFrame I outCat outVat outBids) evm) := by
  simpa [endSkipAfterTabFrame] using
    ExecStmt.letDecl (endEvalSkipTabFromFlipBid evm I outCat outVat outBids)

theorem endSkipAfterTabFrame_get_tab (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterTabFrame I outCat outVat outBids).locals.get? "tab" =
      some (endSkipTabValue outBids) := by
  exact store_get_self (endSkipAfterUsrFrame I outCat outVat outBids).locals
    "tab" (endSkipTabValue outBids)

theorem endEvalSkipTabAfterTab (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterTabFrame I outCat outVat outBids) evm (.var "tab") =
      .ok (endSkipTabValue outBids) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterTabFrame_get_tab I outCat outVat outBids

theorem endSkipAfterTabFrame_get_vat_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterTabFrame I outCat outVat outBids).locals.get? "vat" = none := by
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "vat") = none
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "vat")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "vat") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "vat") = none
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "vat") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "vat") = none
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "vat") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "vat") = none
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "vat") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "vat") = none
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "vat")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "vat") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact endSkipAfterFlipFrame_get_vat_none I outCat

theorem endSkipAfterTabFrame_get_vow_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterTabFrame I outCat outVat outBids).locals.get? "vow" = none := by
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "vow") = none
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "vow")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "vow") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "vow") = none
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "vow") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "vow") = none
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "vow") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "vow") = none
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "vow") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "vow") = none
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "vow")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "vow") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSkipAfterCatIlksFrame I outCat).locals.insert "flip"
      (endSkipFlipValue outCat)).get? "vow") = none
  rw [store_get_ne (endSkipAfterCatIlksFrame I outCat).locals
    (k := "flip") (a := "vow") (endSkipFlipValue outCat) (by decide)]
  change (((endSkipStore I).insert "catIlk"
      (collapseReturns (endSkipCatIlksValues outCat))).get? "vow") = none
  rw [store_get_ne (endSkipStore I) (k := "catIlk")
    (a := "vow") (collapseReturns (endSkipCatIlksValues outCat)) (by decide)]
  simp [endSkipStore]

theorem endEvalVatAddress_skipAfterTab (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterTabFrame I outCat outVat outBids) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterTabFrame I outCat outVat outBids).locals) (evm := evm)
    (slot := vatRef) (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSkipAfterTabFrame_get_vat_none I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVowAddress_skipAfterTab (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterTabFrame I outCat outVat outBids) evm vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterTabFrame I outCat outVat outBids).locals) (evm := evm)
    (slot := vowRef) (er := { base := "vow", steps := [] }) (wordSlot := UInt256.ofNat 4)
    (endSkipAfterTabFrame_get_vow_none I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vow)

theorem endEvalVatCodeGuard_skipAfterTab_false (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkipAfterTabFrame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterTabFrame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterTab evm I outCat outVat outBids) hnocode

theorem endEvalVatCodeGuard_skipAfterTab_true (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterTabFrame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterTabFrame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterTab evm I outCat outVat outBids) hcode

theorem endEvalSkipSuck1ArgsAfterTab (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExprs? config (endSkipAfterTabFrame I outCat outVat outBids) evm
      [vowAddr, vowAddr, .var "tab"] =
      .ok [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        endSkipTabValue outBids] := by
  simp [evalExprs?, EvalResult.bind, bind, pure,
    endEvalVowAddress_skipAfterTab evm I outCat outVat outBids,
    endEvalSkipTabAfterTab evm I outCat outVat outBids]

theorem endSkipBidsReturnMem_readCopied32 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (off : Nat) (hoff : off + 32 ≤ 256) :
    (endSkipBidsReturnMem I outCat outVat outBids).readWithPadding (128 + off) 32 =
      outBids.extract off (off + 32) := by
  have hcopy :
      (min (⟨256⟩ : UInt256) (UInt256.ofNat outBids.size)).toNat = 256 := by
    rw [callCopyLength_toNat outBids (⟨256⟩ : UInt256) houtBids]
    rw [show (⟨256⟩ : UInt256).toNat = 256 from by native_decide]
    exact Nat.min_eq_left h256
  unfold endSkipBidsReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outBids (endSkipBidsCallMem I outCat outVat) 128 256
    (by decide) h256
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)
    (by rw [endSkipBidsCallMem_size I outCat outVat houtCat h96 houtVat h160]; omega)]
  have hpre : ((endSkipBidsCallMem I outCat outVat).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipBidsCallMem_size I outCat outVat houtCat h96
      houtVat h160]
    omega
  have hcopySize : (outBids.extract 0 256).size = 256 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ (128 + off) (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [hpre]; omega), hpre]
  rw [show 128 + off - 128 = off by omega,
    show 128 + off + 32 - 128 = off + 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + off = off by omega, show min (0 + (off + 32)) 256 = off + 32 by omega]

theorem endSkipBidsReturnMem_mload128 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 128) (endSkipBidsReturnMem I outCat outVat outBids) =
      endSkipBidsBidWord outBids := by
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endSkipBidsReturnMem_size I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega)]
  rw [show 128 = 128 + 0 by omega]
  rw [endSkipBidsReturnMem_readCopied32 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256 0 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (outBids.extract 0 (0 + 32))) =
    ABI.bytesToWord ((outBids.toList.drop 0).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outBids 0]

theorem endSkipBidsReturnMem_mload160 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 160) (endSkipBidsReturnMem I outCat outVat outBids) =
      endSkipBidsLotWord outBids := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSkipBidsReturnMem_size I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega)]
  rw [show 160 = 128 + 32 by omega]
  rw [endSkipBidsReturnMem_readCopied32 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256 32 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (outBids.extract 32 (32 + 32))) =
    ABI.bytesToWord ((outBids.toList.drop 32).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outBids 32]

theorem endSkipBidsReturnMem_mload288 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 288) (endSkipBidsReturnMem I outCat outVat outBids) =
      endSkipBidsUsrWord outBids := by
  unfold memLoad
  rw [show (UInt256.ofNat 288).toNat = 288 from by native_decide]
  rw [if_neg (by
    rw [endSkipBidsReturnMem_size I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega)]
  rw [show 288 = 128 + 160 by omega]
  rw [endSkipBidsReturnMem_readCopied32 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256 160 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (outBids.extract 160 (160 + 32))) =
    ABI.bytesToWord ((outBids.toList.drop 160).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outBids 160]

theorem endSkipBidsReturnMem_mload352 (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 352) (endSkipBidsReturnMem I outCat outVat outBids) =
      endSkipBidsTabWord outBids := by
  unfold memLoad
  rw [show (UInt256.ofNat 352).toNat = 352 from by native_decide]
  rw [if_neg (by
    rw [endSkipBidsReturnMem_size I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega)]
  rw [show 352 = 128 + 224 by omega]
  rw [endSkipBidsReturnMem_readCopied32 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256 224 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (outBids.extract 224 (224 + 32))) =
    ABI.bytesToWord ((outBids.toList.drop 224).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outBids 224]

theorem endSkipSuckSelectorEncodedWord_prefix :
    (endSkipSuckSelectorEncodedWord.toByteArray).extract 0 4 = suckSelector := by
  native_decide

theorem endSkipSuck1MemSel_size (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1MemSel I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipBidsReturnMem I outCat outVat outBids)
    endSkipSuckSelectorEncodedWord 128 384 384
    (endSkipBidsReturnMem_size I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipBidsReturnMem_size I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck1MemVow0_size (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1MemVow0 σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck1MemSel I outCat outVat outBids) (endPackVowTarget σ I)
    132 384 384
    (endSkipSuck1MemSel_size σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck1MemSel_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck1MemVow1_size (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1MemVow1 σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck1MemVow0 σ I outCat outVat outBids) (endPackVowTarget σ I)
    164 384 384
    (endSkipSuck1MemVow0_size σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck1MemVow0_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck1CallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck1MemVow1 σ I outCat outVat outBids)
    (endSkipBidsTabWord outBids) 196 384 384
    (endSkipSuck1MemVow1_size σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck1CallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsTabWord outBids)
    (endSkipSuck1MemVow1 σ I outCat outVat outBids) 196 64
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSkipSuck1MemVow0 σ I outCat outVat outBids) 164 64
    (by
      rw [endSkipSuck1MemVow0_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSkipSuck1MemSel I outCat outVat outBids) 132 64
    (by
      rw [endSkipSuck1MemSel_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSkipSuckSelectorEncodedWord
    (endSkipBidsReturnMem I outCat outVat outBids) 128 64
    (by
      rw [endSkipBidsReturnMem_size I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [endSkipBidsReturnMem_read64 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256,
    endSkipBidsCallMem_read64 I outCat outVat houtCat h96 houtVat h160]

theorem endSkipSuck1CallMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64) (endSkipSuck1CallMem σ I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkipSuck1CallMem σ I outCat outVat outBids)
    (by
      rw [endSkipSuck1CallMem_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (endSkipSuck1CallMem_read64 σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

theorem endSkipSuck1CallMem_readSelector (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 128 4 =
      suckSelector := by
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck1MemVow0_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck1MemVow0_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck1MemSel_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck1MemSel_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  change ((endSkipSuckSelectorEncodedWord.toByteArray.write 0
      (endSkipBidsReturnMem I outCat outVat outBids) 128 32).readWithPadding
      128 4) = suckSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipSuckSelectorEncodedWord (endSkipBidsReturnMem I outCat outVat outBids)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipSuckSelectorEncodedWord_prefix]

theorem endSkipSuck1CallMem_readVow0 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 132 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsTabWord outBids)
    (endSkipSuck1MemVow1 σ I outCat outVat outBids) 196 132
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSkipSuck1MemVow0 σ I outCat outVat outBids) 164 132
    (by
      rw [endSkipSuck1MemVow0_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  change ((endPackVowTarget σ I).toByteArray.write 0
      (endSkipSuck1MemSel I outCat outVat outBids) 132 32).readWithPadding
      132 32 = (endPackVowTarget σ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget σ I)
    (endSkipSuck1MemSel I outCat outVat outBids) 132

theorem endSkipSuck1CallMem_readVow1 (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 164 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsTabWord outBids)
    (endSkipSuck1MemVow1 σ I outCat outVat outBids) 196 164
    (by
      rw [endSkipSuck1MemVow1_size σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  change ((endPackVowTarget σ I).toByteArray.write 0
      (endSkipSuck1MemVow0 σ I outCat outVat outBids) 164 32).readWithPadding
      164 32 = (endPackVowTarget σ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget σ I)
    (endSkipSuck1MemVow0 σ I outCat outVat outBids) 164

theorem endSkipSuck1CallMem_readTab (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 196 32 =
      (endSkipBidsTabWord outBids).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endSkipBidsTabWord outBids)
    (endSkipSuck1MemVow1 σ I outCat outVat outBids) 196

theorem endSkipSuck1CallMem_readCallData (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck1CallMem σ I outCat outVat outBids).readWithPadding 128 100 =
      endSkipSuck1EncodedCall σ I outBids := by
  have hsize : 228 ≤ (endSkipSuck1CallMem σ I outCat outVat outBids).size := by
    rw [endSkipSuck1CallMem_size σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  rw [show 100 = 4 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck1CallMem σ I outCat outVat outBids) 128 4 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck1CallMem σ I outCat outVat outBids) 132 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck1CallMem σ I outCat outVat outBids) 164 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [endSkipSuck1CallMem_readSelector σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck1CallMem_readVow0 σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck1CallMem_readVow1 σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck1CallMem_readTab σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_eq_toBytesBE (endPackVowTarget σ I)]
  rw [toByteArray_eq_toBytesBE (endSkipBidsTabWord outBids)]
  simp only [endSkipSuck1EncodedCall, endSkipSuck1PayloadBytes]
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem endEncodeUint_skipTab (outBids : ByteArray) :
    encodeABIValue? uint256 (endSkipTabValue outBids) =
      some (EVM.Word.toBytesBE (endSkipBidsTabWord outBids)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (endSkipTabValue outBids)
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endSkipBidsTabWord outBids))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

theorem endEncodeABIValues_suck_skip1 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    encodeABIValues? [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSkipTabValue outBids] =
      some (endSkipSuck1PayloadBytes σ I outBids) := by
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeUint_skipTab outBids, hdynUint]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSkipSuck1PayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_suck_skip1 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSkipTabValue outBids] =
      some (endSkipSuck1EncodedCall σ I outBids) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_suck_skip1 σ I outBids]
  simp [endSkipSuck1EncodedCall, endSkipSuck1PayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_suck_skip1 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    config.externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSkipTabValue outBids] =
      some (endSkipSuck1EncodedCall σ I outBids) := by
  rw [endExternalEncode_suck_branch]
  exact endEncodeCallWithSelector_suck_skip1 σ I outBids

theorem endSkipSuck1CallMem_generated (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    endRuntimeBlocks.endRuntime_block_3692_memory (ee := I)
        (mem := endSkipBidsReturnMem I outCat outVat outBids) (σ := σ)
        (x1 := memLoad (UInt256.ofNat 64)
          (endSkipBidsReturnMem I outCat outVat outBids)) =
      endSkipSuck1CallMem σ I outCat outVat outBids := by
  have hfree := endSkipBidsReturnMem_mload64 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have htab := endSkipBidsReturnMem_mload352 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endRuntimeBlocks.endRuntime_block_3692_memory
  rw [hfree]
  rw [show (⟨128⟩ : UInt256) + UInt256.ofNat 224 = UInt256.ofNat 352
      from by native_decide]
  rw [htab]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [hmask]

theorem endX_skip_vat_no_code_after_bids {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3692⟩
      (endSkipAfterBidsCursor I sel aw outCat outVat outBids world).stack
      (endSkipBidsReturnMem I outCat outVat outBids) (endSkipAfterBidsAw aw)
      outBids world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSkipBidsReturnMem_mload64 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hbid := endSkipBidsReturnMem_mload128 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hbidAt :
      memLoad (⟨128⟩ : UInt256) (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsBidWord outBids := by
    simpa [show (⟨128⟩ : UInt256) = UInt256.ofNat 128 from by native_decide] using hbid
  have hlot := endSkipBidsReturnMem_mload160 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have husr := endSkipBidsReturnMem_mload288 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have htab := endSkipBidsReturnMem_mload352 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hlotAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsLotWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 32 =
        UInt256.ofNat 160 from by native_decide] using hlot
  have husrAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 160)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsUsrWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 160 =
        UInt256.ofNat 288 from by native_decide] using husr
  have htabAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 224)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsTabWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 224 =
        UInt256.ofNat 352 from by native_decide] using htab
  have hmemGen := endSkipSuck1CallMem_generated world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hcall64 := endSkipSuck1CallMem_mload64 world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hstack3692 :
      endRuntimeBlocks.endRuntime_block_3692_stack
          (ee := I) (mem := endSkipBidsReturnMem I outCat outVat outBids)
          (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64)
            (endSkipBidsReturnMem I outCat outVat outBids))
          (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
          (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
            endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
          endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
          endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
          endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
          endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
          endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_3692_stack]
    change
      [memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids),
        storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 224)
          (endSkipBidsReturnMem I outCat outVat outBids),
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3692_memory
            (ee := I) (mem := endSkipBidsReturnMem I outCat outVat outBids)
            (σ := world.2)
            (x1 := memLoad (UInt256.ofNat 64)
              (endSkipBidsReturnMem I outCat outVat outBids))),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 160)
          (endSkipBidsReturnMem I outCat outVat outBids),
        ⟨0⟩, ⟨0⟩,
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 32)
          (endSkipBidsReturnMem I outCat outVat outBids),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids))
          (endSkipBidsReturnMem I outCat outVat outBids),
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
        endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, htabAt, husrAt, hlotAt, hbidAt]
  obtain ⟨aw3772, k3772, C3772, rd3772⟩ :=
    endRuntimeBlocks.endRuntime_block_3692_packed
      (x0 := UInt256.ofNat outBids.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endSkipBidsReturnMem I outCat outVat outBids))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
      (x4 := (⟨0⟩ : UInt256)) (x5 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSkipAfterBidsCursor] using rd)
  have rd3772' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3772⟩
        [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
          endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
          endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
          endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
          endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
          endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipSuck1CallMem world.2 I outCat outVat outBids) aw3772 outBids
        world k3772 C3772 := by
    simpa [hstack3692, hmemGen] using rd3772
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask))) =
        UInt256.ofNat 0 := by
    rw [hvatTarget, hvatNoCode]
    native_decide
  obtain ⟨aw3813, k3813, C3813, rd3813⟩ :=
    endRuntimeBlocks.endRuntime_block_3772_fallthrough_packed
      (x0 := (⟨128⟩ : UInt256))
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x2 := endSkipBidsTabWord outBids) (x3 := addrMask)
      (x4 := (⟨128⟩ : UInt256)) (x5 := endSkipBidsUsrWord outBids)
      (x6 := (⟨0⟩ : UInt256)) (x7 := (⟨0⟩ : UInt256))
      (R := [endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond rd3772'
  exact endRuntimeBlocks.endRuntime_block_3813
    (R := endRuntimeBlocks.endRuntime_block_3772_fallthrough_stack (σ := world.2)
      (x0 := (⟨128⟩ : UInt256))
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x2 := endSkipBidsTabWord outBids) (x3 := addrMask)
      (x4 := (⟨128⟩ : UInt256)) (x5 := endSkipBidsUsrWord outBids)
      (R := [endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_3772_fallthrough_stack])
    rd3813

theorem endX_skip_after_bids_to_suck1_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3692⟩
      (endSkipAfterBidsCursor I sel aw outCat outVat outBids world).stack
      (endSkipBidsReturnMem I outCat outVat outBids) (endSkipAfterBidsAw aw)
      outBids world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3819⟩
      (endSkipSuck1CallStack world.2 I outCat outVat outBids sel)
      (endSkipSuck1CallMem world.2 I outCat outVat outBids) aw' outBids world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSkipBidsReturnMem_mload64 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hbid := endSkipBidsReturnMem_mload128 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hbidAt :
      memLoad (⟨128⟩ : UInt256) (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsBidWord outBids := by
    simpa [show (⟨128⟩ : UInt256) = UInt256.ofNat 128 from by native_decide] using hbid
  have hlot := endSkipBidsReturnMem_mload160 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have husr := endSkipBidsReturnMem_mload288 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have htab := endSkipBidsReturnMem_mload352 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hlotAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsLotWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 32 =
        UInt256.ofNat 160 from by native_decide] using hlot
  have husrAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 160)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsUsrWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 160 =
        UInt256.ofNat 288 from by native_decide] using husr
  have htabAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 224)
          (endSkipBidsReturnMem I outCat outVat outBids) =
        endSkipBidsTabWord outBids := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 224 =
        UInt256.ofNat 352 from by native_decide] using htab
  have hmemGen := endSkipSuck1CallMem_generated world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hcall64 := endSkipSuck1CallMem_mload64 world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hstack3692 :
      endRuntimeBlocks.endRuntime_block_3692_stack
          (ee := I) (mem := endSkipBidsReturnMem I outCat outVat outBids)
          (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64)
            (endSkipBidsReturnMem I outCat outVat outBids))
          (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
          (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
            endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
          endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
          endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
          endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
          endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
          endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_3692_stack]
    change
      [memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids),
        storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 224)
          (endSkipBidsReturnMem I outCat outVat outBids),
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3692_memory
            (ee := I) (mem := endSkipBidsReturnMem I outCat outVat outBids)
            (σ := world.2)
            (x1 := memLoad (UInt256.ofNat 64)
              (endSkipBidsReturnMem I outCat outVat outBids))),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 160)
          (endSkipBidsReturnMem I outCat outVat outBids),
        ⟨0⟩, ⟨0⟩,
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids) +
            UInt256.ofNat 32)
          (endSkipBidsReturnMem I outCat outVat outBids),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat outBids))
          (endSkipBidsReturnMem I outCat outVat outBids),
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
        endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, htabAt, husrAt, hlotAt, hbidAt]
  obtain ⟨aw3772, k3772, C3772, rd3772⟩ :=
    endRuntimeBlocks.endRuntime_block_3692_packed
      (x0 := UInt256.ofNat outBids.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endSkipBidsReturnMem I outCat outVat outBids))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
      (x4 := (⟨0⟩ : UInt256)) (x5 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSkipAfterBidsCursor] using rd)
  have rd3772' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3772⟩
        [⟨128⟩, storageRead I.codeOwner world.2 (UInt256.ofNat 1),
          endSkipBidsTabWord outBids, addrMask, ⟨128⟩,
          endSkipBidsUsrWord outBids, ⟨0⟩, ⟨0⟩,
          endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
          endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
          endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipSuck1CallMem world.2 I outCat outVat outBids) aw3772 outBids
        world k3772 C3772 := by
    simpa [hstack3692, hmemGen] using rd3772
  have htargetCode :
      extCodeSizeWord world.2
          (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask) ≠
        UInt256.ofNat 0 := by
    rwa [hvatTarget]
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne htargetCode]
    native_decide
  obtain ⟨aw3817, k3817, C3817, rd3817⟩ :=
    endRuntimeBlocks.endRuntime_block_3772_taken_packed
      (x0 := (⟨128⟩ : UInt256))
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x2 := endSkipBidsTabWord outBids) (x3 := addrMask)
      (x4 := (⟨128⟩ : UInt256)) (x5 := endSkipBidsUsrWord outBids)
      (x6 := (⟨0⟩ : UInt256)) (x7 := (⟨0⟩ : UInt256))
      (R := [endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd3772'
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 100 = ⟨100⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 100 = ⟨228⟩ := by
    native_decide
  have rd3817' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3817⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipSuck1CallStack world.2 I outCat outVat outBids sel)
        (endSkipSuck1CallMem world.2 I outCat outVat outBids) aw3817 outBids
        world k3817 C3817 := by
    simpa [endRuntimeBlocks.endRuntime_block_3772_taken_stack,
      endSkipSuck1CallStack, endSkipSuck1CallRest, hvatTarget, hlen, hend,
      endSkipSuckSelectorWord] using rd3817
  have rd3819 := endRuntimeBlocks.endRuntime_block_3817
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSkipSuck1CallStack world.2 I outCat outVat outBids sel)
    (by simp [endSkipSuck1CallStack, endSkipSuck1CallRest]) rd3817'
  exact ⟨aw3817, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3817_stack] using rd3819⟩

set_option maxHeartbeats 12000000 in
theorem endSkipSuck1ExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outCat outVat outBids k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipSuck1CallCursor world I sel aw outCat outVat outBids rdata)
      k C (endSkipAfterTabFrame I outCat outVat outBids) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1" ]
      (sequenceExit ⟨3837⟩
        (fun cur frame e =>
          frame = endSkipAfterSuck1Frame I outCat outVat outBids ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSkipAfterSuck1Stack world.2 I outCat outVat outBids sel ∧
          cur.mem = endSkipSuck1CallMem world.2 I outCat outVat outBids ∧
          cur.aw = endSkipSuck1CallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨3819⟩ = some (.GAS, .none); decide)
    (by simp [endSkipSuck1CallCursor, endSkipSuck1CallStack, endSkipSuck1CallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      endSkipTabValue outBids])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨3820⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipSuck1CallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skipAfterTab evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endPackVatTarget world.2 I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    rw [h.env] at hload
    rw [endEvalSkipSuck1ArgsAfterTab evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok
      [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        endSkipTabValue outBids] =
      EvalResult.ok
        [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          endSkipTabValue outBids]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 4)) solcAddrMask]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_suck_skip1 world.2 I outBids]
    change some (endSkipSuck1EncodedCall world.2 I outBids) =
      some ((endSkipSuck1CallMem world.2 I outCat outVat outBids).readWithPadding 128 100)
    rw [endSkipSuck1CallMem_readCallData world.2 I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_suck out]
    intro rd hrel
    have rd3821 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
          ((⟨1⟩ : UInt256) :: endSkipSuck1CallRest world.2 I outCat outVat outBids sel)
          (endSkipSuck1CallMem world.2 I outCat outVat outBids)
          (endSkipSuck1CallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipSuck1CallCursor,
        endSkipSuck1CallStack, endSkipSuck1CallRest, endSkipSuck1CallAw] using rd
    have rd3837 := endRuntimeBlocks.endRuntime_block_3821_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSkipSuck1CallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipSuck1CallRest]) (by native_decide) (by jump_dest) rd3821
    refine ⟨.ok (endSkipAfterSuck1Frame I outCat outVat outBids) evm',
      Endpoint.reached (endSkipAfterSuck1Cursor world.2 I sel aw outCat outVat outBids out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSkipAfterSuck1Cursor, endSkipAfterSuck1Stack, endSkipSuck1CallAw,
          endRuntimeBlocks.endRuntime_block_3821_taken_stack] using rd3837⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd3821 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
          ((⟨0⟩ : UInt256) :: endSkipSuck1CallRest world.2 I outCat outVat outBids sel)
          (endSkipSuck1CallMem world.2 I outCat outVat outBids)
          (endSkipSuck1CallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipSuck1CallCursor,
        endSkipSuck1CallStack, endSkipSuck1CallRest, endSkipSuck1CallAw] using rd
    have rd3828 := endRuntimeBlocks.endRuntime_block_3821_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipSuck1CallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipSuck1CallRest]) (by native_decide) rd3821
    exact endRuntimeBlocks.endRuntime_block_3828
      (R := endRuntimeBlocks.endRuntime_block_3821_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipSuck1CallRest world.2 I outCat outVat outBids sel))
      (by simp [endRuntimeBlocks.endRuntime_block_3821_fallthrough_stack,
        endSkipSuck1CallRest])
      rd3828

abbrev endSkipAfterSuck1Rel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outCat : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preσ outVat outBids awSuck1,
      frame = endSkipAfterSuck1Frame I outCat outVat outBids ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outBids.size < UInt256.size ∧
      256 ≤ outBids.size ∧
      cur.stack = endSkipAfterSuck1Stack preσ I outCat outVat outBids sel ∧
      cur.mem = endSkipSuck1CallMem preσ I outCat outVat outBids ∧
      cur.aw = endSkipSuck1CallAw awSuck1

set_option maxHeartbeats 12000000 in
theorem endSkipAfterBidsToSuck1Refines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3692⟩
      (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      ([ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1")
      (sequenceExit ⟨3837⟩
        (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨outVat, awBids, hframe, hrel, houtVat, h160, houtBids, h256,
      hstack, hmem, haw⟩
  cases hframe
  have rd3692 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3692⟩
        [UInt256.ofNat cur0.rdata.size,
          memLoad (UInt256.ofNat 64) (endSkipBidsReturnMem I outCat outVat cur0.rdata),
          ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipBidsReturnMem I outCat outVat cur0.rdata) (endSkipAfterBidsAw awBids)
        cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsourceLets :
      ExecBlock config (endSkipAfterBidsFrame I outCat outVat cur0.rdata) evm
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ]
        (.ok (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm) :=
    ExecBlock.consNormal (endLetSkipBid evm I outCat outVat cur0.rdata)
      (ExecBlock.consNormal (endLetSkipLot evm I outCat outVat cur0.rdata)
        (ExecBlock.consNormal (endLetSkipUsr evm I outCat outVat cur0.rdata)
          (ExecBlock.consNormal (endLetSkipTab evm I outCat outVat cur0.rdata)
            ExecBlock.nil)))
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) := by
    have htarget :
        UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur0.world.2 I := by
      have hload := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
      rw [hrel.env] at hload
      rw [hrel.env]
      rw [hload]
      rw [u256_land_comm
        (storageRead I.codeOwner cur0.world.2 (UInt256.ofNat 1)) solcAddrMask]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endPackVatTarget cur0.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hsourceChecked :
        ExecBlock config (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck1")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skipAfterTab_false evm I outCat outVat
              cur0.rdata hsrcNoCode)))
    have hsourceFull :
        ExecBlock config (endSkipAfterBidsFrame I outCat outVat cur0.rdata) evm
          ([ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
              .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
              .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
              .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
            checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
              [vowAddr, vowAddr, .var "tab"] "_suck1")
          .reverted :=
      Reasoning.Theory.execBlock_append hsourceLets hsourceChecked
    have hrev := endX_skip_vat_no_code_after_bids
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := awBids) (outCat := outCat)
      (outVat := outVat) (outBids := cur0.rdata) (k := k) (C := C)
      (world := cur0.world)
      houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd3692
    exact ⟨.reverted, .reverted, hsourceFull, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skipAfterTab_true evm I outCat outVat cur0.rdata
            hsrcCode))
        ExecBlock.nil
    obtain ⟨aw3819, k3819, C3819, rd3819⟩ :=
      endX_skip_after_bids_to_suck1_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awBids) (outCat := outCat)
        (outVat := outVat) (outBids := cur0.rdata) (k := k) (C := C)
        (world := cur0.world)
        houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd3692
    have htailExact :=
      (endSkipSuck1ExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw3819) (rdata := cur0.rdata)
        (outCat := outCat) (outVat := outVat) (outBids := cur0.rdata)
        (k := k3819) (C := C3819) (evm := evm) (world := cur0.world)
        hperm houtCat h96 houtVat h160 houtBids h256)
        (by simpa [endSkipSuck1CallCursor] using rd3819) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm
          [ .externalCall (.storage vatRef) "suck" (.intLit 0)
              [vowAddr, vowAddr, .var "tab"] "_suck1" ]
          (sequenceExit ⟨3837⟩
            (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, cur0.world.2, outVat, cur0.rdata, aw3819,
                hframeQ, hrelQ, houtVat, h160, houtBids, h256, hstackQ, hmemQ, hawQ⟩
          | returned worldOut outOut =>
              exact hQ
          | reverted =>
              exact hQ
      | returned frameOut evmOut ret =>
          exact hQ
      | «break» frameOut evmOut =>
          exact hQ
      | «continue» frameOut evmOut =>
          exact hQ
      | reverted =>
          exact hQ
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterTabFrame I outCat outVat cur0.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck1")
          (sequenceExit ⟨3837⟩
            (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa using BlockProgress.prepend hsourceLets hcheckedProgress

def endSkipSuck2PayloadBytes (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) : List UInt8 :=
  (EVM.Word.toBytesBE (endPackVowTarget σ I) ++
    EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) ++
    EVM.Word.toBytesBE (endSkipBidsBidWord outBids)

def endSkipSuck2EncodedCall (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) : ByteArray :=
  suckSelector ++ ⟨(endSkipSuck2PayloadBytes σ I outBids).toArray⟩

abbrev endSkipSuck2MemSel (preσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  endSkipSuckSelectorEncodedWord.toByteArray.write 0
    (endSkipSuck1CallMem preσ I outCat outVat outBids) 128 32

abbrev endSkipSuck2MemVow (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endPackVowTarget postσ I).toByteArray.write 0
    (endSkipSuck2MemSel preσ I outCat outVat outBids) 132 32

abbrev endSkipSuck2MemThis (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids) 164 32

abbrev endSkipSuck2CallMem (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endSkipBidsBidWord outBids).toByteArray.write 0
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids) 196 32

abbrev endSkipSuck2CallRest (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨228⟩, endSkipSuckSelectorWord, endPackVatTarget σ I,
    endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
    endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
    endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
    endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipSuck2CallStack (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [endPackVatTarget postσ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩] ++
    endSkipSuck2CallRest postσ I outCat outVat outBids sel

abbrev endSkipSuck2CallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (outCat outVat outBids rdata : ByteArray) : Cursor :=
  { pc := ⟨3938⟩,
    stack := endSkipSuck2CallStack preσ world.2 I outCat outVat outBids sel,
    mem := endSkipSuck2CallMem preσ world.2 I outCat outVat outBids,
    aw := aw, rdata := rdata, world := world }

abbrev endSkipSuck2CallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨100⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSkipAfterSuck2Frame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns []) }

abbrev endSkipAfterSuck2Stack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSkipSuck2CallRest σ I outCat outVat outBids sel

abbrev endSkipAfterSuck2Cursor (preσ postσ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outCat outVat outBids out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨3956⟩,
    stack := endSkipAfterSuck2Stack postσ I outCat outVat outBids sel,
    mem := endSkipSuck2CallMem preσ postσ I outCat outVat outBids,
    aw := endSkipSuck2CallAw aw, rdata := out, world := world }

theorem endSkipAfterSuck1Frame_get_bid (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterSuck1Frame I outCat outVat outBids).locals.get? "bid" =
      some (endSkipBidValue outBids) := by
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "bid") = some (endSkipBidValue outBids)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "bid") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "bid") = some (endSkipBidValue outBids)
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "bid")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "bid") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "bid") = some (endSkipBidValue outBids)
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "bid") (endSkipLotValue outBids) (by decide)]
  exact store_get_self (endSkipAfterBidsFrame I outCat outVat outBids).locals
    "bid" (endSkipBidValue outBids)

theorem endEvalSkipBidAfterSuck1 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm (.var "bid") =
      .ok (endSkipBidValue outBids) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterSuck1Frame_get_bid I outCat outVat outBids

theorem endSkipAfterSuck1Frame_get_vat_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterSuck1Frame I outCat outVat outBids).locals.get? "vat" = none := by
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "vat") (collapseReturns []) (by decide)]
  exact endSkipAfterTabFrame_get_vat_none I outCat outVat outBids

theorem endSkipAfterSuck1Frame_get_vow_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterSuck1Frame I outCat outVat outBids).locals.get? "vow" = none := by
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "vow") (collapseReturns []) (by decide)]
  exact endSkipAfterTabFrame_get_vow_none I outCat outVat outBids

theorem endEvalVatAddress_skipAfterSuck1 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterSuck1Frame I outCat outVat outBids).locals) (evm := evm)
    (slot := vatRef) (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSkipAfterSuck1Frame_get_vat_none I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVowAddress_skipAfterSuck1 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterSuck1Frame I outCat outVat outBids).locals) (evm := evm)
    (slot := vowRef) (er := { base := "vow", steps := [] }) (wordSlot := UInt256.ofNat 4)
    (endSkipAfterSuck1Frame_get_vow_none I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vow)

theorem endEvalVatCodeGuard_skipAfterSuck1_false (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterSuck1Frame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterSuck1 evm I outCat outVat outBids) hnocode

theorem endEvalVatCodeGuard_skipAfterSuck1_true (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterSuck1Frame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterSuck1 evm I outCat outVat outBids) hcode

theorem endEvalSkipSuck2ArgsAfterSuck1 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExprs? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
      [vowAddr, thisAddr, .var "bid"] =
      .ok [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        .address evm.executionEnv.codeOwner,
        endSkipBidValue outBids] := by
  rw [evalExprs?]
  rw [endEvalVowAddress_skipAfterSuck1 evm I outCat outVat outBids]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  have hthis :
      evalExpr? config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
        thisAddr = .ok (.address evm.executionEnv.codeOwner) := by
    simp [evalExpr?, thisAddr, envValue, pure]
  rw [hthis]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSkipBidAfterSuck1 evm I outCat outVat outBids]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endSkipSuck2MemSel_size (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2MemSel preσ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck1CallMem preσ I outCat outVat outBids)
    endSkipSuckSelectorEncodedWord 128 384 384
    (endSkipSuck1CallMem_size preσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck1CallMem_size preσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck2MemVow_size (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck2MemSel preσ I outCat outVat outBids) (endPackVowTarget postσ I)
    132 384 384
    (endSkipSuck2MemSel_size preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck2MemSel_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck2MemThis_size (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids)
    (UInt256.ofNat I.codeOwner.val) 164 384 384
    (endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck2CallMem_size (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids)
    (endSkipBidsBidWord outBids) 196 384 384
    (endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipSuck2CallMem_read64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsBidWord outBids)
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids) 196 64
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids) 164 64
    (by
      rw [endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipSuck2MemSel preσ I outCat outVat outBids) 132 64
    (by
      rw [endSkipSuck2MemSel_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSkipSuckSelectorEncodedWord
    (endSkipSuck1CallMem preσ I outCat outVat outBids) 128 64
    (by
      rw [endSkipSuck1CallMem_size preσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  exact endSkipSuck1CallMem_read64 preσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256

theorem endSkipSuck2CallMem_mload64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64) (endSkipSuck2CallMem preσ postσ I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endSkipSuck2CallMem preσ postσ I outCat outVat outBids)
    (by
      rw [endSkipSuck2CallMem_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (endSkipSuck2CallMem_read64 preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

theorem endSkipSuck2CallMem_readSelector (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 128 4 =
      suckSelector := by
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipSuck2MemSel_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipSuck2MemSel_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  change ((endSkipSuckSelectorEncodedWord.toByteArray.write 0
      (endSkipSuck1CallMem preσ I outCat outVat outBids) 128 32).readWithPadding
      128 4) = suckSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipSuckSelectorEncodedWord (endSkipSuck1CallMem preσ I outCat outVat outBids)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipSuckSelectorEncodedWord_prefix]

theorem endSkipSuck2CallMem_readVow (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 132 32 =
      (endPackVowTarget postσ I).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsBidWord outBids)
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids) 196 132
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids) 164 132
    (by
      rw [endSkipSuck2MemVow_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  change ((endPackVowTarget postσ I).toByteArray.write 0
      (endSkipSuck2MemSel preσ I outCat outVat outBids) 132 32).readWithPadding
      132 32 = (endPackVowTarget postσ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipSuck2MemSel preσ I outCat outVat outBids) 132

theorem endSkipSuck2CallMem_readThis (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 164 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsBidWord outBids)
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids) 196 164
    (by
      rw [endSkipSuck2MemThis_size preσ postσ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  change ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (endSkipSuck2MemVow preσ postσ I outCat outVat outBids) 164 32).readWithPadding
      164 32 = (UInt256.ofNat I.codeOwner.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipSuck2MemVow preσ postσ I outCat outVat outBids) 164

theorem endSkipSuck2CallMem_readBid (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 196 32 =
      (endSkipBidsBidWord outBids).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endSkipBidsBidWord outBids)
    (endSkipSuck2MemThis preσ postσ I outCat outVat outBids) 196

theorem endSkipSuck2CallMem_readCallData (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).readWithPadding 128 100 =
      endSkipSuck2EncodedCall postσ I outBids := by
  have hsize : 228 ≤ (endSkipSuck2CallMem preσ postσ I outCat outVat outBids).size := by
    rw [endSkipSuck2CallMem_size preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  rw [show 100 = 4 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids) 128 4 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids) 132 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipSuck2CallMem preσ postσ I outCat outVat outBids) 164 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [endSkipSuck2CallMem_readSelector preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck2CallMem_readVow preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck2CallMem_readThis preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipSuck2CallMem_readBid preσ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_eq_toBytesBE (endPackVowTarget postσ I)]
  rw [toByteArray_eq_toBytesBE (UInt256.ofNat I.codeOwner.val)]
  rw [toByteArray_eq_toBytesBE (endSkipBidsBidWord outBids)]
  simp only [endSkipSuck2EncodedCall, endSkipSuck2PayloadBytes]
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem endEncodeUint_skipBid (outBids : ByteArray) :
    encodeABIValue? uint256 (endSkipBidValue outBids) =
      some (EVM.Word.toBytesBE (endSkipBidsBidWord outBids)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (endSkipBidValue outBids)
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endSkipBidsBidWord outBids))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

theorem endEncodeABIValues_suck_skip2 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    encodeABIValues? [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address I.codeOwner,
        endSkipBidValue outBids] =
      some (endSkipSuck2PayloadBytes σ I outBids) := by
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_this_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeUint_skipBid outBids, hdynUint]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSkipSuck2PayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_suck_skip2 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address I.codeOwner,
        endSkipBidValue outBids] =
      some (endSkipSuck2EncodedCall σ I outBids) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_suck_skip2 σ I outBids]
  simp [endSkipSuck2EncodedCall, endSkipSuck2PayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_suck_skip2 (σ : AccountMap) (I : ExecutionEnv)
    (outBids : ByteArray) :
    config.externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address I.codeOwner,
        endSkipBidValue outBids] =
      some (endSkipSuck2EncodedCall σ I outBids) := by
  rw [endExternalEncode_suck_branch]
  exact endEncodeCallWithSelector_suck_skip2 σ I outBids

theorem endSkipSuck2CallMem_generated (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    endRuntimeBlocks.endRuntime_block_3837_memory (ee := I)
        (mem := endSkipSuck1CallMem preσ I outCat outVat outBids) (σ := postσ)
        (x7 := endSkipBidsBidWord outBids) =
      endSkipSuck2CallMem preσ postσ I outCat outVat outBids := by
  have hfree := endSkipSuck1CallMem_mload64 preσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endRuntimeBlocks.endRuntime_block_3837_memory
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [hmask]

theorem endX_skip_vat_no_code_after_suck1 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3837⟩
      (endSkipAfterSuck1Stack preσ I outCat outVat outBids sel)
      (endSkipSuck1CallMem preσ I outCat outVat outBids) (endSkipSuck1CallAw aw)
      rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSkipSuck1CallMem_mload64 preσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmemGen := endSkipSuck2CallMem_generated preσ world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hcall64 := endSkipSuck2CallMem_mload64 preσ world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hdelta :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 100 = ⟨100⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 100 = ⟨228⟩ := by
    native_decide
  have hstack3837 :
      endRuntimeBlocks.endRuntime_block_3837_stack
          (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
          (σ := world.2)
          (x4 := endSkipBidsTabWord outBids)
          (x5 := endSkipBidsUsrWord outBids)
          (x6 := endSkipBidsLotWord outBids)
          (x7 := endSkipBidsBidWord outBids)
          (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
            endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
          endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_3837_stack]
    change
      [UInt256.sub
            (memLoad (UInt256.ofNat 64)
              (endSkipSuck1CallMem preσ I outCat outVat outBids))
            (memLoad (UInt256.ofNat 64)
              (endRuntimeBlocks.endRuntime_block_3837_memory
                (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
                (σ := world.2) (x7 := endSkipBidsBidWord outBids))) +
          UInt256.ofNat 100,
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3837_memory
            (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
            (σ := world.2) (x7 := endSkipBidsBidWord outBids)),
        ⟨0⟩,
        memLoad (UInt256.ofNat 64)
            (endSkipSuck1CallMem preσ I outCat outVat outBids) +
          UInt256.ofNat 100,
        endSkipSuckSelectorWord,
        UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask,
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
        endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, hdelta, hend, hvatTarget]
  obtain ⟨aw3920, k3920, C3920, rd3920⟩ :=
    endRuntimeBlocks.endRuntime_block_3837_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨228⟩)
      (x2 := endSkipSuckSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp [endSkipSuck1CallRest])
      (by simpa [endSkipAfterSuck1Stack, endSkipSuck1CallRest] using rd)
  have rd3920' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3920⟩
        [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
          endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids) aw3920 rdata
        world k3920 C3920 := by
    simpa [hstack3837, hmemGen] using rd3920
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hvatNoCode]
    native_decide
  obtain ⟨aw3932, k3932, C3932, rd3932⟩ :=
    endRuntimeBlocks.endRuntime_block_3920_fallthrough_packed
      (x0 := (⟨100⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨228⟩ : UInt256))
      (x4 := endSkipSuckSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := [endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond rd3920'
  exact endRuntimeBlocks.endRuntime_block_3932
    (R := endRuntimeBlocks.endRuntime_block_3920_fallthrough_stack (σ := world.2)
      (x0 := (⟨100⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨228⟩ : UInt256))
      (x4 := endSkipSuckSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := [endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_3920_fallthrough_stack,
      endSkipSuck2CallRest])
    rd3932

theorem endX_skip_after_suck1_to_suck2_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3837⟩
      (endSkipAfterSuck1Stack preσ I outCat outVat outBids sel)
      (endSkipSuck1CallMem preσ I outCat outVat outBids) (endSkipSuck1CallAw aw)
      rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3938⟩
      (endSkipSuck2CallStack preσ world.2 I outCat outVat outBids sel)
      (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids) aw' rdata
      world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSkipSuck1CallMem_mload64 preσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmemGen := endSkipSuck2CallMem_generated preσ world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hcall64 := endSkipSuck2CallMem_mload64 preσ world.2 I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hdelta :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 100 = ⟨100⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 100 = ⟨228⟩ := by
    native_decide
  have hstack3837 :
      endRuntimeBlocks.endRuntime_block_3837_stack
          (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
          (σ := world.2)
          (x4 := endSkipBidsTabWord outBids)
          (x5 := endSkipBidsUsrWord outBids)
          (x6 := endSkipBidsLotWord outBids)
          (x7 := endSkipBidsBidWord outBids)
          (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
            endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
          endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_3837_stack]
    change
      [UInt256.sub
            (memLoad (UInt256.ofNat 64)
              (endSkipSuck1CallMem preσ I outCat outVat outBids))
            (memLoad (UInt256.ofNat 64)
              (endRuntimeBlocks.endRuntime_block_3837_memory
                (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
                (σ := world.2) (x7 := endSkipBidsBidWord outBids))) +
          UInt256.ofNat 100,
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3837_memory
            (ee := I) (mem := endSkipSuck1CallMem preσ I outCat outVat outBids)
            (σ := world.2) (x7 := endSkipBidsBidWord outBids)),
        ⟨0⟩,
        memLoad (UInt256.ofNat 64)
            (endSkipSuck1CallMem preσ I outCat outVat outBids) +
          UInt256.ofNat 100,
        endSkipSuckSelectorWord,
        UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask,
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
        endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, hdelta, hend, hvatTarget]
  obtain ⟨aw3920, k3920, C3920, rd3920⟩ :=
    endRuntimeBlocks.endRuntime_block_3837_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨228⟩)
      (x2 := endSkipSuckSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (R := [endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp [endSkipSuck1CallRest])
      (by simpa [endSkipAfterSuck1Stack, endSkipSuck1CallRest] using rd)
  have rd3920' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3920⟩
        [⟨100⟩, ⟨128⟩, ⟨0⟩, ⟨228⟩, endSkipSuckSelectorWord,
          endPackVatTarget world.2 I, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids) aw3920 rdata
        world k3920 C3920 := by
    simpa [hstack3837, hmemGen] using rd3920
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw3936, k3936, C3936, rd3936⟩ :=
    endRuntimeBlocks.endRuntime_block_3920_taken_packed
      (x0 := (⟨100⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨228⟩ : UInt256))
      (x4 := endSkipSuckSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := [endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd3920'
  have rd3936' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3936⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipSuck2CallStack preσ world.2 I outCat outVat outBids sel)
        (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids) aw3936 rdata
        world k3936 C3936 := by
    simpa [endRuntimeBlocks.endRuntime_block_3920_taken_stack,
      endSkipSuck2CallStack, endSkipSuck2CallRest] using rd3936
  have rd3938 := endRuntimeBlocks.endRuntime_block_3936
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSkipSuck2CallStack preσ world.2 I outCat outVat outBids sel)
    (by simp [endSkipSuck2CallStack, endSkipSuck2CallRest]) rd3936'
  exact ⟨aw3936, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3936_stack] using rd3938⟩

set_option maxHeartbeats 12000000 in
theorem endSkipSuck2ExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outCat outVat outBids k C evm}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipSuck2CallCursor world preσ I sel aw outCat outVat outBids rdata)
      k C (endSkipAfterSuck1Frame I outCat outVat outBids) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, thisAddr, .var "bid"] "_suck2" ]
      (sequenceExit ⟨3956⟩
        (fun cur frame e =>
          frame = endSkipAfterSuck2Frame I outCat outVat outBids ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSkipAfterSuck2Stack world.2 I outCat outVat outBids sel ∧
          cur.mem = endSkipSuck2CallMem preσ world.2 I outCat outVat outBids ∧
          cur.aw = endSkipSuck2CallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨3938⟩ = some (.GAS, .none); decide)
    (by simp [endSkipSuck2CallCursor, endSkipSuck2CallStack, endSkipSuck2CallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .address I.codeOwner, endSkipBidValue outBids])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨3939⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipSuck2CallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skipAfterSuck1 evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endPackVatTarget world.2 I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    rw [h.env] at hload
    rw [endEvalSkipSuck2ArgsAfterSuck1 evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok
      [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        .address I.codeOwner,
        endSkipBidValue outBids] =
      EvalResult.ok
        [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          .address I.codeOwner,
          endSkipBidValue outBids]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 4)) solcAddrMask]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_suck_skip2 world.2 I outBids]
    change some (endSkipSuck2EncodedCall world.2 I outBids) =
      some ((endSkipSuck2CallMem preσ world.2 I outCat outVat outBids).readWithPadding
        128 100)
    rw [endSkipSuck2CallMem_readCallData preσ world.2 I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_suck out]
    intro rd hrel
    have rd3940 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
          ((⟨1⟩ : UInt256) :: endSkipSuck2CallRest world.2 I outCat outVat outBids sel)
          (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids)
          (endSkipSuck2CallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipSuck2CallCursor,
        endSkipSuck2CallStack, endSkipSuck2CallRest, endSkipSuck2CallAw] using rd
    have rd3956 := endRuntimeBlocks.endRuntime_block_3940_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSkipSuck2CallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipSuck2CallRest]) (by native_decide) (by jump_dest) rd3940
    refine ⟨.ok (endSkipAfterSuck2Frame I outCat outVat outBids) evm',
      Endpoint.reached
        (endSkipAfterSuck2Cursor preσ world.2 I sel aw outCat outVat outBids out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSkipAfterSuck2Cursor, endSkipAfterSuck2Stack, endSkipSuck2CallAw,
          endRuntimeBlocks.endRuntime_block_3940_taken_stack] using rd3956⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd3940 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
          ((⟨0⟩ : UInt256) :: endSkipSuck2CallRest world.2 I outCat outVat outBids sel)
          (endSkipSuck2CallMem preσ world.2 I outCat outVat outBids)
          (endSkipSuck2CallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipSuck2CallCursor,
        endSkipSuck2CallStack, endSkipSuck2CallRest, endSkipSuck2CallAw] using rd
    have rd3947 := endRuntimeBlocks.endRuntime_block_3940_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipSuck2CallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipSuck2CallRest]) (by native_decide) rd3940
    exact endRuntimeBlocks.endRuntime_block_3947
      (R := endRuntimeBlocks.endRuntime_block_3940_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipSuck2CallRest world.2 I outCat outVat outBids sel))
      (by simp [endRuntimeBlocks.endRuntime_block_3940_fallthrough_stack,
        endSkipSuck2CallRest])
      rd3947

abbrev endSkipAfterSuck2Rel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outCat : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preSuck1σ preSuck2σ outVat outBids awSuck2,
      frame = endSkipAfterSuck2Frame I outCat outVat outBids ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outBids.size < UInt256.size ∧
      256 ≤ outBids.size ∧
      cur.stack = endSkipAfterSuck2Stack preSuck2σ I outCat outVat outBids sel ∧
      cur.mem = endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
      cur.aw = endSkipSuck2CallAw awSuck2

set_option maxHeartbeats 12000000 in
theorem endSkipAfterSuck1ToSuck2Refines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3837⟩
      (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, thisAddr, .var "bid"] "_suck2")
      (sequenceExit ⟨3956⟩
        (endSkipAfterSuck2Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨preσ, outVat, outBids, awSuck1, hframe, hrel, houtVat, h160, houtBids, h256,
      hstack, hmem, haw⟩
  cases hframe
  have rd3837 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3837⟩
        (endSkipAfterSuck1Stack preσ I outCat outVat outBids sel)
        (endSkipSuck1CallMem preσ I outCat outVat outBids)
        (endSkipSuck1CallAw awSuck1) cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) := by
    have htarget :
        UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur0.world.2 I := by
      have hload := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
      rw [hrel.env] at hload
      rw [hrel.env]
      rw [hload]
      rw [u256_land_comm
        (storageRead I.codeOwner cur0.world.2 (UInt256.ofNat 1)) solcAddrMask]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endPackVatTarget cur0.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hsourceChecked :
        ExecBlock config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
          (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, thisAddr, .var "bid"] "_suck2")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skipAfterSuck1_false evm I outCat outVat
              outBids hsrcNoCode)))
    have hrev := endX_skip_vat_no_code_after_suck1
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := awSuck1) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
      (k := k) (C := C) (preσ := preσ) (world := cur0.world)
      houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd3837
    exact ⟨.reverted, .reverted, hsourceChecked, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkipAfterSuck1Frame I outCat outVat outBids) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkipAfterSuck1Frame I outCat outVat outBids) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skipAfterSuck1_true evm I outCat outVat outBids
            hsrcCode))
        ExecBlock.nil
    obtain ⟨aw3938, k3938, C3938, rd3938⟩ :=
      endX_skip_after_suck1_to_suck2_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awSuck1) (outCat := outCat)
        (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
        (k := k) (C := C) (preσ := preσ) (world := cur0.world)
        houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd3837
    have htailExact :=
      (endSkipSuck2ExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw3938) (rdata := cur0.rdata)
        (outCat := outCat) (outVat := outVat) (outBids := outBids)
        (k := k3938) (C := C3938) (evm := evm) (preσ := preσ)
        (world := cur0.world) hperm houtCat h96 houtVat h160 houtBids h256)
        (by simpa [endSkipSuck2CallCursor] using rd3938) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterSuck1Frame I outCat outVat outBids) evm
          [ .externalCall (.storage vatRef) "suck" (.intLit 0)
              [vowAddr, thisAddr, .var "bid"] "_suck2" ]
          (sequenceExit ⟨3956⟩
            (endSkipAfterSuck2Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, preσ, cur0.world.2, outVat, outBids, aw3938,
                hframeQ, hrelQ, houtVat, h160, houtBids, h256, hstackQ, hmemQ, hawQ⟩
          | returned worldOut outOut =>
              exact hQ
          | reverted =>
              exact hQ
      | returned frameOut evmOut ret =>
          exact hQ
      | «break» frameOut evmOut =>
          exact hQ
      | «continue» frameOut evmOut =>
          exact hQ
      | reverted =>
          exact hQ
    simpa [checkedExternalCallStmts] using
      BlockProgress.prepend hsourceRequire htailProgress

abbrev endSkipHopeSelectorWord : UInt256 :=
  UInt256.ofNat 2746363844

abbrev endSkipHopeSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)

def endSkipHopePayloadBytes (outCat : ByteArray) : List UInt8 :=
  EVM.Word.toBytesBE (endSkipFlipTarget outCat)

def endSkipHopeEncodedCall (outCat : ByteArray) : ByteArray :=
  hopeSelector ++ ⟨(endSkipHopePayloadBytes outCat).toArray⟩

abbrev endSkipHopeMemSel (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  endSkipHopeSelectorEncodedWord.toByteArray.write 0
    (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 32

abbrev endSkipHopeCallMem (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endSkipFlipTarget outCat).toByteArray.write 0
    (endSkipHopeMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 32

abbrev endSkipHopeCallRest (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endSkipHopeSelectorWord, endPackVatTarget σ I,
    endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
    endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
    endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
    endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipHopeCallStack (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [endPackVatTarget postσ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨0⟩] ++
    endSkipHopeCallRest postσ I outCat outVat outBids sel

abbrev endSkipHopeCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outCat outVat outBids rdata : ByteArray) : Cursor :=
  { pc := ⟨4040⟩,
    stack := endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat
      outBids sel,
    mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids,
    aw := aw, rdata := rdata, world := world }

abbrev endSkipHopeCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSkipAfterHopeFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns []) }

abbrev endSkipAfterHopeStack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSkipHopeCallRest σ I outCat outVat outBids sel

abbrev endSkipAfterHopeCursor (preSuck1σ preSuck2σ preHopeσ : AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outCat outVat outBids out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨4058⟩,
    stack := endSkipAfterHopeStack preHopeσ I outCat outVat outBids sel,
    mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids,
    aw := endSkipHopeCallAw aw, rdata := out, world := world }

theorem endSkipAfterSuck2Frame_get_flip (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterSuck2Frame I outCat outVat outBids).locals.get? "flip" =
      some (endSkipFlipValue outCat) := by
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "flip") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "flip") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "flip")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "flip") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "flip") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "flip") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "flip") =
    some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "flip") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  exact endSkipAfterRateFrame_get_flip I outCat outVat

theorem endEvalSkipFlipAfterSuck2 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      (.var "flip") =
      .ok (endSkipFlipValue outCat) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterSuck2Frame_get_flip I outCat outVat outBids

theorem endEvalSkipFlipAfterSuck2_masked (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      (.var "flip") =
      .ok (.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)) := by
  rw [endEvalSkipFlipAfterSuck2 evm I outCat outVat outBids]
  simp [endSkipFlipValue, endSkipFlipAddress_eq_mask outCat]

theorem endSkipAfterSuck2Frame_get_vat_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterSuck2Frame I outCat outVat outBids).locals.get? "vat" = none := by
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "vat") (collapseReturns []) (by decide)]
  exact endSkipAfterSuck1Frame_get_vat_none I outCat outVat outBids

theorem endEvalVatAddress_skipAfterSuck2 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterSuck2Frame I outCat outVat outBids).locals) (evm := evm)
    (slot := vatRef) (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSkipAfterSuck2Frame_get_vat_none I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVatCodeGuard_skipAfterSuck2_false (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterSuck2Frame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterSuck2 evm I outCat outVat outBids) hnocode

theorem endEvalVatCodeGuard_skipAfterSuck2_true (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterSuck2Frame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_skipAfterSuck2 evm I outCat outVat outBids) hcode

theorem endEvalSkipHopeArgsAfterSuck2 (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExprs? config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      [.var "flip"] =
      .ok [.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)] := by
  rw [evalExprs?]
  rw [endEvalSkipFlipAfterSuck2_masked evm I outCat outVat outBids]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endSkipHopeSelectorEncodedWord_prefix :
    (endSkipHopeSelectorEncodedWord.toByteArray).extract 0 4 = hopeSelector := by
  native_decide

theorem endSkipHopeMemSel_size (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipHopeMemSel preSuck1σ preSuck2σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    endSkipHopeSelectorEncodedWord 128 384 384
    (endSkipSuck2CallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipSuck2CallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipHopeCallMem_size (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipHopeMemSel preSuck1σ preSuck2σ I outCat outVat outBids)
    (endSkipFlipTarget outCat) 132 384 384
    (endSkipHopeMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipHopeMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipHopeCallMem_read64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipFlipTarget outCat)
    (endSkipHopeMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 64
    (by
      rw [endSkipHopeMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSkipHopeSelectorEncodedWord
    (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 64
    (by
      rw [endSkipSuck2CallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  exact endSkipSuck2CallMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256

theorem endSkipHopeCallMem_mload64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64)
      (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (by
      rw [endSkipHopeCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (endSkipHopeCallMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

theorem endSkipHopeCallMem_readSelector (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      128 4 =
      hopeSelector := by
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipHopeMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipHopeMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  change ((endSkipHopeSelectorEncodedWord.toByteArray.write 0
      (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      128 32).readWithPadding 128 4) = hopeSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipHopeSelectorEncodedWord
    (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipHopeSelectorEncodedWord_prefix]

theorem endSkipHopeCallMem_readFlip (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      132 32 =
      (endSkipFlipTarget outCat).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endSkipFlipTarget outCat)
    (endSkipHopeMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132

theorem endSkipHopeCallMem_readCallData (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      128 36 =
      endSkipHopeEncodedCall outCat := by
  have hsize :
      164 ≤ (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipHopeCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSkipHopeCallMem_readSelector preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipHopeCallMem_readFlip preSuck1σ preSuck2σ I outCat outVat outBids]
  rw [toByteArray_eq_toBytesBE (endSkipFlipTarget outCat)]
  simp only [endSkipHopeEncodedCall, endSkipHopePayloadBytes]

theorem endSkipFlipTarget_canonical (outCat : ByteArray) :
    (endSkipFlipTarget outCat).toNat < EVM.addressModulus := by
  unfold endSkipFlipTarget
  exact solcAddrMask_result_canonical _

theorem endEncodeAddress_skipFlip (outCat : ByteArray) :
    encodeABIValue? addr
      (.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)) =
      some (EVM.Word.toBytesBE (endSkipFlipTarget outCat)) := by
  have hmod :
      (endSkipFlipTarget outCat).toNat % AccountAddress.size =
        (endSkipFlipTarget outCat).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size]
      using endSkipFlipTarget_canonical outCat
  have hword :
      EVM.word (endSkipFlipTarget outCat).toNat = endSkipFlipTarget outCat :=
    u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, hmod, hword]

theorem endEncodeABIValues_hope_skip (outCat : ByteArray) :
    encodeABIValues? [addr]
      [.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)] =
      some (endSkipHopePayloadBytes outCat) := by
  have hhead : abiTupleHeadSize? [addr] = some 32 := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_skipFlip outCat, hdynAddr]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSkipHopePayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_hope_skip (outCat : ByteArray) :
    ABI.encodeCallWithSelector? hopeSelector [addr]
      [.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)] =
      some (endSkipHopeEncodedCall outCat) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_hope_skip outCat]
  simp [endSkipHopeEncodedCall, endSkipHopePayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_hope_branch (args : List Value) :
    config.externalABI.encode? "hope" args =
      ABI.encodeCallWithSelector? hopeSelector [addr] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "hope" = "cage")]
  rw [if_neg (by decide : ¬ "hope" = "vatIlks")]
  rw [if_neg (by decide : ¬ "hope" = "catIlks")]
  rw [if_neg (by decide : ¬ "hope" = "dogIlks")]
  rw [if_neg (by decide : ¬ "hope" = "spotIlks")]
  rw [if_neg (by decide : ¬ "hope" = "urns")]
  rw [if_neg (by decide : ¬ "hope" = "dai")]
  rw [if_neg (by decide : ¬ "hope" = "debt")]
  rw [if_neg (by decide : ¬ "hope" = "move")]
  rw [if_pos (by decide : "hope" = "hope")]

theorem endExternalEncode_hope_skip (outCat : ByteArray) :
    config.externalABI.encode? "hope"
      [.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)] =
      some (endSkipHopeEncodedCall outCat) := by
  rw [endExternalEncode_hope_branch]
  exact endEncodeCallWithSelector_hope_skip outCat

theorem endExternalDecode_hope (out : ByteArray) :
    config.externalABI.decode? "hope" out = some [] := by
  rfl

theorem endSkipHopeCallMem_generated (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    endRuntimeBlocks.endRuntime_block_3956_taken_memory
        (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
        (x9 := endSkipCatIlksFlipWord outCat) =
      endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids := by
  have hfree := endSkipSuck2CallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endRuntimeBlocks.endRuntime_block_3956_taken_memory
  unfold endSkipHopeCallMem endSkipHopeMemSel endSkipFlipTarget
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [hmask]
  rw [u256_land_comm solcAddrMask (endSkipCatIlksFlipWord outCat)]

theorem endX_skip_vat_no_code_after_suck2 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preSuck1σ preSuck2σ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3956⟩
      (endSkipAfterSuck2Stack preSuck2σ I outCat outVat outBids sel)
      (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (endSkipSuck2CallAw aw) rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
                addrMask))) =
        UInt256.ofNat 0 := by
    rw [hvatTarget, hvatNoCode]
    native_decide
  obtain ⟨aw4034, k4034, C4034, rd4034⟩ :=
    endRuntimeBlocks.endRuntime_block_3956_fallthrough_packed
      (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endSkipSuckSelectorWord) (x3 := endPackVatTarget preSuck2σ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (R := [endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond
      (by simpa [endSkipAfterSuck2Stack, endSkipSuck2CallRest] using rd)
  exact endRuntimeBlocks.endRuntime_block_4034
    (R := endRuntimeBlocks.endRuntime_block_3956_fallthrough_stack
      (ee := I)
      (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (σ := world.2)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (R := [endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_3956_fallthrough_stack])
    rd4034

theorem endX_skip_after_suck2_to_hope_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preSuck1σ preSuck2σ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3956⟩
      (endSkipAfterSuck2Stack preSuck2σ I outCat outVat outBids sel)
      (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (endSkipSuck2CallAw aw) rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4040⟩
      (endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat outBids sel)
      (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) aw' rdata
      world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSkipSuck2CallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmemGen := endSkipHopeCallMem_generated preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hcall64 := endSkipHopeCallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hdelta :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
                addrMask))) ≠
        UInt256.ofNat 0 := by
    rw [hvatTarget]
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw4038, k4038, C4038, rd4038⟩ :=
    endRuntimeBlocks.endRuntime_block_3956_taken_packed
      (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endSkipSuckSelectorWord) (x3 := endPackVatTarget preSuck2σ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (R := [endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest)
      (by simpa [endSkipAfterSuck2Stack, endSkipSuck2CallRest] using rd)
  have hstack3956 :
      endRuntimeBlocks.endRuntime_block_3956_taken_stack
          (ee := I)
          (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (σ := world.2)
          (x4 := endSkipBidsTabWord outBids)
          (x5 := endSkipBidsUsrWord outBids)
          (x6 := endSkipBidsLotWord outBids)
          (x7 := endSkipBidsBidWord outBids)
          (x8 := endFlowVatIlksRateWord outVat)
          (x9 := endSkipCatIlksFlipWord outCat)
          (R := [endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I,
            ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat outBids sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_3956_taken_stack]
    change
      [UInt256.isZero (extCodeSizeWord world.2
          (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask)),
        UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask,
        (⟨0⟩ : UInt256),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3956_taken_memory
            (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
            (x9 := endSkipCatIlksFlipWord outCat)),
        UInt256.sub
          (memLoad (UInt256.ofNat 64)
            (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids))
          (memLoad (UInt256.ofNat 64)
            (endRuntimeBlocks.endRuntime_block_3956_taken_memory
              (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
              (x9 := endSkipCatIlksFlipWord outCat))) +
          UInt256.ofNat 36,
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_3956_taken_memory
            (mem := endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
            (x9 := endSkipCatIlksFlipWord outCat)),
        (⟨0⟩ : UInt256),
        memLoad (UInt256.ofNat 64)
            (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids) +
          UInt256.ofNat 36,
        UInt256.ofNat 2746363844,
        UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask,
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
        endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat outBids sel
    rw [hmemGen, hcall64, hfree, hdelta, hend, hvatTarget]
    rfl
  have rd4038' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4038⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat outBids sel)
        (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) aw4038
        rdata world k4038 C4038 := by
    simpa [hstack3956, hmemGen] using rd4038
  have rd4040 := endRuntimeBlocks.endRuntime_block_4038
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSkipHopeCallStack preSuck1σ preSuck2σ world.2 I outCat outVat outBids sel)
    (by simp [endSkipHopeCallStack, endSkipHopeCallRest]) rd4038'
  exact ⟨aw4038, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_4038_stack] using rd4040⟩

set_option maxHeartbeats 12000000 in
theorem endSkipHopeExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outCat outVat outBids k C evm}
    {preSuck1σ preSuck2σ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipHopeCallCursor world preSuck1σ preSuck2σ I sel aw outCat outVat outBids rdata)
      k C (endSkipAfterSuck2Frame I outCat outVat outBids) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope" ]
      (sequenceExit ⟨4058⟩
        (fun cur frame e =>
          frame = endSkipAfterHopeFrame I outCat outVat outBids ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSkipAfterHopeStack world.2 I outCat outVat outBids sel ∧
          cur.mem = endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
          cur.aw = endSkipHopeCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨4040⟩ = some (.GAS, .none); decide)
    (by simp [endSkipHopeCallCursor, endSkipHopeCallStack, endSkipHopeCallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨4041⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipHopeCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skipAfterSuck2 evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endPackVatTarget world.2 I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkipHopeArgsAfterSuck2 evm I outCat outVat outBids
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_hope_skip outCat]
    change some (endSkipHopeEncodedCall outCat) =
      some ((endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
        128 36)
    rw [endSkipHopeCallMem_readCallData preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_hope out]
    intro rd hrel
    have rd4042 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
          ((⟨1⟩ : UInt256) :: endSkipHopeCallRest world.2 I outCat outVat outBids sel)
          (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (endSkipHopeCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipHopeCallCursor,
        endSkipHopeCallStack, endSkipHopeCallRest, endSkipHopeCallAw] using rd
    have rd4058 := endRuntimeBlocks.endRuntime_block_4042_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSkipHopeCallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipHopeCallRest]) (by native_decide) (by jump_dest) rd4042
    refine ⟨.ok (endSkipAfterHopeFrame I outCat outVat outBids) evm',
      Endpoint.reached
        (endSkipAfterHopeCursor preSuck1σ preSuck2σ world.2 I sel aw outCat outVat
          outBids out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSkipAfterHopeCursor, endSkipAfterHopeStack, endSkipHopeCallAw,
          endRuntimeBlocks.endRuntime_block_4042_taken_stack] using rd4058⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd4042 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
          ((⟨0⟩ : UInt256) :: endSkipHopeCallRest world.2 I outCat outVat outBids sel)
          (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (endSkipHopeCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipHopeCallCursor,
        endSkipHopeCallStack, endSkipHopeCallRest, endSkipHopeCallAw] using rd
    have rd4049 := endRuntimeBlocks.endRuntime_block_4042_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipHopeCallRest world.2 I outCat outVat outBids sel)
      (by simp [endSkipHopeCallRest]) (by native_decide) rd4042
    exact endRuntimeBlocks.endRuntime_block_4049
      (R := endRuntimeBlocks.endRuntime_block_4042_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipHopeCallRest world.2 I outCat outVat outBids sel))
      (by simp [endRuntimeBlocks.endRuntime_block_4042_fallthrough_stack,
        endSkipHopeCallRest])
      rd4049

abbrev endSkipAfterHopeRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outCat : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preSuck1σ preSuck2σ preHopeσ outVat outBids awHope,
      frame = endSkipAfterHopeFrame I outCat outVat outBids ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outBids.size < UInt256.size ∧
      256 ≤ outBids.size ∧
      cur.stack = endSkipAfterHopeStack preHopeσ I outCat outVat outBids sel ∧
      cur.mem = endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
      cur.aw = endSkipHopeCallAw awHope

set_option maxHeartbeats 12000000 in
theorem endSkipAfterSuck2ToHopeRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3956⟩
      (endSkipAfterSuck2Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      (checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
        [.var "flip"] "_hope")
      (sequenceExit ⟨4058⟩
        (endSkipAfterHopeRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨preSuck1σ, preSuck2σ, outVat, outBids, awHope, hframe, hrel, houtVat, h160,
      houtBids, h256, hstack, hmem, haw⟩
  cases hframe
  have rd3956 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3956⟩
        (endSkipAfterSuck2Stack preSuck2σ I outCat outVat outBids sel)
        (endSkipSuck2CallMem preSuck1σ preSuck2σ I outCat outVat outBids)
        (endSkipSuck2CallAw awHope) cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) := by
    have htarget :
        UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur0.world.2 I := by
      have hload := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
      rw [hrel.env] at hload
      rw [hrel.env]
      rw [hload]
      rw [u256_land_comm
        (storageRead I.codeOwner cur0.world.2 (UInt256.ofNat 1)) solcAddrMask]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endPackVatTarget cur0.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hsourceChecked :
        ExecBlock config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
          (checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "flip"] "_hope")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skipAfterSuck2_false evm I outCat outVat
              outBids hsrcNoCode)))
    have hrev := endX_skip_vat_no_code_after_suck2
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := awHope) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
      (k := k) (C := C) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (world := cur0.world) houtCat h96 houtVat h160 houtBids h256
      hvatNoCode rd3956
    exact ⟨.reverted, .reverted, hsourceChecked, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkipAfterSuck2Frame I outCat outVat outBids) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkipAfterSuck2Frame I outCat outVat outBids) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skipAfterSuck2_true evm I outCat outVat outBids
            hsrcCode))
        ExecBlock.nil
    obtain ⟨aw4040, k4040, C4040, rd4040⟩ :=
      endX_skip_after_suck2_to_hope_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awHope) (outCat := outCat)
        (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
        (k := k) (C := C) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (world := cur0.world) houtCat h96 houtVat h160 houtBids h256
        hvatNoCode rd3956
    have htailExact :=
      (endSkipHopeExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw4040) (rdata := cur0.rdata)
        (outCat := outCat) (outVat := outVat) (outBids := outBids)
        (k := k4040) (C := C4040) (evm := evm)
        (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (world := cur0.world) hperm houtCat h96 houtVat h160 houtBids h256)
        (by simpa [endSkipHopeCallCursor] using rd4040) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterSuck2Frame I outCat outVat outBids) evm
          [ .externalCall (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope" ]
          (sequenceExit ⟨4058⟩
            (endSkipAfterHopeRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, preSuck1σ, preSuck2σ, cur0.world.2, outVat, outBids,
                aw4040, hframeQ, hrelQ, houtVat, h160, houtBids, h256,
                hstackQ, hmemQ, hawQ⟩
          | returned worldOut outOut =>
              exact hQ
          | reverted =>
              exact hQ
      | returned frameOut evmOut ret =>
          exact hQ
      | «break» frameOut evmOut =>
          exact hQ
      | «continue» frameOut evmOut =>
          exact hQ
      | reverted =>
          exact hQ
    simpa [checkedExternalCallStmts] using
      BlockProgress.prepend hsourceRequire htailProgress

abbrev endSkipYankSelectorWord : UInt256 :=
  endSnipYankSelectorWord

abbrev endSkipYankSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (UInt256.ofNat 4294967295) endSkipYankSelectorWord)
    (UInt256.ofNat 224)

def endSkipYankPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg1Word I)

def endSkipYankEncodedCall (I : ExecutionEnv) : ByteArray :=
  yankSelector ++ ⟨(endSkipYankPayloadBytes I).toArray⟩

abbrev endSkipYankMemSel (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  endSkipYankSelectorEncodedWord.toByteArray.write 0
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 32

abbrev endSkipYankCallMem (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endArg1Word I).toByteArray.write 0
    (endSkipYankMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 32

abbrev endSkipYankCallRest (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endSkipYankSelectorWord, endSkipFlipTarget outCat,
    endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
    endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
    endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
    endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipYankCallStack (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [endSkipFlipTarget outCat, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨0⟩] ++
    endSkipYankCallRest I outCat outVat outBids sel

abbrev endSkipYankCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outCat outVat outBids rdata : ByteArray) : Cursor :=
  { pc := ⟨4134⟩,
    stack := endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel,
    mem := endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids,
    aw := aw, rdata := rdata, world := world }

abbrev endSkipYankCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSkipAfterYankFrame (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns []) }

abbrev endSkipAfterYankStack (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSkipYankCallRest I outCat outVat outBids sel

abbrev endSkipAfterYankCursor (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outCat outVat outBids out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨4152⟩,
    stack := endSkipAfterYankStack I outCat outVat outBids sel,
    mem := endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids,
    aw := endSkipYankCallAw aw, rdata := out, world := world }

theorem endSkipAfterHopeFrame_get_flip (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterHopeFrame I outCat outVat outBids).locals.get? "flip" =
      some (endSkipFlipValue outCat) := by
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "flip") = some (endSkipFlipValue outCat)
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "flip") (collapseReturns []) (by decide)]
  exact endSkipAfterSuck2Frame_get_flip I outCat outVat outBids

theorem endEvalSkipFlipAfterHope (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (.var "flip") =
      .ok (endSkipFlipValue outCat) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterHopeFrame_get_flip I outCat outVat outBids

theorem endEvalSkipFlipAfterHope_masked (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (.var "flip") =
      .ok (.address (AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)) := by
  rw [endEvalSkipFlipAfterHope evm I outCat outVat outBids]
  simp [endSkipFlipValue, endSkipFlipAddress_eq_mask outCat]

theorem endSkipAfterHopeFrame_get_id (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterHopeFrame I outCat outVat outBids).locals.get? "id" =
      some (endUIntValue (endArg1Word I)) := by
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "id") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "id") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "id") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "id")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "id") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "id") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "id") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "id") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  exact endSkipAfterRateFrame_get_id I outCat outVat

theorem endEvalSkipIdAfterHope (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (.var "id") =
      .ok (endUIntValue (endArg1Word I)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterHopeFrame_get_id I outCat outVat outBids

theorem endEvalFlipCodeGuard_skipAfterHope_false (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) = ⟨0⟩) :
    evalExpr? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSkipAfterHopeFrame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .var "flip") (target := endSkipFlipTarget outCat)
    (endEvalSkipFlipAfterHope_masked evm I outCat outVat outBids) hnocode

theorem endEvalFlipCodeGuard_skipAfterHope_true (evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSkipAfterHopeFrame I outCat outVat outBids).locals) (evm := evm)
    (receiver := .var "flip") (target := endSkipFlipTarget outCat)
    (endEvalSkipFlipAfterHope_masked evm I outCat outVat outBids) hcode

theorem endEvalSkipYankArgsAfterHope (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExprs? config (endSkipAfterHopeFrame I outCat outVat outBids) evm
      [.var "id"] =
      .ok [endUIntValue (endArg1Word I)] := by
  rw [evalExprs?]
  rw [endEvalSkipIdAfterHope evm I outCat outVat outBids]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endSkipYankSelectorEncodedWord_prefix :
    (endSkipYankSelectorEncodedWord.toByteArray).extract 0 4 = yankSelector := by
  native_decide

theorem endSkipYankMemSel_size (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipYankMemSel preSuck1σ preSuck2σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    endSkipYankSelectorEncodedWord 128 384 384
    (endSkipHopeCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipHopeCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipYankCallMem_size (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size = 384 := by
  exact toByteArray_write32_size_of_le
    (endSkipYankMemSel preSuck1σ preSuck2σ I outCat outVat outBids)
    (endArg1Word I) 132 384 384
    (endSkipYankMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)
    (by
      rw [endSkipYankMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (by omega)

theorem endSkipYankCallMem_read64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1Word I)
    (endSkipYankMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 64
    (by
      rw [endSkipYankMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSkipYankSelectorEncodedWord
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 64
    (by
      rw [endSkipHopeCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  exact endSkipHopeCallMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256

theorem endSkipYankCallMem_mload64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64)
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (by
      rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (endSkipYankCallMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

theorem endSkipYankCallMem_readSelector (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      128 4 =
      yankSelector := by
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSkipYankMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)
    (by
      rw [endSkipYankMemSel_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by decide) (by decide)]
  change ((endSkipYankSelectorEncodedWord.toByteArray.write 0
      (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      128 32).readWithPadding 128 4) = yankSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipYankSelectorEncodedWord
    (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipYankSelectorEncodedWord_prefix]

theorem endSkipYankCallMem_readId (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      132 32 =
      (endArg1Word I).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endArg1Word I)
    (endSkipYankMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132

theorem endSkipYankCallMem_readCallData (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
      128 36 =
      endSkipYankEncodedCall I := by
  have hsize :
      164 ≤ (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSkipYankCallMem_readSelector preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipYankCallMem_readId preSuck1σ preSuck2σ I outCat outVat outBids]
  rw [toByteArray_eq_toBytesBE (endArg1Word I)]
  simp only [endSkipYankEncodedCall, endSkipYankPayloadBytes]

theorem endEncodeABIValues_yank_skip (I : ExecutionEnv) :
    encodeABIValues? [uint256] [endUIntValue (endArg1Word I)] =
      some (endSkipYankPayloadBytes I) := by
  simpa [endSkipYankPayloadBytes, endSnipYankPayloadBytes] using
    endEncodeABIValues_yank_snip I

theorem endEncodeCallWithSelector_yank_skip (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? yankSelector [uint256]
      [endUIntValue (endArg1Word I)] =
      some (endSkipYankEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_yank_skip I]
  simp [endSkipYankEncodedCall, endSkipYankPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_yank_skip (I : ExecutionEnv) :
    config.externalABI.encode? "yank" [endUIntValue (endArg1Word I)] =
      some (endSkipYankEncodedCall I) := by
  rw [endExternalEncode_yank_branch]
  exact endEncodeCallWithSelector_yank_skip I

end Benchmarks.Dss.End
