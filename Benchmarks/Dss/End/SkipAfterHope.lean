import Benchmarks.Dss.End.Skip

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)`: suffix after `vat.hope(flip)` -/

theorem endSkipYankCallMem_generated (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    endRuntimeBlocks.endRuntime_block_4058_taken_memory
        (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
        (x11 := endArg1Word I) =
      endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids := by
  have hfree := endSkipHopeCallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  unfold endRuntimeBlocks.endRuntime_block_4058_taken_memory
  unfold endSkipYankCallMem endSkipYankMemSel endSkipYankSelectorEncodedWord
    endSkipYankSelectorWord endSnipYankSelectorWord
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show (UInt256.ofNat 4 + (⟨128⟩ : UInt256)).toNat = 132 from by native_decide]

theorem endX_skip_flip_no_code_after_hope {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preSuck1σ preSuck2σ preHopeσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hflipNoCode : extCodeSizeWord world.2 (endSkipFlipTarget outCat) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4058⟩
      (endSkipAfterHopeStack preHopeσ I outCat outVat outBids sel)
      (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (endSkipHopeCallAw aw) rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hflipTarget :
      UInt256.land addrMask (endSkipCatIlksFlipWord outCat) =
        endSkipFlipTarget outCat := by
    rw [hmask]
    rw [u256_land_comm solcAddrMask (endSkipCatIlksFlipWord outCat)]
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land addrMask (endSkipCatIlksFlipWord outCat)))) =
        UInt256.ofNat 0 := by
    rw [hflipTarget, hflipNoCode]
    native_decide
  obtain ⟨aw4128, k4128, C4128, rd4128⟩ :=
    endRuntimeBlocks.endRuntime_block_4058_fallthrough_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
      (x2 := endSkipHopeSelectorWord) (x3 := endPackVatTarget preHopeσ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (x10 := endSkipCatIlksFlipWord outCat)
      (x11 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond
      (by simpa [endSkipAfterHopeStack, endSkipHopeCallRest] using rd)
  exact endRuntimeBlocks.endRuntime_block_4128
    (R := endRuntimeBlocks.endRuntime_block_4058_fallthrough_stack
      (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (σ := world.2)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (x10 := endSkipCatIlksFlipWord outCat)
      (x11 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4058_fallthrough_stack])
    rd4128

theorem endX_skip_after_hope_to_yank_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outCat outVat outBids rdata k C}
    {preSuck1σ preSuck2σ preHopeσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hflipCode : extCodeSizeWord world.2 (endSkipFlipTarget outCat) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4058⟩
      (endSkipAfterHopeStack preHopeσ I outCat outVat outBids sel)
      (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      (endSkipHopeCallAw aw) rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4134⟩
      (endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel)
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids) aw' rdata
      world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hflipTarget :
      UInt256.land addrMask (endSkipCatIlksFlipWord outCat) =
        endSkipFlipTarget outCat := by
    rw [hmask]
    rw [u256_land_comm solcAddrMask (endSkipCatIlksFlipWord outCat)]
  have hfree := endSkipHopeCallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hmemGen := endSkipYankCallMem_generated preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hyank64 := endSkipYankCallMem_mload64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  have hdelta :
      UInt256.sub (UInt256.ofNat 32 + (UInt256.ofNat 4 + (⟨128⟩ : UInt256)))
          (⟨128⟩ : UInt256) =
        ⟨36⟩ := by
    native_decide
  have hend : UInt256.ofNat 32 + (UInt256.ofNat 4 + (⟨128⟩ : UInt256)) = ⟨164⟩ := by
    native_decide
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land addrMask (endSkipCatIlksFlipWord outCat)))) ≠
        UInt256.ofNat 0 := by
    rw [hflipTarget]
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hflipCode]
    native_decide
  obtain ⟨aw4132, k4132, C4132, rd4132⟩ :=
    endRuntimeBlocks.endRuntime_block_4058_taken_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
      (x2 := endSkipHopeSelectorWord) (x3 := endPackVatTarget preHopeσ I)
      (x4 := endSkipBidsTabWord outBids)
      (x5 := endSkipBidsUsrWord outBids)
      (x6 := endSkipBidsLotWord outBids)
      (x7 := endSkipBidsBidWord outBids)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (x10 := endSkipCatIlksFlipWord outCat)
      (x11 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest)
      (by simpa [endSkipAfterHopeStack, endSkipHopeCallRest] using rd)
  have hstack4058 :
      endRuntimeBlocks.endRuntime_block_4058_taken_stack
          (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (σ := world.2)
          (x4 := endSkipBidsTabWord outBids)
          (x5 := endSkipBidsUsrWord outBids)
          (x6 := endSkipBidsLotWord outBids)
          (x7 := endSkipBidsBidWord outBids)
          (x8 := endFlowVatIlksRateWord outVat)
          (x9 := endSkipCatIlksFlipWord outCat)
          (x10 := endSkipCatIlksFlipWord outCat)
          (x11 := endArg1Word I)
          (R := [endArg0Word I, ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
          endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_4058_taken_stack]
    change
      [UInt256.isZero (extCodeSizeWord world.2
          (UInt256.land addrMask (endSkipCatIlksFlipWord outCat))),
        UInt256.land addrMask (endSkipCatIlksFlipWord outCat), (⟨0⟩ : UInt256),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_4058_taken_memory
            (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
            (x11 := endArg1Word I)),
        UInt256.sub
          (UInt256.ofNat 32 +
            (UInt256.ofNat 4 +
              memLoad (UInt256.ofNat 64)
                (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)))
          (memLoad (UInt256.ofNat 64)
            (endRuntimeBlocks.endRuntime_block_4058_taken_memory
              (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
              (x11 := endArg1Word I))),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_4058_taken_memory
            (mem := endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
            (x11 := endArg1Word I)),
        (⟨0⟩ : UInt256),
        UInt256.ofNat 32 +
          (UInt256.ofNat 4 +
            memLoad (UInt256.ofNat 64)
              (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)),
        UInt256.ofNat 652224497,
        UInt256.land addrMask (endSkipCatIlksFlipWord outCat),
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
        endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel
    rw [hmemGen, hyank64, hfree, hdelta, hend, hflipTarget]
    rfl
  have rd4132' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4132⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)) ::
          endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel)
        (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids) aw4132
        rdata world k4132 C4132 := by
    simpa [hstack4058, hmemGen] using rd4132
  have rd4134 := endRuntimeBlocks.endRuntime_block_4132
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endSkipFlipTarget outCat)))
    (R := endSkipYankCallStack preSuck1σ preSuck2σ I outCat outVat outBids sel)
    (by simp [endSkipYankCallStack, endSkipYankCallRest]) rd4132'
  exact ⟨aw4132, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_4132_stack] using rd4134⟩

set_option maxHeartbeats 12000000 in
theorem endSkipYankExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outCat outVat outBids k C evm}
    {preSuck1σ preSuck2σ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipYankCallCursor world preSuck1σ preSuck2σ I sel aw outCat outVat outBids rdata)
      k C (endSkipAfterHopeFrame I outCat outVat outBids) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ]
      (sequenceExit ⟨4152⟩
        (fun cur frame e =>
          frame = endSkipAfterYankFrame I outCat outVat outBids ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSkipAfterYankStack I outCat outVat outBids sel ∧
          cur.mem = endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
          cur.aw = endSkipYankCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨4134⟩ = some (.GAS, .none); decide)
    (by simp [endSkipYankCallCursor, endSkipYankCallStack, endSkipYankCallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endSkipFlipTarget outCat).toNat)
    (argVals := [endUIntValue (endArg1Word I)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨4135⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipYankCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro _
    rw [endEvalSkipFlipAfterHope_masked evm I outCat outVat outBids]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkipYankArgsAfterHope evm I outCat outVat outBids
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endSkipFlipTarget outCat).toNat % EVM.addressModulus % AccountAddress.size =
      (endSkipFlipTarget outCat).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_yank_skip I]
    change some (endSkipYankEncodedCall I) =
      some ((endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
        128 36)
    rw [endSkipYankCallMem_readCallData preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_yank out]
    intro rd hrel
    have rd4136 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
          ((⟨1⟩ : UInt256) :: endSkipYankCallRest I outCat outVat outBids sel)
          (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (endSkipYankCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipYankCallCursor,
        endSkipYankCallStack, endSkipYankCallRest, endSkipYankCallAw] using rd
    have rd4152 := endRuntimeBlocks.endRuntime_block_4136_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSkipYankCallRest I outCat outVat outBids sel)
      (by simp [endSkipYankCallRest]) (by native_decide) (by jump_dest) rd4136
    refine ⟨.ok (endSkipAfterYankFrame I outCat outVat outBids) evm',
      Endpoint.reached
        (endSkipAfterYankCursor preSuck1σ preSuck2σ I sel aw outCat outVat
          outBids out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSkipAfterYankCursor, endSkipAfterYankStack, endSkipYankCallAw,
          endRuntimeBlocks.endRuntime_block_4136_taken_stack] using rd4152⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd4136 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
          ((⟨0⟩ : UInt256) :: endSkipYankCallRest I outCat outVat outBids sel)
          (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (endSkipYankCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipYankCallCursor,
        endSkipYankCallStack, endSkipYankCallRest, endSkipYankCallAw] using rd
    have rd4143 := endRuntimeBlocks.endRuntime_block_4136_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkipYankCallRest I outCat outVat outBids sel)
      (by simp [endSkipYankCallRest]) (by native_decide) rd4136
    exact endRuntimeBlocks.endRuntime_block_4143
      (R := endRuntimeBlocks.endRuntime_block_4136_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkipYankCallRest I outCat outVat outBids sel))
      (by simp [endRuntimeBlocks.endRuntime_block_4136_fallthrough_stack,
        endSkipYankCallRest])
      rd4143

abbrev endSkipAfterYankRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outCat : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preSuck1σ preSuck2σ outVat outBids awYank,
      frame = endSkipAfterYankFrame I outCat outVat outBids ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outBids.size < UInt256.size ∧
      256 ≤ outBids.size ∧
      cur.stack = endSkipAfterYankStack I outCat outVat outBids sel ∧
      cur.mem = endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
      cur.aw = endSkipYankCallAw awYank

set_option maxHeartbeats 12000000 in
theorem endSkipAfterHopeToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨4058⟩
      (endSkipAfterHopeRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      (checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank")
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨preSuck1σ, preSuck2σ, preHopeσ, outVat, outBids, awYank, hframe, hrel,
      houtVat, h160, houtBids, h256, hstack, hmem, haw⟩
  cases hframe
  have rd4058 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4058⟩
        (endSkipAfterHopeStack preHopeσ I outCat outVat outBids sel)
        (endSkipHopeCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
        (endSkipHopeCallAw awYank) cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
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
        ExecBlock config (endSkipAfterHopeFrame I outCat outVat outBids) evm
          (checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalFlipCodeGuard_skipAfterHope_false evm I outCat outVat
              outBids hsrcNoCode)))
    have hrev := endX_skip_flip_no_code_after_hope
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := awYank) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
      (k := k) (C := C) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (preHopeσ := preHopeσ) (world := cur0.world) hflipNoCode rd4058
    exact ⟨.reverted, .reverted, hsourceChecked, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endSkipFlipTarget outCat) ≠ ⟨0⟩ := by
      intro hzero
      exact hflipNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkipAfterHopeFrame I outCat outVat outBids) evm
          [ .require (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) ]
          (.ok (endSkipAfterHopeFrame I outCat outVat outBids) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalFlipCodeGuard_skipAfterHope_true evm I outCat outVat outBids
            hsrcCode))
        ExecBlock.nil
    obtain ⟨aw4134, k4134, C4134, rd4134⟩ :=
      endX_skip_after_hope_to_yank_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awYank) (outCat := outCat)
        (outVat := outVat) (outBids := outBids) (rdata := cur0.rdata)
        (k := k) (C := C) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (preHopeσ := preHopeσ) (world := cur0.world)
        houtCat h96 houtVat h160 houtBids h256 hflipNoCode rd4058
    have htailExact :=
      (endSkipYankExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw4134) (rdata := cur0.rdata)
        (outCat := outCat) (outVat := outVat) (outBids := outBids)
        (k := k4134) (C := C4134) (evm := evm)
        (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (world := cur0.world) hperm houtCat h96 houtVat h160 houtBids h256)
        (by simpa [endSkipYankCallCursor] using rd4134) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterHopeFrame I outCat outVat outBids) evm
          [ .externalCall (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ]
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, preSuck1σ, preSuck2σ, outVat, outBids, aw4134,
                hframeQ, hrelQ, houtVat, h160, houtBids, h256, hstackQ, hmemQ,
                hawQ⟩
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

end Benchmarks.Dss.End
