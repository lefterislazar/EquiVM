import Benchmarks.Dss.End.Snip
import Benchmarks.Dss.End.RuntimeBlocks_006
import Benchmarks.Dss.End.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `snip(bytes32,uint256)`: suffix after `clip.yank` -/

set_option maxHeartbeats 12000000 in
theorem endSnipAfterSuckToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {outDog : ByteArray}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨2252⟩
      (endSnipAfterSuckRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
      (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
      (sequenceExit ⟨2346⟩
        (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨preσ, outVat, outSales, awSuck, hframe, hrel, houtVat, h160, houtSales, h192,
      hstack, hmem, haw⟩
  cases hframe
  have rd2252 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2252⟩
        (endSnipAfterSuckStack preσ I outDog outVat outSales sel)
        (endSnipSuckCallMem preσ I outDog outVat outSales)
        (endSnipSuckCallAw awSuck) cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) =
        extCodeSizeWord cur0.world.2 (endSnipClipTarget outDog) := by
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endSnipClipTarget outDog)).symm
  by_cases hclipNoCode :
      extCodeSizeWord cur0.world.2 (endSnipClipTarget outDog) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) = ⟨0⟩ := by
      rw [hsrcCodeEq, hclipNoCode]
    have hsourceChecked :
        ExecBlock config (endSnipAfterSuckFrame I outDog outVat outSales) evm
          (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
          .reverted := by
      change ExecBlock config (endSnipAfterSuckFrame I outDog outVat outSales) evm
        [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
          .externalCall (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ]
        .reverted
      exact ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalClipCodeGuard_snipAfterSuck_false evm I outDog outVat outSales
              hsrcNoCode))
    have hrev := endX_snip_clip_no_code_after_suck
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := endSnipSuckCallAw awSuck) (outDog := outDog)
      (outVat := outVat) (outSales := outSales) (out := cur0.rdata) (k := k) (C := C)
      (preσ := preσ) (world := cur0.world)
      houtDog h128 houtVat h160 houtSales h192 hclipNoCode rd2252
    exact ⟨.reverted, .reverted, hsourceChecked, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) ≠ ⟨0⟩ := by
      intro hzero
      exact hclipNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSnipAfterSuckFrame I outDog outVat outSales) evm
          [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) ]
          (.ok (endSnipAfterSuckFrame I outDog outVat outSales) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalClipCodeGuard_snipAfterSuck_true evm I outDog outVat outSales hsrcCode))
        ExecBlock.nil
    obtain ⟨aw2328, k2328, C2328, rd2328⟩ :=
      endX_snip_after_suck_to_yank_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := endSnipSuckCallAw awSuck) (outDog := outDog)
        (outVat := outVat) (outSales := outSales) (out := cur0.rdata) (k := k) (C := C)
        (preσ := preσ) (world := cur0.world)
        houtDog h128 houtVat h160 houtSales h192 hclipNoCode rd2252
    have htailExact :=
      (endSnipYankExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw2328) (rdata := cur0.rdata)
        (outDog := outDog) (outVat := outVat) (outSales := outSales)
        (preσ := preσ) (k := k2328) (C := C2328) (evm := evm)
        (world := cur0.world)
        hperm houtDog h128 houtVat h160 houtSales h192)
        (by simpa [endSnipYankCallCursor] using rd2328) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterSuckFrame I outDog outVat outSales) evm
          [ .externalCall (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ]
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, preσ, outVat, outSales, aw2328,
                hframeQ, hrelQ, houtVat, h160, houtSales, h192, hstackQ, hmemQ, hawQ⟩
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
    change BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipAfterSuckFrame I outDog outVat outSales) evm
      [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)),
        .externalCall (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ]
      (sequenceExit ⟨2346⟩
        (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi [])))
    exact BlockProgress.prepend hsourceRequire htailProgress

abbrev endSnipArtStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (outVat outSales : ByteArray) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endFlowArtWorldSlot I)
    (endSnipArtNewWorldWord world.2 I outVat outSales))

abbrev endSnipAfterArtStoreMem (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_2391_taken_memory
    (mem := endSnipArtHashMem preσ I outDog outVat outSales) (x9 := endArg0Word I)

theorem endSnipArtHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 14).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowArtWorldSlot I :=
  endFlowArtHashSlot mem I

theorem endX_snip_after_yank_rate_invalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2346⟩
      (endSnipAfterYankStack preσ I outDog outVat outSales sel)
      (endSnipYankCallMem preσ I outDog outVat outSales) aw rdata world k C) :
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2360 := endRuntimeBlocks.endRuntime_block_2346_fallthrough
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨164⟩ : UInt256))
    (x2 := endSnipYankSelectorWord) (x3 := endSnipClipTarget outDog)
    (x4 := endSnipSalesUsrWord outSales) (x5 := endSnipSalesLotWord outSales)
    (x6 := endSnipSalesTabWord outSales) (x7 := endFlowVatIlksRateWord outVat)
    (R := [endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrate
    (by simpa [endSnipAfterYankStack, endSnipYankCallRest] using rd)
  exact endRuntimeBlocks.endRuntime_block_2360 rd2360

theorem endX_snip_after_yank_to_add {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2346⟩
      (endSnipAfterYankStack preσ I outDog outVat outSales sel)
      (endSnipYankCallMem preσ I outDog outVat outSales) aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSnipAddCallStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw' rdata world k' C' := by
  have rd2361 := endRuntimeBlocks.endRuntime_block_2346_taken
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨164⟩ : UInt256))
    (x2 := endSnipYankSelectorWord) (x3 := endSnipClipTarget outDog)
    (x4 := endSnipSalesUsrWord outSales) (x5 := endSnipSalesLotWord outSales)
    (x6 := endSnipSalesTabWord outSales) (x7 := endFlowVatIlksRateWord outVat)
    (R := [endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrate (by jump_dest)
    (by simpa [endSnipAfterYankStack, endSnipYankCallRest] using rd)
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_2361_packed
      (x0 := endSnipSalesTabWord outSales) (x1 := endFlowVatIlksRateWord outVat)
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSnipSalesUsrWord outSales)
      (x4 := endSnipSalesLotWord outSales) (x5 := endSnipSalesTabWord outSales)
      (x6 := endFlowVatIlksRateWord outVat) (x7 := endSnipDogIlksClipWord outDog)
      (x8 := endSnipDogIlksClipWord outDog) (x9 := endArg1Word I)
      (x10 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_2346_taken_stack] using rd2361)
  have hslot :=
    endSnipArtHashSlot (endSnipYankCallMem preσ I outDog outVat outSales) I
  exact ⟨aw10092, k10092, C10092, by
    simpa [endRuntimeBlocks.endRuntime_block_2361_stack, endSnipAddCallStack,
      endSnipArtWord, endSnipArtHashMem, endFlowArtWorldWord, hslot] using rd10092⟩

theorem endX_snip_art_add_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ (endFlowArtWorldWord world.2 I).toNat +
      (endSnipArtWord outVat outSales).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSnipAddCallStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond := endPackAddFailCond
    (endSnipArtWord outVat outSales) (endFlowArtWorldWord world.2 I) hover
  have rd10104 := endRuntimeBlocks.endRuntime_block_10092_fallthrough
    (x0 := endSnipArtWord outVat outSales)
    (x1 := endFlowArtWorldWord world.2 I)
    (R := [⟨2391⟩, endSnipArtWord outVat outSales,
      endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
      endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
      endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcond (by simpa [endSnipAddCallStack] using rd)
  exact endRuntimeBlocks.endRuntime_block_10104
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endSnipArtWord outVat outSales)
      (x1 := endFlowArtWorldWord world.2 I)
      (R := [⟨2391⟩, endSnipArtWord outVat outSales,
        endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endX_snip_art_add_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hfit : (endFlowArtWorldWord world.2 I).toNat +
      (endSnipArtWord outVat outSales).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSnipAddCallStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2391⟩
      (endSnipAfterAddStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw' rdata world k' C' := by
  have hcond := endPackAddSuccessCond
    (endSnipArtWord outVat outSales) (endFlowArtWorldWord world.2 I) hfit
  obtain ⟨aw10108, k10108, C10108, rd10108⟩ :=
    endRuntimeBlocks.endRuntime_block_10092_taken_packed
      (x0 := endSnipArtWord outVat outSales)
      (x1 := endFlowArtWorldWord world.2 I)
      (R := [⟨2391⟩, endSnipArtWord outVat outSales,
        endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) (by simpa [endSnipAddCallStack] using rd)
  obtain ⟨aw2391, k2391, C2391, rd2391⟩ :=
    endRuntimeBlocks.endRuntime_block_10108_packed
      (x0 := endSnipArtWord outVat outSales + endFlowArtWorldWord world.2 I)
      (x1 := endSnipArtWord outVat outSales)
      (x2 := endFlowArtWorldWord world.2 I)
      (x3 := (⟨2391⟩ : UInt256))
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10092_taken_stack] using rd10108)
  have hsum :
      endSnipArtWord outVat outSales + endFlowArtWorldWord world.2 I =
        endSnipArtNewWorldWord world.2 I outVat outSales := by
    simp [endSnipArtNewWorldWord, endGenericAddResult, u256_add_comm]
  exact ⟨aw2391, k2391, C2391, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack, endSnipAfterAddStack,
      hsum] using rd2391⟩

abbrev endSnipAfterArtNewState (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSales : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (ArtSlot (endArg0Bytes32Key I))
    (endSnipArtNewWord evm I outVat outSales)

theorem endSnipAfterYankFrame_get_lot (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterYankFrame I outDog outVat outSales).locals.get? "lot" =
      some (endSnipLotValue outSales) := by
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "lot") = some (endSnipLotValue outSales)
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "lot") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "lot") = some (endSnipLotValue outSales)
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "lot") (collapseReturns []) (by decide)]
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "lot") = some (endSnipLotValue outSales)
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "lot")
    (endSnipUsrValue outSales) (by decide)]
  exact store_get_self (endSnipAfterTabFrame I outDog outVat outSales).locals
    "lot" (endSnipLotValue outSales)

theorem endSnipAfterYankFrame_get_usr (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterYankFrame I outDog outVat outSales).locals.get? "usr" =
      some (endSnipUsrValue outSales) := by
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "usr") = some (endSnipUsrValue outSales)
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "usr") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "usr") = some (endSnipUsrValue outSales)
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "usr") (collapseReturns []) (by decide)]
  exact store_get_self ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) "usr" (endSnipUsrValue outSales)

theorem endSnipAfterArtFrame_get_lot (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtFrame I outDog outVat outSales).locals.get? "lot" =
      some (endSnipLotValue outSales) := by
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "lot") = some (endSnipLotValue outSales)
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "lot") (endSnipArtValue outVat outSales) (by decide)]
  exact endSnipAfterYankFrame_get_lot I outDog outVat outSales

theorem endSnipAfterArtFrame_get_usr (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtFrame I outDog outVat outSales).locals.get? "usr" =
      some (endSnipUsrValue outSales) := by
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "usr") = some (endSnipUsrValue outSales)
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "usr") (endSnipArtValue outVat outSales) (by decide)]
  exact endSnipAfterYankFrame_get_usr I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_ArtNew (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "ArtNew" =
      some (endUIntValue (endSnipArtNewWord evm I outVat outSales)) := by
  exact store_get_self (endSnipAfterArtFrame I outDog outVat outSales).locals "ArtNew"
    (endUIntValue (endSnipArtNewWord evm I outVat outSales))

theorem endSnipAfterArtNewFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "art" =
      some (endSnipArtValue outVat outSales) := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "art") =
    some (endSnipArtValue outVat outSales)
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "art")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  exact endSnipAfterArtFrame_get_art I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_lot (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "lot" =
      some (endSnipLotValue outSales) := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "lot") =
    some (endSnipLotValue outSales)
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "lot")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  exact endSnipAfterArtFrame_get_lot I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_usr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "usr" =
      some (endSnipUsrValue outSales) := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "usr") =
    some (endSnipUsrValue outSales)
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "usr")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  exact endSnipAfterArtFrame_get_usr I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "ilk")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  exact endSnipAfterArtFrame_get_ilk I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_Art_none (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "Art" = none := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "Art") = none
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "Art")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  exact endSnipAfterArtFrame_get_Art_none I outDog outVat outSales

theorem endEvalSnipArtNewVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.var "ArtNew") =
      .ok (endUIntValue (endSnipArtNewWord baseEvm I outVat outSales)) := by
  rw [evalExpr?]
  rw [endSnipAfterArtNewFrame_get_ArtNew baseEvm I outDog outVat outSales]
  rfl

theorem endEvalSnipArtVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.var "art") = .ok (endSnipArtValue outVat outSales) := by
  rw [evalExpr?]
  rw [endSnipAfterArtNewFrame_get_art baseEvm I outDog outVat outSales]
  rfl

theorem endEvalSnipLotVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.var "lot") = .ok (endSnipLotValue outSales) := by
  rw [evalExpr?]
  rw [endSnipAfterArtNewFrame_get_lot baseEvm I outDog outVat outSales]
  rfl

theorem endEvalSnipUsrVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.var "usr") = .ok (endSnipUsrValue outSales) := by
  rw [evalExpr?]
  rw [endSnipAfterArtNewFrame_get_usr baseEvm I outDog outVat outSales]
  rfl

theorem endEvalSnipIlkVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.var "ilk") = .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSnipAfterArtNewFrame_get_ilk baseEvm I outDog outVat outSales]
  rfl

theorem endAssignSnipArtNew (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
        .storage (ArtRef (.var "ilk"))
        (endUIntValue (endSnipArtNewWord evm I outVat outSales)) =
      .ok (endSnipAfterArtNewFrame evm I outDog outVat outSales,
        endSnipAfterArtNewState evm I outVat outSales) := by
  let er : EvaledStorageRef := { base := "Art", steps := [.mindex (endArg0Bytes32Key I)] }
  let loc : StorageLoc := wordLoc (ArtSlot (endArg0Bytes32Key I))
  have hdrop : 32 ≤ I.calldata.toList.length - 4 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    omega
  have her : evalStorageRef config (endSnipAfterArtNewFrame evm I outDog outVat outSales)
      evm (ArtRef (.var "ilk")) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefStep, ArtRef, endArg0Bytes32Key,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      endEvalSnipIlkVarAfterAdd, bytes32Width, hdrop]
  have hty :
      storageTypeAt? (endSnipAfterArtNewFrame evm I outDog outVat outSales).contract.storage
          er =
        some (.elem (.int uint256Int)) := by
    unfold endSnipAfterArtNewFrame
    simp [er, storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simp [er, loc]
  have hstore :
      storageLocStore evm loc (endUIntValue (endSnipArtNewWord evm I outVat outSales)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (ArtSlot (endArg0Bytes32Key I)) (endSnipArtNewWord evm I outVat outSales)) := by
    simpa [loc, wordLoc, uint256Loc, endUIntValue] using
      storageLocStore_uint256 evm (ArtSlot (endArg0Bytes32Key I))
        (endSnipArtNewWord evm I outVat outSales)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endSnipAfterArtNewFrame evm I outDog outVat outSales)
    (evm := evm) (slot := ArtRef (.var "ilk")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endSnipArtNewWord evm I outVat outSales).toNat)
    (endSnipAfterArtNewFrame_get_Art_none evm I outDog outVat outSales)
    her hty hloc hstore
  simpa [endSnipAfterArtNewState, loc, endUIntValue] using hassign

theorem endEvalSnipLotLimit_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) := by
  have hlt : Int.ofNat (endSnipSalesLotWord outSales).toNat < int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hlot
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipLotVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [evalExpr?, evalBinaryOp?, endSnipLotValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hlt

theorem endEvalSnipLotLimit_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSnipSalesLotWord outSales).toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool false) := by
  have hle : int256Limit ≤ Int.ofNat (endSnipSalesLotWord outSales).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hlot
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipLotVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [evalExpr?, evalBinaryOp?, endSnipLotValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hle

theorem endEvalSnipArtLimit_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool true) := by
  have hlt : Int.ofNat (endSnipArtWord outVat outSales).toNat < int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipArtVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [evalExpr?, evalBinaryOp?, endSnipArtValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hlt

theorem endEvalSnipArtLimit_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSnipArtWord outVat outSales).toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool false) := by
  have hle : int256Limit ≤ Int.ofNat (endSnipArtWord outVat outSales).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipArtVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [evalExpr?, evalBinaryOp?, endSnipArtValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hle

theorem endEvalSnipLimitGuard_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool true) := by
  rw [evalExpr?]
  rw [endEvalSnipLotLimit_true baseEvm evm I outDog outVat outSales hlot]
  rw [endEvalSnipArtLimit_true baseEvm evm I outDog outVat outSales hart]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSnipLimitGuard_lot_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSnipSalesLotWord outSales).toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSnipLotLimit_false baseEvm evm I outDog outVat outSales hlot]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSnipLimitGuard_art_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSnipArtWord outVat outSales).toNat) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSnipLotLimit_true baseEvm evm I outDog outVat outSales hlot]
  rw [endEvalSnipArtLimit_false baseEvm evm I outDog outVat outSales hart]
  simp [EvalResult.bind, bind, pure]

def endSnipAfterAddStoreGuardStmts : List Stmt :=
  [ .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
    .require
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) ]

theorem endSnipAfterAddStoreGuardOk (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    ExecBlock config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
      endSnipAfterAddStoreGuardStmts
      (.ok (endSnipAfterArtNewFrame evm I outDog outVat outSales)
        (endSnipAfterArtNewState evm I outVat outSales)) := by
  simp [endSnipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSnipArtNewVarAfterAdd evm evm I outDog outVat outSales)
      (endAssignSnipArtNew evm I outDog outVat outSales (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (endEvalSnipLimitGuard_true evm
          (endSnipAfterArtNewState evm I outVat outSales) I outDog outVat outSales
          hlot hart)) <|
    ExecBlock.nil

theorem endSnipAfterAddStoreGuardLotRevert (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSnipSalesLotWord outSales).toNat) :
    ExecBlock config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
      endSnipAfterAddStoreGuardStmts .reverted := by
  simp [endSnipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSnipArtNewVarAfterAdd evm evm I outDog outVat outSales)
      (endAssignSnipArtNew evm I outDog outVat outSales (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSnipLimitGuard_lot_false evm
          (endSnipAfterArtNewState evm I outVat outSales) I outDog outVat outSales
          hlot))

theorem endSnipAfterAddStoreGuardArtRevert (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSnipArtWord outVat outSales).toNat) :
    ExecBlock config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
      endSnipAfterAddStoreGuardStmts .reverted := by
  simp [endSnipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSnipArtNewVarAfterAdd evm evm I outDog outVat outSales)
      (endAssignSnipArtNew evm I outDog outVat outSales (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSnipLimitGuard_art_false evm
          (endSnipAfterArtNewState evm I outVat outSales) I outDog outVat outSales
          hlot hart))

theorem endSnipSltZero_of_lt_limit (w : UInt256)
    (h : w.toNat < endFreeInt256LimitWord.toNat) :
    UInt256.slt w (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by native_decide
  have hhi : w.toNat < 2 ^ 255 := by
    simpa [hlimit] using h
  exact Reasoning.Theory.slt_lit_zero (a := w) (m := 0) (by decide) (by omega) hhi

theorem endSnipSltOne_of_ge_limit (w : UInt256)
    (h : endFreeInt256LimitWord.toNat ≤ w.toNat) :
    UInt256.slt w (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by native_decide
  have hhi : 2 ^ 255 ≤ w.toNat := by
    simpa [hlimit] using h
  exact Reasoning.Theory.slt_lit_one_high (a := w) (m := 0) (by decide) hhi

theorem endSnipSltNonzero_of_ge_limit (w : UInt256)
    (h : endFreeInt256LimitWord.toNat ≤ w.toNat) :
    UInt256.slt w (UInt256.ofNat 0) ≠ UInt256.ofNat 0 := by
  rw [endSnipSltOne_of_ge_limit w h]
  decide

theorem endSnipSignedFlagPass (w : UInt256)
    (h : w.toNat < endFreeInt256LimitWord.toNat) :
    UInt256.isZero (UInt256.slt w (UInt256.ofNat 0)) ≠ UInt256.ofNat 0 := by
  rw [endSnipSltZero_of_lt_limit w h]
  decide

theorem endSnipSignedFlagFail (w : UInt256)
    (h : endFreeInt256LimitWord.toNat ≤ w.toNat) :
    UInt256.isZero (UInt256.slt w (UInt256.ofNat 0)) = UInt256.ofNat 0 := by
  rw [endSnipSltOne_of_ge_limit w h]
  decide

theorem endX_snip_lot_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSnipSalesLotWord outSales).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2391⟩
      (endSnipAfterAddStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw2425, k2425, C2425, rd2425⟩ :=
    endRuntimeBlocks.endRuntime_block_2391_taken_packed
      (x0 := endSnipArtNewWorldWord world.2 I outVat outSales)
      (x1 := endSnipArtWord outVat outSales)
      (x2 := endSnipSalesUsrWord outSales)
      (x3 := endSnipSalesLotWord outSales)
      (x4 := endSnipSalesTabWord outSales)
      (x5 := endFlowVatIlksRateWord outVat)
      (x6 := endSnipDogIlksClipWord outDog)
      (x7 := endSnipDogIlksClipWord outDog)
      (x8 := endArg1Word I) (x9 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltNonzero_of_ge_limit (endSnipSalesLotWord outSales) hlot)
      (by jump_dest)
      (by simpa [endSnipAfterAddStack] using rd)
  have hslot :=
    endSnipArtHashSlot (endSnipArtHashMem preσ I outDog outVat outSales) I
  have rd2425' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2425⟩
        [UInt256.isZero (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)),
          endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
          endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
          endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
          endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw2425 rdata
        (endSnipArtStoredWorld world I outVat outSales) k2425 C2425 := by
    simpa [endRuntimeBlocks.endRuntime_block_2391_taken_stack,
      endRuntimeBlocks.endRuntime_block_2391_taken_memory, endSnipAfterArtStoreMem,
      endSnipArtStoredWorld, hslot] using rd2425
  obtain ⟨aw2430, k2430, C2430, rd2430⟩ :=
    endRuntimeBlocks.endRuntime_block_2425_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)))
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagFail (endSnipSalesLotWord outSales) hlot)
      rd2425'
  exact endRuntimeBlocks.endRuntime_block_2430
    (R := endRuntimeBlocks.endRuntime_block_2425_fallthrough_stack
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_2425_fallthrough_stack])
    rd2430

theorem endX_snip_art_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSnipArtWord outVat outSales).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2391⟩
      (endSnipAfterAddStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw2419, k2419, C2419, rd2419⟩ :=
    endRuntimeBlocks.endRuntime_block_2391_fallthrough_packed
      (x0 := endSnipArtNewWorldWord world.2 I outVat outSales)
      (x1 := endSnipArtWord outVat outSales)
      (x2 := endSnipSalesUsrWord outSales)
      (x3 := endSnipSalesLotWord outSales)
      (x4 := endSnipSalesTabWord outSales)
      (x5 := endFlowVatIlksRateWord outVat)
      (x6 := endSnipDogIlksClipWord outDog)
      (x7 := endSnipDogIlksClipWord outDog)
      (x8 := endArg1Word I) (x9 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltZero_of_lt_limit (endSnipSalesLotWord outSales) hlot)
      (by simpa [endSnipAfterAddStack] using rd)
  have hslot :=
    endSnipArtHashSlot (endSnipArtHashMem preσ I outDog outVat outSales) I
  have rd2419' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2419⟩
        [UInt256.isZero (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)),
          endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
          endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
          endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
          endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw2419 rdata
        (endSnipArtStoredWorld world I outVat outSales) k2419 C2419 := by
    simpa [endRuntimeBlocks.endRuntime_block_2391_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_2391_fallthrough_memory, endSnipAfterArtStoreMem,
      endSnipArtStoredWorld, hslot] using rd2419
  obtain ⟨aw2425, k2425, C2425, rd2425⟩ :=
    endRuntimeBlocks.endRuntime_block_2419_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)))
      (x1 := endSnipArtWord outVat outSales)
      (R := [endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd2419'
  obtain ⟨aw2430, k2430, C2430, rd2430⟩ :=
    endRuntimeBlocks.endRuntime_block_2425_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSnipArtWord outVat outSales) (UInt256.ofNat 0)))
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagFail (endSnipArtWord outVat outSales) hart)
      (by simpa [endRuntimeBlocks.endRuntime_block_2419_stack] using rd2425)
  exact endRuntimeBlocks.endRuntime_block_2430
    (R := endRuntimeBlocks.endRuntime_block_2425_fallthrough_stack
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_2425_fallthrough_stack])
    rd2430

theorem endX_snip_art_guards_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2391⟩
      (endSnipAfterAddStack world.2 I outDog outVat outSales sel)
      (endSnipArtHashMem preσ I outDog outVat outSales) aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2489⟩
      [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
      (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw' rdata
      (endSnipArtStoredWorld world I outVat outSales) k' C' := by
  obtain ⟨aw2419, k2419, C2419, rd2419⟩ :=
    endRuntimeBlocks.endRuntime_block_2391_fallthrough_packed
      (x0 := endSnipArtNewWorldWord world.2 I outVat outSales)
      (x1 := endSnipArtWord outVat outSales)
      (x2 := endSnipSalesUsrWord outSales)
      (x3 := endSnipSalesLotWord outSales)
      (x4 := endSnipSalesTabWord outSales)
      (x5 := endFlowVatIlksRateWord outVat)
      (x6 := endSnipDogIlksClipWord outDog)
      (x7 := endSnipDogIlksClipWord outDog)
      (x8 := endArg1Word I) (x9 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltZero_of_lt_limit (endSnipSalesLotWord outSales) hlot)
      (by simpa [endSnipAfterAddStack] using rd)
  have hslot :=
    endSnipArtHashSlot (endSnipArtHashMem preσ I outDog outVat outSales) I
  have rd2419' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2419⟩
        [UInt256.isZero (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)),
          endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
          endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
          endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
          endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw2419 rdata
        (endSnipArtStoredWorld world I outVat outSales) k2419 C2419 := by
    simpa [endRuntimeBlocks.endRuntime_block_2391_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_2391_fallthrough_memory, endSnipAfterArtStoreMem,
      endSnipArtStoredWorld, hslot] using rd2419
  obtain ⟨aw2425, k2425, C2425, rd2425⟩ :=
    endRuntimeBlocks.endRuntime_block_2419_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSnipSalesLotWord outSales) (UInt256.ofNat 0)))
      (x1 := endSnipArtWord outVat outSales)
      (R := [endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd2419'
  obtain ⟨aw2489, k2489, C2489, rd2489⟩ :=
    endRuntimeBlocks.endRuntime_block_2425_taken_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSnipArtWord outVat outSales) (UInt256.ofNat 0)))
      (R := [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
        endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagPass (endSnipArtWord outVat outSales) hart)
      (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_2419_stack] using rd2425)
  exact ⟨aw2489, k2489, C2489, by
    simpa [endRuntimeBlocks.endRuntime_block_2425_taken_stack] using rd2489⟩

/-! ### Final `vat.grab` call for `snip(bytes32,uint256)` -/

theorem endSnipAfterArtNewFrame_get_vat_none (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "vat" = none := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "vat") = none
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "vat")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "vat") = none
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "vat") (endSnipArtValue outVat outSales) (by decide)]
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "vat") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "vat") (collapseReturns []) (by decide)]
  exact endSnipAfterUsrFrame_get_vat_none I outDog outVat outSales

theorem endSnipAfterArtNewFrame_get_vow_none (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtNewFrame evm I outDog outVat outSales).locals.get? "vow" = none := by
  change (((endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales))).get? "vow") = none
  rw [store_get_ne (endSnipAfterArtFrame I outDog outVat outSales).locals
    (k := "ArtNew") (a := "vow")
    (endUIntValue (endSnipArtNewWord evm I outVat outSales)) (by decide)]
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "vow") = none
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "vow") (endSnipArtValue outVat outSales) (by decide)]
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "vow") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "vow") (collapseReturns []) (by decide)]
  exact endSnipAfterUsrFrame_get_vow_none I outDog outVat outSales

theorem endEvalVatAddress_snipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales).locals)
    (evm := evm) (slot := vatRef) (er := { base := "vat", steps := [] })
    (wordSlot := UInt256.ofNat 1)
    (endSnipAfterArtNewFrame_get_vat_none baseEvm I outDog outVat outSales)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVowAddress_snipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
        vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  unfold vowAddr
  exact endEvalAddressSlot_cage
    (locals := (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales).locals)
    (evm := evm) (slot := vowRef) (er := { base := "vow", steps := [] })
    (wordSlot := UInt256.ofNat 4)
    (endSnipAfterArtNewFrame_get_vow_none baseEvm I outDog outVat outSales)
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vow)

theorem endEvalVatExtCodeSize_snipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_snipAfterArtNew baseEvm evm I outDog outVat outSales]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_snipAfterArtNew_false (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_snipAfterArtNew baseEvm evm I outDog outVat outSales,
    hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_snipAfterArtNew_true (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_snipAfterArtNew baseEvm evm I outDog outVat outSales]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalSnipCastLotAfterAdd (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (asInt256 (.var "lot")) =
      .ok (.int (Int.ofNat (endSnipSalesLotWord outSales).toNat)) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales)
        evm (.var "lot")
      EvalResult.ofOption EvalError.typeError (castValue? value int256St)) =
    .ok (.int (Int.ofNat (endSnipSalesLotWord outSales).toNat))
  rw [endEvalSnipLotVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [int256St, castValue?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    endSnipLotValue, endUIntValue]

theorem endEvalSnipCastArtAfterAdd (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (asInt256 (.var "art")) =
      .ok (.int (Int.ofNat (endSnipArtWord outVat outSales).toNat)) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales)
        evm (.var "art")
      EvalResult.ofOption EvalError.typeError (castValue? value int256St)) =
    .ok (.int (Int.ofNat (endSnipArtWord outVat outSales).toNat))
  rw [endEvalSnipArtVarAfterAdd baseEvm evm I outDog outVat outSales]
  simp [int256St, castValue?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    endSnipArtValue, endUIntValue]

theorem endEvalSnipGrabArgs (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExprs? config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")] =
    .ok [endArg0Bytes32Value I, endSnipUsrValue outSales,
      .address evm.executionEnv.codeOwner,
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat),
      .int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
      .int (Int.ofNat (endSnipArtWord outVat outSales).toNat)] := by
  simp [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind,
    EvalResult.ofOption, bind, pure, endEvalSnipIlkVarAfterAdd,
    endEvalSnipUsrVarAfterAdd, endEvalVowAddress_snipAfterArtNew,
    endEvalSnipCastLotAfterAdd, endEvalSnipCastArtAfterAdd]

theorem endEncodeABIWord_int256_posWord (w : UInt256)
    (h : w.toNat < endFreeInt256LimitWord.toNat) :
    encodeABIWord? int256 (.int (Int.ofNat w.toNat)) = some w := by
  have hltNat : w.toNat < EVM.twoPow 255 := by
    rw [← endFreeInt256LimitWord_toNat]
    exact h
  simp [int256, int256Int, encodeABIWord?, hltNat]
  exact wordOfInt_ofNat_toNat w

theorem endEncodeInt256_posWord (w : UInt256)
    (h : w.toNat < endFreeInt256LimitWord.toNat) :
    encodeABIValue? int256 (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? int256 (.int (Int.ofNat w.toNat))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE w)
  rw [endEncodeABIWord_int256_posWord w h]
  simp only [bind, Option.bind]

theorem endEncodeAddress_maskedWord (w : UInt256) :
    encodeABIValue? addr (.address (AccountAddress.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land solcAddrMask w)) := by
  rw [solcAddressValue_masked w]
  have hcanon := solcAddrMask_result_canonical w
  have hcanonLeft :
      (UInt256.land solcAddrMask w).toNat < EVM.addressModulus := by
    simpa [u256_land_comm solcAddrMask w] using hcanon
  have haddrMod :
      (UInt256.land solcAddrMask w).toNat % AccountAddress.size =
        (UInt256.land solcAddrMask w).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanonLeft
  have hword : EVM.word (UInt256.land solcAddrMask w).toNat =
      UInt256.land solcAddrMask w :=
    u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

def endSnipGrabPayloadBytes (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outSales : ByteArray) : List UInt8 :=
  (((((EVM.Word.toBytesBE (endArg0Word I) ++
      EVM.Word.toBytesBE (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) ++
      EVM.Word.toBytesBE (endPackVowTarget postσ I)) ++
      EVM.Word.toBytesBE (endSnipSalesLotWord outSales)) ++
      EVM.Word.toBytesBE (endSnipArtWord outVat outSales))

def endSnipGrabEncodedCall (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outSales : ByteArray) : ByteArray :=
  grabSelector ++ ⟨(endSnipGrabPayloadBytes postσ I outVat outSales).toArray⟩

theorem endEncodeABIValues_grab_snip (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    encodeABIValues? [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endSnipUsrValue outSales, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
        .int (Int.ofNat (endSnipArtWord outVat outSales).toNat)] =
      some (endSnipGrabPayloadBytes postσ I outVat outSales) := by
  have hhead : abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
      some 192 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynInt : isDynamicABIType int256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I (by omega : 36 ≤ I.calldata.size), hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [show encodeABIValue? addr (endSnipUsrValue outSales) =
      some (EVM.Word.toBytesBE
        (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))) by
    exact endEncodeAddress_maskedWord (endSnipSalesUsrWord outSales), hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_this_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow postσ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_posWord (endSnipSalesLotWord outSales) hlot, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_posWord (endSnipArtWord outVat outSales) hart, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSnipGrabPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_grab_snip (postσ : AccountMap)
    (I : ExecutionEnv) (outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endSnipUsrValue outSales, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
        .int (Int.ofNat (endSnipArtWord outVat outSales).toNat)] =
      some (endSnipGrabEncodedCall postσ I outVat outSales) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_grab_snip postσ I outVat outSales hsz68 hlot hart]
  simp [endSnipGrabEncodedCall, endSnipGrabPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_grab_snip (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
      [endArg0Bytes32Value I, endSnipUsrValue outSales, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
        .int (Int.ofNat (endSnipArtWord outVat outSales).toNat)] =
      some (endSnipGrabEncodedCall postσ I outVat outSales) := by
  rw [endExternalEncode_grab_branch]
  exact endEncodeCallWithSelector_grab_snip postσ I outVat outSales hsz68 hlot hart

abbrev endSnipGrabSelectorWord : UInt256 := endFreeGrabSelectorWord

abbrev endSnipGrabSelectorEncodedWord : UInt256 := endFreeGrabSelectorEncodedWord

theorem endSnipArtHashMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipArtHashMem preσ I outDog outVat outSales).size =
      (endSnipYankCallMem preσ I outDog outVat outSales).size := by
  have hbase : 64 ≤ (endSnipYankCallMem preσ I outDog outVat outSales).size := by
    rw [endSnipYankCallMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  simpa [endSnipArtHashMem, endRuntimeBlocks.endRuntime_block_2361_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 14) hbase

theorem endSnipArtHashMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipArtHashMem preσ I outDog outVat outSales).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hbase : 96 ≤ (endSnipYankCallMem preσ I outDog outVat outSales).size := by
    rw [endSnipYankCallMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  have hread := endSnipYankCallMem_read64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  simpa [endSnipArtHashMem, endRuntimeBlocks.endRuntime_block_2361_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 14) hbase hread

theorem endSnipAfterArtStoreMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipAfterArtStoreMem preσ I outDog outVat outSales).size =
      (endSnipArtHashMem preσ I outDog outVat outSales).size := by
  have hbase : 64 ≤ (endSnipArtHashMem preσ I outDog outVat outSales).size := by
    rw [endSnipArtHashMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    rw [endSnipYankCallMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  simpa [endSnipAfterArtStoreMem, endRuntimeBlocks.endRuntime_block_2391_taken_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 14) hbase

theorem endSnipAfterArtStoreMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipAfterArtStoreMem preσ I outDog outVat outSales).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hbase : 96 ≤ (endSnipArtHashMem preσ I outDog outVat outSales).size := by
    rw [endSnipArtHashMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    rw [endSnipYankCallMem_size preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  have hread := endSnipArtHashMem_read64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  simpa [endSnipAfterArtStoreMem, endRuntimeBlocks.endRuntime_block_2391_taken_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 14) hbase hread

theorem endSnipAfterArtStoreMem_mload64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 64) (endSnipAfterArtStoreMem preσ I outDog outVat outSales) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endSnipAfterArtStoreMem preσ I outDog outVat outSales)
    (by
      rw [endSnipAfterArtStoreMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      rw [endSnipArtHashMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      rw [endSnipYankCallMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (endSnipAfterArtStoreMem_read64 preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)

abbrev endSnipGrabMemSel (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  endSnipGrabSelectorEncodedWord.toByteArray.write 0
    (endSnipAfterArtStoreMem preσ I outDog outVat outSales) 128 32

abbrev endSnipGrabMemIlk (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endArg0Word I).toByteArray.write 0
    (endSnipGrabMemSel preσ I outDog outVat outSales) 132 32

abbrev endSnipGrabMemUsr (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales)).toByteArray.write 0
    (endSnipGrabMemIlk preσ I outDog outVat outSales) 164 32

abbrev endSnipGrabMemThis (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196 32

abbrev endSnipGrabMemVow (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endPackVowTarget postσ I).toByteArray.write 0
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228 32

abbrev endSnipGrabMemLot (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endSnipSalesLotWord outSales).toByteArray.write 0
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 32

abbrev endSnipGrabMemFull (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endSnipArtWord outVat outSales).toByteArray.write 0
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 32

abbrev endSnipGrabCallMem (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_2489_memory
    (ee := I) (mem := endSnipAfterArtStoreMem preσ I outDog outVat outSales)
    (σ := postσ) (x0 := endSnipArtWord outVat outSales)
    (x1 := endSnipSalesUsrWord outSales) (x2 := endSnipSalesLotWord outSales)
    (x8 := endArg0Word I)

theorem endSnipGrabCallMem_eq_full (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    endSnipGrabCallMem preσ postσ I outDog outVat outSales =
      endSnipGrabMemFull preσ postσ I outDog outVat outSales := by
  have hfreeCall := endSnipAfterArtStoreMem_mload64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endSnipGrabCallMem endSnipGrabMemFull endSnipGrabMemLot endSnipGrabMemVow
    endSnipGrabMemThis endSnipGrabMemUsr endSnipGrabMemIlk endSnipGrabMemSel
    endSnipGrabSelectorEncodedWord endFreeGrabSelectorEncodedWord endPackVowTarget
  dsimp [endRuntimeBlocks.endRuntime_block_2489_memory]
  rw [hfreeCall]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
  rw [hmaskGenerated]
  rfl

theorem endSnipGrabMemSel_size_ge160 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    160 ≤ (endSnipGrabMemSel preσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded endSnipGrabSelectorEncodedWord
    (endSnipAfterArtStoreMem preσ I outDog outVat outSales) 128

theorem endSnipGrabMemIlk_size_ge164 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    164 ≤ (endSnipGrabMemIlk preσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endSnipGrabMemSel preσ I outDog outVat outSales) 132

theorem endSnipGrabMemUsr_size_ge196 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    196 ≤ (endSnipGrabMemUsr preσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))
    (endSnipGrabMemIlk preσ I outDog outVat outSales) 164

theorem endSnipGrabMemThis_size_ge228 (preσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    228 ≤ (endSnipGrabMemThis preσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196

theorem endSnipGrabMemVow_size_ge260 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    260 ≤ (endSnipGrabMemVow preσ postσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228

theorem endSnipGrabMemLot_size_ge292 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    292 ≤ (endSnipGrabMemLot preσ postσ I outDog outVat outSales).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260

theorem endSnipGrabCallMem_size_ge324 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    324 ≤ (endSnipGrabCallMem preσ postσ I outDog outVat outSales).size := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292

theorem endSnipGrabCallMem_read64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 64
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 64
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228 64
    (by have := endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196 64
    (by have := endSnipGrabMemUsr_size_ge196 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))
    (endSnipGrabMemIlk preσ I outDog outVat outSales) 164 64
    (by have := endSnipGrabMemIlk_size_ge164 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg0Word I)
    (endSnipGrabMemSel preσ I outDog outVat outSales) 132 64
    (by have := endSnipGrabMemSel_size_ge160 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSnipGrabSelectorEncodedWord
    (endSnipAfterArtStoreMem preσ I outDog outVat outSales) 128 64
    (by
      rw [endSnipAfterArtStoreMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      rw [endSnipArtHashMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      rw [endSnipYankCallMem_size preσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  exact endSnipAfterArtStoreMem_read64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192

theorem endSnipGrabCallMem_mload64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 64) (endSnipGrabCallMem preσ postσ I outDog outVat outSales) =
      ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥
        (endSnipGrabCallMem preσ postσ I outDog outVat outSales).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endSnipGrabCallMem preσ postσ I outDog outVat outSales)
    (by
      have hge := endSnipGrabCallMem_size_ge324 preσ postσ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192
      change 64 < (endSnipGrabCallMem preσ postσ I outDog outVat outSales).size
      omega)
    (endSnipGrabCallMem_read64 preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)

theorem endSnipGrabSelectorEncodedWord_prefix :
    (endSnipGrabSelectorEncodedWord.toByteArray).extract 0 4 = grabSelector := by
  exact endFreeGrabSelectorEncodedWord_prefix

theorem endSnipGrabCallMem_readSelector (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 128 4 =
      grabSelector := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [write32_read_below_len _ _ 292 128 4 (by rw [toByteArray_size])
    (endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales) (by omega)
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size])
    (endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales) (by omega)
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales) (by omega)
    (by have := endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endSnipGrabMemUsr_size_ge196 preσ I outDog outVat outSales) (by omega)
    (by have := endSnipGrabMemUsr_size_ge196 preσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endSnipGrabMemIlk_size_ge164 preσ I outDog outVat outSales) (by omega)
    (by have := endSnipGrabMemIlk_size_ge164 preσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endSnipGrabMemSel_size_ge160 preσ I outDog outVat outSales; omega)
    (by omega)
    (by have := endSnipGrabMemSel_size_ge160 preσ I outDog outVat outSales; omega)
    (by decide) (by decide)]
  change ((endSnipGrabSelectorEncodedWord.toByteArray.write 0
      (endSnipAfterArtStoreMem preσ I outDog outVat outSales) 128 32).readWithPadding
        128 4) = grabSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSnipGrabSelectorEncodedWord (endSnipAfterArtStoreMem preσ I outDog outVat outSales)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSnipGrabSelectorEncodedWord_prefix]

theorem endSnipGrabCallMem_readIlk (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 132
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 132
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228 132
    (by have := endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196 132
    (by have := endSnipGrabMemUsr_size_ge196 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))
    (endSnipGrabMemIlk preσ I outDog outVat outSales) 164 132
    (by have := endSnipGrabMemIlk_size_ge164 preσ I outDog outVat outSales; omega)
    (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      (endSnipGrabMemSel preσ I outDog outVat outSales) 132 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I)
    (endSnipGrabMemSel preσ I outDog outVat outSales) 132

theorem endSnipGrabCallMem_readUsr (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 164 32 =
      (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales)).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 164
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 164
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228 164
    (by have := endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196 164
    (by have := endSnipGrabMemUsr_size_ge196 preσ I outDog outVat outSales; omega)
    (by omega)]
  change (((UInt256.land solcAddrMask (endSnipSalesUsrWord outSales)).toByteArray.write 0
      (endSnipGrabMemIlk preσ I outDog outVat outSales) 164 32).readWithPadding
        164 32) =
    (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales)).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land solcAddrMask (endSnipSalesUsrWord outSales))
    (endSnipGrabMemIlk preσ I outDog outVat outSales) 164

theorem endSnipGrabCallMem_readThis (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 196 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 196
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 196
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228 196
    (by have := endSnipGrabMemThis_size_ge228 preσ I outDog outVat outSales; omega)
    (by omega)]
  change (((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (endSnipGrabMemUsr preσ I outDog outVat outSales) 196 32).readWithPadding 196 32) =
    (UInt256.ofNat I.codeOwner.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSnipGrabMemUsr preσ I outDog outVat outSales) 196

theorem endSnipGrabCallMem_readVow (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 228 32 =
      (endPackVowTarget postσ I).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 228
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 228
    (by have := endSnipGrabMemVow_size_ge260 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  change (((endPackVowTarget postσ I).toByteArray.write 0
      (endSnipGrabMemThis preσ I outDog outVat outSales) 228 32).readWithPadding 228 32) =
    (endPackVowTarget postσ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget postσ I)
    (endSnipGrabMemThis preσ I outDog outVat outSales) 228

theorem endSnipGrabCallMem_readLot (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 260 32 =
      (endSnipSalesLotWord outSales).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 260
    (by have := endSnipGrabMemLot_size_ge292 preσ postσ I outDog outVat outSales; omega)
    (by omega)]
  change (((endSnipSalesLotWord outSales).toByteArray.write 0
      (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260 32).readWithPadding
        260 32) =
    (endSnipSalesLotWord outSales).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endSnipSalesLotWord outSales)
    (endSnipGrabMemVow preσ postσ I outDog outVat outSales) 260

theorem endSnipGrabCallMem_readArt (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 292 32 =
      (endSnipArtWord outVat outSales).toByteArray := by
  rw [endSnipGrabCallMem_eq_full preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  change (((endSnipArtWord outVat outSales).toByteArray.write 0
      (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292 32).readWithPadding
        292 32) =
    (endSnipArtWord outVat outSales).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endSnipArtWord outVat outSales)
    (endSnipGrabMemLot preσ postσ I outDog outVat outSales) 292

theorem endSnipGrabCallMem_readCallData (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales).readWithPadding 128 196 =
      endSnipGrabEncodedCall postσ I outVat outSales := by
  have hsize := endSnipGrabCallMem_size_ge324 preσ postσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  rw [show 196 = 4 + 192 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 128 4 192
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 192 = 32 + 160 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 132 32 160
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 160 = 32 + 128 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 164 32 128
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [show 128 = 32 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 196 32 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 196 + 32 = 228 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 228 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 228 + 32 = 260 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipGrabCallMem preσ postσ I outDog outVat outSales) 260 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 260 + 32 = 292 by norm_num]
  rw [endSnipGrabCallMem_readSelector preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readIlk preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readUsr preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readThis preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readVow preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readLot preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipGrabCallMem_readArt preσ postσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSnipGrabEncodedCall, endSnipGrabPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endSnipGrabGateRest (I : ExecutionEnv) (sel : UInt256)
    (outDog outVat outSales : ByteArray) : List UInt256 :=
  [endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
    endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
    endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
    endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipGrabGateStack (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outDog outVat outSales : ByteArray) : List UInt256 :=
  [⟨196⟩, ⟨196⟩, ⟨128⟩, ⟨128⟩, endSnipGrabSelectorWord,
    endPackVatTarget postσ I] ++ endSnipGrabGateRest I sel outDog outVat outSales

abbrev endSnipGrabCallRest (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outDog outVat outSales : ByteArray) : List UInt256 :=
  [⟨324⟩, endSnipGrabSelectorWord, endPackVatTarget postσ I] ++
    endSnipGrabGateRest I sel outDog outVat outSales

abbrev endSnipGrabCallStack (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outDog outVat outSales : ByteArray) : List UInt256 :=
  [endPackVatTarget postσ I, ⟨0⟩, ⟨128⟩, ⟨196⟩, ⟨128⟩, ⟨0⟩] ++
    endSnipGrabCallRest postσ I sel outDog outVat outSales

abbrev endSnipGrabCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (rdata outDog outVat outSales : ByteArray) : Cursor :=
  { pc := ⟨2605⟩, stack := endSnipGrabCallStack world.2 I sel outDog outVat outSales,
    mem := endSnipGrabCallMem preσ world.2 I outDog outVat outSales, aw := aw,
    rdata := rdata, world := world }

abbrev endSnipGrabCallAw (aw : UInt256) : UInt256 :=
  endFreeGrabCallAw aw

theorem endX_snip_after_guards_to_grab_gate {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2489⟩
      (endSnipGrabGateRest I sel outDog outVat outSales)
      (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (endSnipGrabGateStack world.2 I sel outDog outVat outSales)
      (endSnipGrabCallMem preσ world.2 I outDog outVat outSales) aw' rdata
      world k' C' := by
  obtain ⟨aw2574, k2574, C2574, rd2574⟩ :=
    endRuntimeBlocks.endRuntime_block_2489_packed
      (x0 := endSnipArtWord outVat outSales)
      (x1 := endSnipSalesUsrWord outSales)
      (x2 := endSnipSalesLotWord outSales)
      (x3 := endSnipSalesTabWord outSales)
      (x4 := endFlowVatIlksRateWord outVat)
      (x5 := endSnipDogIlksClipWord outDog)
      (x6 := endSnipDogIlksClipWord outDog)
      (x7 := endArg1Word I) (x8 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by simpa [endSnipGrabGateRest] using rd)
  have hpreMload := endSnipAfterArtStoreMem_mload64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hcallMload := endSnipGrabCallMem_mload64 preσ world.2 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endPackVatTarget world.2 I := by
    rw [hmaskGenerated, u256_land_comm]
  have hstack2574 :
      endRuntimeBlocks.endRuntime_block_2489_stack (ee := I)
          (mem := endSnipAfterArtStoreMem preσ I outDog outVat outSales)
          (σ := world.2)
          (x0 := endSnipArtWord outVat outSales)
          (x1 := endSnipSalesUsrWord outSales)
          (x2 := endSnipSalesLotWord outSales)
          (x3 := endSnipSalesTabWord outSales)
          (x4 := endFlowVatIlksRateWord outVat)
          (x5 := endSnipDogIlksClipWord outDog)
          (x6 := endSnipDogIlksClipWord outDog)
          (x7 := endArg1Word I) (x8 := endArg0Word I)
          (R := [⟨562⟩, sel]) =
        endSnipGrabGateStack world.2 I sel outDog outVat outSales := by
    have hcallMloadRaw := hcallMload
    dsimp [endSnipGrabCallMem, endRuntimeBlocks.endRuntime_block_2489_memory] at hcallMloadRaw
    rw [hpreMload] at hcallMloadRaw
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide] at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
      at hcallMloadRaw
    dsimp [endRuntimeBlocks.endRuntime_block_2489_stack, endSnipGrabGateStack,
      endSnipGrabGateRest, endSnipGrabSelectorWord, endFreeGrabSelectorWord]
    rw [htarget, hpreMload]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
    rw [hcallMloadRaw]
    rw [show UInt256.ofNat 196 = (⟨196⟩ : UInt256) from by native_decide]
  exact ⟨aw2574, k2574, C2574, by
    simpa [hstack2574, endSnipGrabCallMem] using rd2574⟩

theorem endX_snip_grab_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2489⟩
      (endSnipGrabGateRest I sel outDog outVat outSales)
      (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw2574, k2574, C2574, rd2574⟩ :=
    endX_snip_after_guards_to_grab_gate
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
      (rdata := rdata) (outDog := outDog) (outVat := outVat) (outSales := outSales)
      (world := world) houtDog h128 houtVat h160 houtSales h192 rd
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hvatNoCode]
    native_decide
  obtain ⟨aw2599, k2599, C2599, rd2599⟩ :=
    endRuntimeBlocks.endRuntime_block_2574_fallthrough_packed
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSnipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSnipGrabGateRest I sel outDog outVat outSales)
      (by simp [endSnipGrabGateRest]) hcondCode
      (by simpa [endSnipGrabGateStack] using rd2574)
  exact endRuntimeBlocks.endRuntime_block_2599
    (R := endRuntimeBlocks.endRuntime_block_2574_fallthrough_stack (σ := world.2)
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSnipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSnipGrabGateRest I sel outDog outVat outSales))
    (by simp [endRuntimeBlocks.endRuntime_block_2574_fallthrough_stack,
      endSnipGrabGateRest])
    rd2599

theorem endX_snip_to_grab_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2489⟩
      (endSnipGrabGateRest I sel outDog outVat outSales)
      (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw rdata world k C) :
    ∃ awNext kNext CNext, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2605⟩
      (endSnipGrabCallStack world.2 I sel outDog outVat outSales)
      (endSnipGrabCallMem preσ world.2 I outDog outVat outSales) awNext rdata
      world kNext CNext := by
  obtain ⟨aw2574, k2574, C2574, rd2574⟩ :=
    endX_snip_after_guards_to_grab_gate
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
      (rdata := rdata) (outDog := outDog) (outVat := outVat) (outSales := outSales)
      (world := world) houtDog h128 houtVat h160 houtSales h192 rd
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw2603, k2603, C2603, rd2603⟩ :=
    endRuntimeBlocks.endRuntime_block_2574_taken_packed
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSnipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSnipGrabGateRest I sel outDog outVat outSales)
      (by simp [endSnipGrabGateRest]) hcondCode (by jump_dest)
      (by simpa [endSnipGrabGateStack] using rd2574)
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + (⟨196⟩ : UInt256) =
      ⟨196⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + (⟨196⟩ : UInt256) = ⟨324⟩ := by
    native_decide
  have hstack2603 :
      endRuntimeBlocks.endRuntime_block_2574_taken_stack (σ := world.2)
          (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
          (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
          (x4 := endSnipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
          (R := endSnipGrabGateRest I sel outDog outVat outSales) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSnipGrabCallStack world.2 I sel outDog outVat outSales := by
    dsimp [endRuntimeBlocks.endRuntime_block_2574_taken_stack,
      endSnipGrabCallStack, endSnipGrabCallRest, endSnipGrabGateRest]
    rw [hlen, hend]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide]
  have rd2603Ok :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2603⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSnipGrabCallStack world.2 I sel outDog outVat outSales)
        (endSnipGrabCallMem preσ world.2 I outDog outVat outSales) aw2603 rdata
        world k2603 C2603 := by
    simpa [hstack2603] using rd2603
  obtain ⟨aw2605, k2605, C2605, rd2605⟩ :=
    endRuntimeBlocks.endRuntime_block_2603_packed
      (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
      (R := endSnipGrabCallStack world.2 I sel outDog outVat outSales)
      (by simp [endSnipGrabCallStack, endSnipGrabCallRest, endSnipGrabGateRest])
      rd2603Ok
  exact ⟨aw2605, k2605, C2605, by
    simpa [endRuntimeBlocks.endRuntime_block_2603_stack] using rd2605⟩

theorem endSnipGrabExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C baseEvm evm}
    {preσ : AccountMap} {outDog outVat outSales : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipGrabCallCursor world preσ I sel aw rdata outDog outVat outSales)
      k C (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr,
            asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨2605⟩ = some (.GAS, .none); decide)
    (by simp [endSnipGrabCallCursor, endSnipGrabCallStack, endSnipGrabCallRest,
      endSnipGrabGateRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I, endSnipUsrValue outSales, .address I.codeOwner,
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
      .int (Int.ofNat (endSnipArtWord outVat outSales).toNat)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨2606⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSnipGrabCallRest, endSnipGrabGateRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_snipAfterArtNew baseEvm evm I outDog outVat outSales]
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
    rw [endEvalSnipGrabArgs baseEvm evm I outDog outVat outSales]
    rw [h.env]
    change EvalResult.ok
      [endArg0Bytes32Value I, endSnipUsrValue outSales, Value.address I.codeOwner,
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        Value.int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
        Value.int (Int.ofNat (endSnipArtWord outVat outSales).toNat)] =
      EvalResult.ok
        [endArg0Bytes32Value I, endSnipUsrValue outSales, Value.address I.codeOwner,
          Value.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          Value.int (Int.ofNat (endSnipSalesLotWord outSales).toNat),
          Value.int (Int.ofNat (endSnipArtWord outVat outSales).toNat)]
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
    rw [endExternalEncode_grab_snip world.2 I outVat outSales hsz68 hlot hart]
    change some (endSnipGrabEncodedCall world.2 I outVat outSales) =
      some ((endSnipGrabCallMem preσ world.2 I outDog outVat outSales).readWithPadding 128 196)
    rw [endSnipGrabCallMem_readCallData preσ world.2 I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  · intro out evmNext worldNext kNext CNext
    dsimp only
    intro _ _
    rw [endExternalDecode_grab out]
    intro rd hrel
    have rd2607 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2607⟩
          ((⟨1⟩ : UInt256) :: endSnipGrabCallRest world.2 I sel outDog outVat outSales)
          (endSnipGrabCallMem preσ world.2 I outDog outVat outSales)
          (endSnipGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipGrabCallCursor,
        endSnipGrabCallStack, endSnipGrabCallRest, endSnipGrabGateRest,
        endSnipGrabCallAw] using rd
    have rd2623 := endRuntimeBlocks.endRuntime_block_2607_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endSnipGrabCallRest world.2 I sel outDog outVat outSales)
      (by simp [endSnipGrabCallRest, endSnipGrabGateRest])
      (by native_decide) (by jump_dest) rd2607
    have rd562 := endRuntimeBlocks.endRuntime_block_2623
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨324⟩ : UInt256))
      (x2 := endSnipGrabSelectorWord) (x3 := endPackVatTarget world.2 I)
      (x4 := endSnipArtWord outVat outSales)
      (x5 := endSnipSalesUsrWord outSales)
      (x6 := endSnipSalesLotWord outSales)
      (x7 := endSnipSalesTabWord outSales)
      (x8 := endFlowVatIlksRateWord outVat)
      (x9 := endSnipDogIlksClipWord outDog)
      (x10 := endSnipDogIlksClipWord outDog)
      (x11 := endArg1Word I) (x12 := endArg0Word I)
      (x13 := (⟨562⟩ : UInt256)) (R := [sel])
      (by simp) hperm (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_2607_taken_stack,
          endSnipGrabCallRest, endSnipGrabGateRest] using rd2623)
    have rdret := endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp) rd562
    exact BlockProgress.ofRDret ExecBlock.nil rdret
      (by simpa using hrel.created.symm)
      (by simpa using hrel.accounts)
      abiVoidFallthrough
  · intro out worldNext kNext CNext
    dsimp only
    intro rd
    have rd2607 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2607⟩
          ((⟨0⟩ : UInt256) :: endSnipGrabCallRest world.2 I sel outDog outVat outSales)
          (endSnipGrabCallMem preσ world.2 I outDog outVat outSales)
          (endSnipGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipGrabCallCursor,
        endSnipGrabCallStack, endSnipGrabCallRest, endSnipGrabGateRest,
        endSnipGrabCallAw] using rd
    have rd2614 := endRuntimeBlocks.endRuntime_block_2607_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endSnipGrabCallRest world.2 I sel outDog outVat outSales)
      (by simp [endSnipGrabCallRest, endSnipGrabGateRest])
      (by native_decide) rd2607
    exact endRuntimeBlocks.endRuntime_block_2614
      (R := endRuntimeBlocks.endRuntime_block_2607_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256))
        (R := endSnipGrabCallRest world.2 I sel outDog outVat outSales))
      (by simp [endRuntimeBlocks.endRuntime_block_2607_fallthrough_stack,
        endSnipGrabCallRest, endSnipGrabGateRest])
      rd2614

theorem endSnipGrabCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preσ : AccountMap} {baseEvm : EVM.State}
    {outDog outVat outSales : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hlot : (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨2489⟩
      (fun cur frame e =>
        frame = endSnipAfterArtNewFrame baseEvm I outDog outVat outSales ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.stack = endSnipGrabGateRest I sel outDog outVat outSales ∧
        cur.mem = endSnipAfterArtStoreMem preσ I outDog outVat outSales ∧
        cur.aw = aw)
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")]
        "_grab")
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hstack, hmem, haw⟩
  cases hframe
  have rd2489 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2489⟩
        (endSnipGrabGateRest I sel outDog outVat outSales)
        (endSnipAfterArtStoreMem preσ I outDog outVat outSales) aw cur.rdata
        cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hslotVat := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
  rw [hrel.env] at hslotVat
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) := by
    rw [hrel.env, hslotVat]
    have htarget :
        UInt256.land (storageRead I.codeOwner cur.world.2 (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur.world.2 I := by
      simp [endPackVatTarget, u256_land_comm]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endPackVatTarget cur.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hsource :
        ExecBlock config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
          (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", .var "usr", thisAddr, vowAddr,
              asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_snipAfterArtNew_false baseEvm evm
              I outDog outVat outSales hsrcNoCode)))
    have hrev := endX_snip_grab_no_code
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
      (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
      (outSales := outSales) (world := cur.world)
      houtDog h128 houtVat h160 houtSales h192 hvatNoCode rd2489
    exact BlockProgress.ofRDrev hsource hrev
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hrequire :
        ExecBlock config (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_snipAfterArtNew_true baseEvm evm
            I outDog outVat outSales hsrcCode))
        ExecBlock.nil
    obtain ⟨aw2605, k2605, C2605, rd2605⟩ :=
      endX_snip_to_grab_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
        (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
        (outSales := outSales) (world := cur.world)
        houtDog h128 houtVat h160 houtSales h192 hvatNoCode rd2489
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipGrabCallCursor cur.world preσ I sel aw2605 cur.rdata
            outDog outVat outSales)
          k2605 C2605 (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "usr", thisAddr, vowAddr,
                asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
          (runtimeExit (.abi [])) :=
      endSnipGrabExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw2605)
        (rdata := cur.rdata) (k := k2605) (C := C2605)
        (baseEvm := baseEvm) (evm := evm) (preσ := preσ)
        (outDog := outDog) (outVat := outVat) (outSales := outSales)
        (world := cur.world)
        hperm hsz68 houtDog h128 houtVat h160 houtSales h192 hlot hart
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "usr", thisAddr, vowAddr,
                asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
          (runtimeExit (.abi [])) :=
      htail (by simpa [endSnipGrabCallCursor] using rd2605) hrel
    have hprogress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterArtNewFrame baseEvm I outDog outVat outSales) evm
          ([ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
            [ .externalCall (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "usr", thisAddr, vowAddr,
                  asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ])
          (runtimeExit (.abi [])) :=
      BlockProgress.prepend hrequire htailProgress
    simpa [checkedExternalCallStmts] using hprogress

def endSnipGrabCheckedStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
    [.var "ilk", .var "usr", thisAddr, vowAddr,
      asInt256 (.var "lot"), asInt256 (.var "art")]
    "_grab"

def endSnipAfterYankArtAddStmts : List Stmt :=
  [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
    .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew" ]

def endSnipAfterYankPrefixStmts : List Stmt :=
  endSnipAfterYankArtAddStmts ++ endSnipAfterAddStoreGuardStmts

def endSnipAfterYankSuffixStmts : List Stmt :=
  endSnipAfterYankPrefixStmts ++ endSnipGrabCheckedStmts

def endSnipAfterSuckYankStmts : List Stmt :=
  checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank"

def endSnipAfterSalesSuckStmts : List Stmt :=
  [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
    .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
    .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck"

def endSnipAfterSalesToYankStmts : List Stmt :=
  endSnipAfterSalesSuckStmts ++ endSnipAfterSuckYankStmts

def endSnipAfterVatIlksSalesStmts : List Stmt :=
  [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
    checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
      "clipSale" (perm := false)

def endSnipAfterVatIlksToYankStmts : List Stmt :=
  endSnipAfterVatIlksSalesStmts ++ endSnipAfterSalesToYankStmts

def endSnipAfterDogIlksVatIlksStmts : List Stmt :=
  [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
    checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
      [.var "ilk"] "vatIlk"

def endSnipAfterDogIlksToYankStmts : List Stmt :=
  endSnipAfterDogIlksVatIlksStmts ++ endSnipAfterVatIlksToYankStmts

set_option maxHeartbeats 12000000 in
theorem endSnipAfterYankSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (hpc : cur.pc = ⟨2346⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP : endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog
      cur frame evm) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSnipAfterYankSuffixStmts (runtimeExit (.abi [])) ∨
      (ExecBlock config frame evm endSnipAfterYankSuffixStmts .reverted ∧
        RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with
    ⟨preσ, outVat, outSales, awYank, hframe, hrel, houtVat, h160,
      houtSales, h192, hstack, hmem, haw⟩
  cases hframe
  have rd2346 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2346⟩
        (endSnipAfterYankStack preσ I outDog outVat outSales sel)
        (endSnipYankCallMem preσ I outDog outVat outSales) (endSnipYankCallAw awYank)
        cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  by_cases hrateZero : endFlowVatIlksRateWord outVat = ⟨0⟩
  · have hsource :
        ExecBlock config (endSnipAfterYankFrame I outDog outVat outSales) evm
          endSnipAfterYankSuffixStmts .reverted := by
      simpa [endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
        endSnipAfterYankArtAddStmts] using
        (ExecBlock.consRevert
          (endLetSnipArtRevert evm I outDog outVat outSales hrateZero))
    have hinv := endX_snip_after_yank_rate_invalid
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := endSnipYankCallAw awYank)
      (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
      (outSales := outSales) (world := cur.world) (k := k) (C := C)
      hrateZero rd2346
    exact Or.inr ⟨hsource, hinv⟩
  · have hsourceLet := endLetSnipArt evm I outDog outVat outSales hrateZero
    obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
      endX_snip_after_yank_to_add
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preσ := preσ) (sel := sel)
        (aw := endSnipYankCallAw awYank) (rdata := cur.rdata)
        (outDog := outDog) (outVat := outVat) (outSales := outSales)
        (world := cur.world) (k := k) (C := C) hrateZero rd2346
    have hArtEq := endFlowArtWord_eq_world_of_callRel hrel (by omega : 36 ≤ I.calldata.size)
    by_cases hfit :
        (endFlowArtWorldWord cur.world.2 I).toNat +
          (endSnipArtWord outVat outSales).toNat < UInt256.size
    · have hfitSource :
          (endFlowArtWord evm I).toNat +
            (endSnipArtWord outVat outSales).toNat < UInt256.size := by
        simpa [hArtEq] using hfit
      have hsourceAdd :=
        endSnipInternalAddOk evm I outDog outVat outSales hsz68 hfitSource
      obtain ⟨aw2391, k2391, C2391, rd2391⟩ :=
        endX_snip_art_add_ok
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw10092)
          (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
          (outSales := outSales) (world := cur.world) (k := k10092)
          (C := C10092) hfit rd10092
      by_cases hlot :
          (endSnipSalesLotWord outSales).toNat < endFreeInt256LimitWord.toNat
      · by_cases hart :
            (endSnipArtWord outVat outSales).toNat < endFreeInt256LimitWord.toNat
        · have hsourceStore :=
            endSnipAfterAddStoreGuardOk evm I outDog outVat outSales hsz68 hlot hart
          obtain ⟨aw2489, k2489, C2489, rd2489⟩ :=
            endX_snip_art_guards_ok
              (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (preσ := preσ) (sel := sel)
              (aw := aw2391) (rdata := cur.rdata) (outDog := outDog)
              (outVat := outVat) (outSales := outSales) (world := cur.world)
              (k := k2391) (C := C2391) hperm hlot hart rd2391
          have hsourcePrefix :
              ExecBlock config (endSnipAfterYankFrame I outDog outVat outSales) evm
                endSnipAfterYankPrefixStmts
                (.ok (endSnipAfterArtNewFrame evm I outDog outVat outSales)
                  (endSnipAfterArtNewState evm I outVat outSales)) := by
            simpa [endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts] using
              (ExecBlock.consNormal hsourceLet
                (ExecBlock.consNormal hsourceAdd hsourceStore))
          have hNewEq :
              endSnipArtNewWord evm I outVat outSales =
                endSnipArtNewWorldWord cur.world.2 I outVat outSales := by
            simp [endSnipArtNewWord, endSnipArtNewWorldWord, hArtEq]
          have hstored :=
            hrel.storageStore_codeOwner (ArtSlot (endArg0Bytes32Key I))
              (endSnipArtNewWord evm I outVat outSales)
          have hrelPost :
              CallStateRel (initState cA gh bl σ σ₀ g A I) I
                (endSnipArtStoredWorld cur.world I outVat outSales)
                (endSnipAfterArtNewState evm I outVat outSales) := by
            simpa [endSnipArtStoredWorld, endSnipAfterArtNewState, storageWrite,
              hNewEq, endFlowArtWorldSlot, endArtSlot_eq I (by omega : 36 ≤ I.calldata.size)]
              using hstored
          have htailProgress :
              BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
                (endSnipAfterArtNewFrame evm I outDog outVat outSales)
                (endSnipAfterArtNewState evm I outVat outSales)
                endSnipGrabCheckedStmts (runtimeExit (.abi [])) := by
            simpa [endSnipGrabCheckedStmts] using
              endSnipGrabCheckedCallRefines
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := sel) (aw := aw2489)
                (preσ := preσ) (baseEvm := evm) (outDog := outDog)
                (outVat := outVat) (outSales := outSales)
                hperm hsz68 houtDog h128 houtVat h160 houtSales h192 hlot hart
                { pc := ⟨2489⟩,
                  stack := endSnipGrabGateRest I sel outDog outVat outSales,
                  mem := endSnipAfterArtStoreMem preσ I outDog outVat outSales,
                  aw := aw2489,
                  rdata := cur.rdata,
                  world := endSnipArtStoredWorld cur.world I outVat outSales }
                k2489 C2489
                (endSnipAfterArtNewFrame evm I outDog outVat outSales)
                (endSnipAfterArtNewState evm I outVat outSales)
                rfl rd2489 ⟨rfl, hrelPost, rfl, rfl, rfl⟩
          exact Or.inl <| by
            simpa [endSnipAfterYankSuffixStmts] using
              BlockProgress.prepend hsourcePrefix htailProgress
        · have hartGe :
              endFreeInt256LimitWord.toNat ≤ (endSnipArtWord outVat outSales).toNat := by
            omega
          have hguard :=
            endSnipAfterAddStoreGuardArtRevert evm I outDog outVat outSales hsz68 hlot hartGe
          have hguardFull :
              ExecBlock config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
                (endSnipAfterAddStoreGuardStmts ++ endSnipGrabCheckedStmts) .reverted :=
            Reasoning.Theory.execBlock_append_term hguard (by intros; intro h; cases h)
          have hsourceFull :
              ExecBlock config (endSnipAfterYankFrame I outDog outVat outSales) evm
                endSnipAfterYankSuffixStmts .reverted := by
            simpa [endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
              endSnipAfterYankArtAddStmts, List.append_assoc] using
              (ExecBlock.consNormal hsourceLet
                (ExecBlock.consNormal hsourceAdd hguardFull))
          have hrev := endX_snip_art_guard_fail
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw2391)
            (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
            (outSales := outSales) (world := cur.world) (k := k2391) (C := C2391)
            hperm hlot hartGe rd2391
          exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)
      · have hlotGe :
            endFreeInt256LimitWord.toNat ≤ (endSnipSalesLotWord outSales).toNat := by
          omega
        have hguard :=
          endSnipAfterAddStoreGuardLotRevert evm I outDog outVat outSales hsz68 hlotGe
        have hguardFull :
            ExecBlock config (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm
              (endSnipAfterAddStoreGuardStmts ++ endSnipGrabCheckedStmts) .reverted :=
          Reasoning.Theory.execBlock_append_term hguard (by intros; intro h; cases h)
        have hsourceFull :
            ExecBlock config (endSnipAfterYankFrame I outDog outVat outSales) evm
              endSnipAfterYankSuffixStmts .reverted := by
          simpa [endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
            endSnipAfterYankArtAddStmts, List.append_assoc] using
            (ExecBlock.consNormal hsourceLet
              (ExecBlock.consNormal hsourceAdd hguardFull))
        have hrev := endX_snip_lot_guard_fail
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw2391)
          (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
          (outSales := outSales) (world := cur.world) (k := k2391) (C := C2391)
          hperm hlotGe rd2391
        exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)
    · have hover :
          UInt256.size ≤ (endFlowArtWorldWord cur.world.2 I).toNat +
            (endSnipArtWord outVat outSales).toNat := by
        omega
      have hoverSource :
          UInt256.size ≤ (endFlowArtWord evm I).toNat +
            (endSnipArtWord outVat outSales).toNat := by
        simpa [hArtEq] using hover
      have hsourceFull :
          ExecBlock config (endSnipAfterYankFrame I outDog outVat outSales) evm
            endSnipAfterYankSuffixStmts .reverted := by
        simpa [endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
          endSnipAfterYankArtAddStmts, List.append_assoc] using
          (ExecBlock.consNormal hsourceLet
            (ExecBlock.consRevert
              (endSnipInternalAddRevert evm I outDog outVat outSales hsz68 hoverSource)))
      have hrev := endX_snip_art_add_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw10092)
        (rdata := cur.rdata) (outDog := outDog) (outVat := outVat)
        (outSales := outSales) (world := cur.world) (k := k10092) (C := C10092)
        hover rd10092
      exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)

theorem endSnipAfterSalesToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨2112⟩
      (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
      endSnipAfterSalesToYankStmts
      (sequenceExit ⟨2346⟩
        (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSnipAfterSalesToSuckRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outDog := outDog) hperm houtDog h128 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm
        ([ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
            .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
            .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
          checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck")
        (sequenceExit ⟨2252⟩
          (endSnipAfterSuckRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit] using hQ
  have htail :=
    endSnipAfterSuckToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (outDog := outDog)
      hperm houtDog h128
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
    endSnipAfterSuckYankStmts, List.append_assoc] using
    hcombined

theorem endSnipAfterVatIlksToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨1984⟩
      (fun cur frame e =>
        frame = endSnipAfterVatIlksFrame I outDog cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        160 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog cur.rdata),
            ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSnipVatIlksReturnMem I outDog cur.rdata ∧
        cur.aw = endSnipAfterVatIlksAw aw)
      endSnipAfterVatIlksToYankStmts
      (sequenceExit ⟨2346⟩
        (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSnipAfterVatIlksToSalesRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outDog := outDog) houtDog h128 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm
        ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false))
        (sequenceExit ⟨2112⟩
          (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit] using hQ
  have htail :=
    endSnipAfterSalesToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outDog := outDog)
      hperm houtDog h128
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
    endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
    endSnipAfterSuckYankStmts, List.append_assoc] using
    hcombined

set_option maxHeartbeats 12000000 in
theorem endSnipAfterDogIlksToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨1858⟩
      (fun cur frame e =>
        frame = endSnipAfterDogIlksFrame I outDog ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata = outDog ∧
        cur.stack =
          [UInt256.ofNat outDog.size,
            memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog),
            ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSnipDogIlksReturnMem I outDog ∧
        cur.aw = endSnipAfterDogIlksAw aw)
      endSnipAfterDogIlksToYankStmts
      (sequenceExit ⟨2346⟩
        (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hrdata, hstack, hmem, haw⟩
  cases hframe
  have rd1858 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
        [UInt256.ofNat outDog.size,
          memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog),
          ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipDogIlksReturnMem I outDog) (endSnipAfterDogIlksAw aw) outDog
        cur0.world k C := by
    simpa [hpc, hstack, hmem, haw, hrdata] using rd
  have hsourceClip :
      ExecBlock config (endSnipAfterDogIlksFrame I outDog) evm
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ]
        (.ok (endSnipAfterClipFrame I outDog) evm) :=
    ExecBlock.consNormal (endLetSnipClip evm I outDog) ExecBlock.nil
  have hslotVat := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
  rw [hrel.env] at hslotVat
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur0.world.2 (endPackVatTarget cur0.world.2 I) := by
    rw [hrel.env, hslotVat]
    have htarget :
        UInt256.land (storageRead I.codeOwner cur0.world.2 (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur0.world.2 I := by
      simp [endPackVatTarget, u256_land_comm]
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
        ExecBlock config (endSnipAfterClipFrame I outDog) evm
          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
            [.var "ilk"] "vatIlk")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_snipAfterClip_false evm I outDog hsrcNoCode)))
    have hsourcePrefix :
        ExecBlock config (endSnipAfterDogIlksFrame I outDog) evm
          endSnipAfterDogIlksVatIlksStmts .reverted := by
      simpa [endSnipAfterDogIlksVatIlksStmts] using
        Reasoning.Theory.execBlock_append hsourceClip hsourceChecked
    have hsourceFull :
        ExecBlock config (endSnipAfterDogIlksFrame I outDog) evm
          endSnipAfterDogIlksToYankStmts .reverted := by
      simpa [endSnipAfterDogIlksToYankStmts, List.append_assoc] using
        (Reasoning.Theory.execBlock_append_term
          (s2 := endSnipAfterVatIlksToYankStmts) hsourcePrefix
          (by intros; intro h; cases h))
    have hrev := endX_snip_vat_no_code_after_dog
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outDog := outDog)
      (k := k) (C := C) (world := cur0.world)
      houtDog h128 hvatNoCode rd1858
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
        ExecBlock config (endSnipAfterClipFrame I outDog) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSnipAfterClipFrame I outDog) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_snipAfterClip_true evm I outDog hsrcCode))
        ExecBlock.nil
    obtain ⟨aw1944, k1944, C1944, rd1944⟩ :=
      endX_snip_after_dog_to_vat_ilks_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outDog := outDog)
        (k := k) (C := C) (world := cur0.world)
        houtDog h128 hvatNoCode rd1858
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipVatIlksCallCursor cur0.world I sel aw1944 outDog outDog)
          k1944 C1944 (endSnipAfterClipFrame I outDog) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ] ++
            endSnipAfterVatIlksToYankStmts)
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      intro rdCall hCallRel
      have hcallProgress0 :=
        (endSnipVatIlksExternalCallRefines
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw1944) (outDog := outDog)
          (rdata := outDog) (k := k1944) (C := C1944) (evm := evm)
          (world := cur0.world)
          hperm hsz68 houtDog h128) rdCall hCallRel
      have hcallProgress :
          BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
            (endSnipAfterClipFrame I outDog) evm
            [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
            (sequenceExit ⟨1984⟩
              (fun cur frame e =>
                frame = endSnipAfterVatIlksFrame I outDog cur.rdata ∧
                CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
                cur.rdata.size < UInt256.size ∧
                160 ≤ cur.rdata.size ∧
                cur.stack =
                  [UInt256.ofNat cur.rdata.size,
                    memLoad (UInt256.ofNat 64)
                      (endSnipVatIlksReturnMem I outDog cur.rdata),
                    ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
                    endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                cur.mem = endSnipVatIlksReturnMem I outDog cur.rdata ∧
                cur.aw = endSnipAfterVatIlksAw aw1944)
              (sequenceExit ⟨2346⟩
                (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
                (runtimeExit (.abi [])))) := by
        rcases hcallProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
        refine ⟨result, endpoint, hb, hr, ?_⟩
        cases result <;> simpa [sequenceExit] using hQ
      exact BlockProgress.seqOrExit hcallProgress
        (endSnipAfterVatIlksToYankRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw1944) (outDog := outDog)
        hperm houtDog h128)
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterClipFrame I outDog) evm
          ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ] ++
            endSnipAfterVatIlksToYankStmts)
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) :=
      htail (by simpa [endSnipVatIlksCallCursor] using rd1944) hrel
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterClipFrame I outDog) evm
          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ++
            endSnipAfterVatIlksToYankStmts)
          (sequenceExit ⟨2346⟩
            (endSnipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts, List.append_assoc] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa [endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
      List.append_assoc] using
      BlockProgress.prepend hsourceClip hcheckedProgress

def endSnipPostDogIlksSuffixStmts : List Stmt :=
  endSnipAfterDogIlksToYankStmts ++ endSnipAfterYankSuffixStmts

def endSnipAfterPrefixStmts : List Stmt :=
  [ .externalCall (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"] "dogIlk" ] ++
    endSnipPostDogIlksSuffixStmts

theorem endSnipDogTarget_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) :
    UInt256.land
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨3⟩)
        solcAddrMask =
      endSnipDogTarget σ I := by
  rw [show (⟨3⟩ : UInt256) = UInt256.ofNat 3 by rfl]
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    Batteries.RBMap.findD, endSnipDogTarget, endCageSlotTarget, storageRead_eq]

theorem endSnipDogTarget_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    endSnipDogTarget σ I = endSnipDogTarget τ I := by
  have hread :
      storageRead I.codeOwner σ (UInt256.ofNat 3) =
        storageRead I.codeOwner τ (UInt256.ofNat 3) := by
    simpa [storageRead_eq] using
      accountMapEquiv_storage_findD hστ I.codeOwner (UInt256.ofNat 3) (default : UInt256)
  unfold endSnipDogTarget endCageSlotTarget
  rw [hread]

theorem endSnipDogCodeSize_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    extCodeSizeWord σ (endSnipDogTarget σ I) =
      extCodeSizeWord τ (endSnipDogTarget τ I) := by
  have htarget := endSnipDogTarget_accountMapEquiv (I := I) hστ
  rw [htarget]
  exact extCodeSizeWord_accountMapEquiv hστ (endSnipDogTarget τ I)

set_option maxHeartbeats 12000000 in
theorem endSnipBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 24))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 24 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some snipTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 24 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some snipTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (snipTransition.params.map Param.name) (transitionSignature snipTransition).paramTypes
        I.calldata = some (endSnipStore I) := by
      simpa [config, snipTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_snip_ok (I := I) hsz68
    have hTagWord :
        endSnipTagWorldWord σ_evm I = endSnipTagWorldWord σ_solm I := by
      simpa [endSnipTagWorldWord, endSkimTagWorldWord, storageRead_eq] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSnipTagWorldSlot I)
          (default : UInt256)
    by_cases htagZeroEvm : endSnipTagWorldWord σ_evm I = ⟨0⟩
    · have htagZeroSolm : endSnipTagWorldWord σ_solm I = ⟨0⟩ :=
        hTagWord.symm.trans htagZeroEvm
      have htagSrc :
          endSnipTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
            ⟨0⟩ := by
        rw [endSnipTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagZeroSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endSnipStore I) snipTransition.body .reverted := by
        simpa [initState] using
          endSnipBodyTagFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc
      exact (endX_snip_tag_fail (g := Sat256.ofUInt256 g)
          hsz68 hsize htagZeroEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have htagNonzeroSolm : endSnipTagWorldWord σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact htagZeroEvm (hTagWord.trans hzero)
      have htagSrc :
          endSnipTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠
            ⟨0⟩ := by
        rw [endSnipTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagNonzeroSolm
      have hDogCodeEq :
          extCodeSizeWord σ_evm (endSnipDogTarget σ_evm I) =
            extCodeSizeWord σ_solm (endSnipDogTarget σ_solm I) :=
        endSnipDogCodeSize_accountMapEquiv (I := I) hAccounts
      by_cases hdogNoCodeEvm :
          extCodeSizeWord σ_evm (endSnipDogTarget σ_evm I) = ⟨0⟩
      · have hdogNoCodeSolm :
            extCodeSizeWord σ_solm (endSnipDogTarget σ_solm I) = ⟨0⟩ :=
          hDogCodeEq.symm.trans hdogNoCodeEvm
        have hdogNoCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨3⟩)
                solcAddrMask) = ⟨0⟩ := by
          rw [endSnipDogTarget_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g)]
          simpa [initState] using hdogNoCodeSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endSnipStore I) snipTransition.body .reverted := by
          simpa [initState] using
            endSnipBodyDogNoCode
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz68 htagSrc hdogNoCodeSrc
        exact (endX_snip_dog_no_code (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hdogNoCodeEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdogCodeSolm :
            extCodeSizeWord σ_solm (endSnipDogTarget σ_solm I) ≠ ⟨0⟩ := by
          intro hzero
          exact hdogNoCodeEvm (hDogCodeEq.trans hzero)
        have hdogCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨3⟩)
                solcAddrMask) ≠ ⟨0⟩ := by
          rw [endSnipDogTarget_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g)]
          simpa [initState] using hdogCodeSolm
        obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
          endX_snip_to_dog_ilks_call (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hdogNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := endSnipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++
                [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := endSnipStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
          endSnipBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc hdogCodeSrc
        have hpostRel :
            CallStateRel
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
              (cA, σ_evm)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
          CallStateRel.initState hAccounts
        have finishProgress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endSnipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              snipTransition.body (runtimeExit (.abi [])) →
            runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
          intro hprogressBody
          simpa [Sat256.ofUInt256, Sat256.toUInt256] using
            (hprogressBody.toRuntimeEquivalenceFor hcode
              (convention := .abi [])
              (by
                intro result hfunc
                exact solmExec.intro hdispatchSel rfl hdec
                  (by simp [initState, Sat256.ofUInt256, Sat256.toUInt256]) hfunc)
              (by
                intro result endpoint h
                exact h))
        have hcallProgress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endSnipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              [ .externalCall (.storage dogRef) "dogIlks" (.intLit 0)
                  [.var "ilk"] "dogIlk" ]
              (sequenceExit ⟨1858⟩
                (fun cur frame e =>
                  frame = endSnipAfterDogIlksFrame I cur.rdata ∧
                  CallStateRel
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    I cur.world e ∧
                  cur.rdata.size < UInt256.size ∧
                  128 ≤ cur.rdata.size ∧
                  cur.stack =
                    [UInt256.ofNat cur.rdata.size,
                      memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I cur.rdata),
                      ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                  cur.mem = endSnipDogIlksReturnMem I cur.rdata ∧
                  cur.aw = endSnipAfterDogIlksAw awCall)
                (runtimeExit (.abi []))) :=
          (endSnipDogIlksExternalCallRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
            (aw := awCall) (rdata := ByteArray.empty) (k := kCall) (C := CCall)
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            hperm hsz68)
            (by simpa [endSnipDogIlksCallCursor] using rdCall)
            hpostRel
        rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
        cases result with
        | ok frameDog evmDog =>
            cases endpoint with
            | reached curDog =>
                simp only [sequenceExit, fallthrough] at hQ
                rcases hQ with
                  ⟨hpcDog, hframeDog, hrelDog, houtDog, h128, hstackDog, hmemDog, hawDog⟩
                rcases hreachEndpoint with ⟨kDog, CDog, rdDog⟩
                have hdogRel :
                    (fun cur frame e =>
                      frame = endSnipAfterDogIlksFrame I curDog.rdata ∧
                      CallStateRel
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        I cur.world e ∧
                      cur.rdata = curDog.rdata ∧
                      cur.stack =
                        [UInt256.ofNat curDog.rdata.size,
                          memLoad (UInt256.ofNat 64)
                            (endSnipDogIlksReturnMem I curDog.rdata),
                          ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                      cur.mem = endSnipDogIlksReturnMem I curDog.rdata ∧
                      cur.aw = endSnipAfterDogIlksAw awCall)
                      curDog frameDog evmDog :=
                  ⟨hframeDog, hrelDog, rfl, hstackDog, hmemDog, hawDog⟩
                have hyankProgress :=
                  (endSnipAfterDogIlksToYankRefines
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                    (aw := awCall) (outDog := curDog.rdata)
                    hperm hsz68 houtDog h128
                    curDog kDog CDog frameDog evmDog hpcDog) rdDog hdogRel
                rcases hyankProgress with
                  ⟨resultYank, endpointYank, hyankBlock, hreachYank, hQYank⟩
                cases resultYank with
                | ok frameYank evmYank =>
                    cases endpointYank with
                    | reached curYank =>
                        simp only [sequenceExit, fallthrough] at hQYank
                        rcases hQYank with ⟨hpcYank, hrelYank⟩
                        rcases hreachYank with ⟨kYank, CYank, rdYank⟩
                        have hsuffix :=
                          endSnipAfterYankSuffixProgressOrInvalid
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                            (aw := awCall) (outDog := curDog.rdata) (cur := curYank)
                            (k := kYank) (C := CYank) (frame := frameYank)
                            (evm := evmYank) hperm hsz68 houtDog h128 hpcYank
                            rdYank hrelYank
                        cases hsuffix with
                        | inl hsuffixProgress =>
                            have hyankSuffixProgress :
                                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  config frameDog evmDog
                                  endSnipPostDogIlksSuffixStmts
                                  (runtimeExit (.abi [])) := by
                              simpa [endSnipPostDogIlksSuffixStmts] using
                                BlockProgress.prepend hyankBlock hsuffixProgress
                            have hcallSuffixProgress :
                                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  config { contract := contract, locals := endSnipStore I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  endSnipAfterPrefixStmts
                                  (runtimeExit (.abi [])) := by
                              simpa [endSnipAfterPrefixStmts] using
                                BlockProgress.prepend hcallBlock hyankSuffixProgress
                            have hprogress :=
                              BlockProgress.prepend hprefix hcallSuffixProgress
                            exact finishProgress (by
                              simpa [snipTransition, checkedExternalCallStmts,
                                endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                                endSnipAfterDogIlksToYankStmts,
                                endSnipAfterDogIlksVatIlksStmts,
                                endSnipAfterVatIlksToYankStmts,
                                endSnipAfterVatIlksSalesStmts,
                                endSnipAfterSalesToYankStmts,
                                endSnipAfterSalesSuckStmts, endSnipAfterSuckYankStmts,
                                endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
                                endSnipAfterYankArtAddStmts, endSnipGrabCheckedStmts,
                                endSnipAfterAddStoreGuardStmts, nonpayable, List.append_assoc]
                                using hprogress)
                        | inr hinvalid =>
                            rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                            have hyankSuffixBlock :
                                ExecBlock config frameDog evmDog
                                  endSnipPostDogIlksSuffixStmts .reverted := by
                              simpa [endSnipPostDogIlksSuffixStmts] using
                                Reasoning.Theory.execBlock_append hyankBlock hsuffixBlock
                            have hcallSuffixBlock :
                                ExecBlock config { contract := contract, locals := endSnipStore I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  endSnipAfterPrefixStmts .reverted := by
                              simpa [endSnipAfterPrefixStmts] using
                                Reasoning.Theory.execBlock_append hcallBlock hyankSuffixBlock
                            have hfullBlock :=
                              Reasoning.Theory.execBlock_append hprefix hcallSuffixBlock
                            have hbody :
                                ExecTransitionBody config contract
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  (endSnipStore I) snipTransition.body .reverted := by
                              have hblock :
                                  ExecBlock config { contract := contract, locals := endSnipStore I }
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    snipTransition.body .reverted := by
                                simpa [snipTransition, checkedExternalCallStmts,
                                  endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                                  endSnipAfterDogIlksToYankStmts,
                                  endSnipAfterDogIlksVatIlksStmts,
                                  endSnipAfterVatIlksToYankStmts,
                                  endSnipAfterVatIlksSalesStmts,
                                  endSnipAfterSalesToYankStmts,
                                  endSnipAfterSalesSuckStmts, endSnipAfterSuckYankStmts,
                                  endSnipAfterYankSuffixStmts, endSnipAfterYankPrefixStmts,
                                  endSnipAfterYankArtAddStmts, endSnipGrabCheckedStmts,
                                  endSnipAfterAddStoreGuardStmts, nonpayable,
                                  List.append_assoc] using hfullBlock
                              simpa [ExecTransitionBody] using execFuncBody_of_execBlock hblock
                            exact endRDinvalidReEquivExecutionRevert hcode hinv hd hdec hbody rfl rfl
                    | returned worldOut outOut =>
                        simp [sequenceExit, fallthrough] at hQYank
                    | reverted =>
                        simp [sequenceExit, fallthrough] at hQYank
                | returned frameRet evmRet value =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameDog evmDog endSnipPostDogIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.returned frameRet evmRet value, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSnipPostDogIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSnipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSnipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSnipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [snipTransition, checkedExternalCallStmts,
                        endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                        endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                        endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                        endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                        endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                        endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                        endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | reverted =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameDog evmDog endSnipPostDogIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.reverted, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSnipPostDogIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSnipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSnipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSnipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [snipTransition, checkedExternalCallStmts,
                        endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                        endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                        endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                        endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                        endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                        endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                        endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | «break» frameBreak evmBreak =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameDog evmDog endSnipPostDogIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.break frameBreak evmBreak, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSnipPostDogIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSnipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSnipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSnipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [snipTransition, checkedExternalCallStmts,
                        endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                        endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                        endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                        endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                        endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                        endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                        endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | «continue» frameCont evmCont =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameDog evmDog endSnipPostDogIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.continue frameCont evmCont, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSnipPostDogIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSnipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSnipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSnipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [snipTransition, checkedExternalCallStmts,
                        endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                        endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                        endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                        endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                        endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                        endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                        endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
            | returned worldOut outOut =>
                simp [sequenceExit, fallthrough] at hQ
            | reverted =>
                simp [sequenceExit, fallthrough] at hQ
        | returned frameRet evmRet value =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSnipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSnipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSnipPostDogIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [snipTransition, checkedExternalCallStmts,
                endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | reverted =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSnipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSnipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSnipPostDogIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [snipTransition, checkedExternalCallStmts,
                endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | «break» frameBreak evmBreak =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSnipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSnipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSnipPostDogIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [snipTransition, checkedExternalCallStmts,
                endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | «continue» frameCont evmCont =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSnipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSnipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.continue frameCont evmCont, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSnipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSnipPostDogIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [snipTransition, checkedExternalCallStmts,
                endSnipAfterPrefixStmts, endSnipPostDogIlksSuffixStmts,
                endSnipAfterDogIlksToYankStmts, endSnipAfterDogIlksVatIlksStmts,
                endSnipAfterVatIlksToYankStmts, endSnipAfterVatIlksSalesStmts,
                endSnipAfterSalesToYankStmts, endSnipAfterSalesSuckStmts,
                endSnipAfterSuckYankStmts, endSnipAfterYankSuffixStmts,
                endSnipAfterYankPrefixStmts, endSnipAfterYankArtAddStmts,
                endSnipGrabCheckedStmts, endSnipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (snipTransition.params.map Param.name) (transitionSignature snipTransition).paramTypes
        I.calldata = none := by
      simpa [config, snipTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_snip_none_short (I := I) hsz4 hshort
    exact (endX_snip_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
