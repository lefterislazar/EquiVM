import Benchmarks.Dss.End.SkipAfterHope

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)`: suffix after `flip.yank(id)` -/

abbrev endSkipArtWord (outVat outBids : ByteArray) : UInt256 :=
  UInt256.div (endSkipBidsTabWord outBids) (endFlowVatIlksRateWord outVat)

abbrev endSkipArtValue (outVat outBids : ByteArray) : Value :=
  endUIntValue (endSkipArtWord outVat outBids)

def endSkipAfterArtFrame (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids) }

abbrev endSkipArtNewWord (evm : EVM.State) (I : ExecutionEnv)
    (outVat outBids : ByteArray) : UInt256 :=
  endGenericAddResult (endFlowArtWord evm I) (endSkipArtWord outVat outBids)

abbrev endSkipArtNewWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outVat outBids : ByteArray) : UInt256 :=
  endGenericAddResult (endFlowArtWorldWord σ I) (endSkipArtWord outVat outBids)

def endSkipAfterArtNewFrame (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids)) }

abbrev endSkipArtHashMem (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_4167_memory
    (mem := endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (x11 := endArg0Word I)

abbrev endSkipAddCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [endSkipArtWord outVat outBids, endFlowArtWorldWord σ I, ⟨4197⟩,
    endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
    endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
    endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
    endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipAfterAddStack (σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (sel : UInt256) : List UInt256 :=
  [endSkipArtNewWorldWord σ I outVat outBids, endSkipArtWord outVat outBids,
    endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
    endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
    endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
    endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkipArtStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (outVat outBids : ByteArray) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endFlowArtWorldSlot I)
    (endSkipArtNewWorldWord world.2 I outVat outBids))

abbrev endSkipAfterArtStoreMem (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_4197_fallthrough_memory
    (mem := endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (x10 := endArg0Word I)

theorem endSkipArtHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 14).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowArtWorldSlot I :=
  endFlowArtHashSlot mem I

theorem endX_skip_after_yank_rate_invalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4152⟩
      (endSkipAfterYankStack I outCat outVat outBids sel)
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4166 := endRuntimeBlocks.endRuntime_block_4152_fallthrough
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨164⟩ : UInt256))
    (x2 := endSkipYankSelectorWord) (x3 := endSkipFlipTarget outCat)
    (x4 := endSkipBidsTabWord outBids)
    (x5 := endSkipBidsUsrWord outBids)
    (x6 := endSkipBidsLotWord outBids)
    (x7 := endSkipBidsBidWord outBids)
    (x8 := endFlowVatIlksRateWord outVat)
    (R := [endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrate
    (by simpa [endSkipAfterYankStack, endSkipYankCallRest] using rd)
  exact endRuntimeBlocks.endRuntime_block_4166 rd4166

theorem endX_skip_after_yank_to_add {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4152⟩
      (endSkipAfterYankStack I outCat outVat outBids sel)
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipAddCallStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw' rdata world k' C' := by
  have rd4167 := endRuntimeBlocks.endRuntime_block_4152_taken
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨164⟩ : UInt256))
    (x2 := endSkipYankSelectorWord) (x3 := endSkipFlipTarget outCat)
    (x4 := endSkipBidsTabWord outBids)
    (x5 := endSkipBidsUsrWord outBids)
    (x6 := endSkipBidsLotWord outBids)
    (x7 := endSkipBidsBidWord outBids)
    (x8 := endFlowVatIlksRateWord outVat)
    (R := [endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrate (by jump_dest)
    (by simpa [endSkipAfterYankStack, endSkipYankCallRest] using rd)
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_4167_packed
      (x0 := endSkipBidsTabWord outBids)
      (x1 := endFlowVatIlksRateWord outVat)
      (x2 := (⟨0⟩ : UInt256))
      (x3 := endSkipBidsTabWord outBids)
      (x4 := endSkipBidsUsrWord outBids)
      (x5 := endSkipBidsLotWord outBids)
      (x6 := endSkipBidsBidWord outBids)
      (x7 := endFlowVatIlksRateWord outVat)
      (x8 := endSkipCatIlksFlipWord outCat)
      (x9 := endSkipCatIlksFlipWord outCat)
      (x10 := endArg1Word I) (x11 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_4152_taken_stack] using rd4167)
  have hslot :=
    endSkipArtHashSlot
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids) I
  exact ⟨aw10092, k10092, C10092, by
    simpa [endRuntimeBlocks.endRuntime_block_4167_stack, endSkipAddCallStack,
      endSkipArtWord, endSkipArtHashMem, endFlowArtWorldWord, hslot] using rd10092⟩

theorem endX_skip_art_add_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ (endFlowArtWorldWord world.2 I).toNat +
      (endSkipArtWord outVat outBids).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipAddCallStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond := endPackAddFailCond
    (endSkipArtWord outVat outBids) (endFlowArtWorldWord world.2 I) hover
  have rd10104 := endRuntimeBlocks.endRuntime_block_10092_fallthrough
    (x0 := endSkipArtWord outVat outBids)
    (x1 := endFlowArtWorldWord world.2 I)
    (R := [⟨4197⟩, endSkipArtWord outVat outBids,
      endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
      endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
      endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
      endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcond (by simpa [endSkipAddCallStack] using rd)
  exact endRuntimeBlocks.endRuntime_block_10104
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endSkipArtWord outVat outBids)
      (x1 := endFlowArtWorldWord world.2 I)
      (R := [⟨4197⟩, endSkipArtWord outVat outBids,
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endX_skip_art_add_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hfit : (endFlowArtWorldWord world.2 I).toNat +
      (endSkipArtWord outVat outBids).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipAddCallStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipAfterAddStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw' rdata world k' C' := by
  have hcond := endPackAddSuccessCond
    (endSkipArtWord outVat outBids) (endFlowArtWorldWord world.2 I) hfit
  obtain ⟨aw10108, k10108, C10108, rd10108⟩ :=
    endRuntimeBlocks.endRuntime_block_10092_taken_packed
      (x0 := endSkipArtWord outVat outBids)
      (x1 := endFlowArtWorldWord world.2 I)
      (R := [⟨4197⟩, endSkipArtWord outVat outBids,
        endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) (by simpa [endSkipAddCallStack] using rd)
  obtain ⟨aw4197, k4197, C4197, rd4197⟩ :=
    endRuntimeBlocks.endRuntime_block_10108_packed
      (x0 := endSkipArtWord outVat outBids + endFlowArtWorldWord world.2 I)
      (x1 := endSkipArtWord outVat outBids)
      (x2 := endFlowArtWorldWord world.2 I)
      (x3 := (⟨4197⟩ : UInt256))
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10092_taken_stack] using rd10108)
  have hsum :
      endSkipArtWord outVat outBids + endFlowArtWorldWord world.2 I =
        endSkipArtNewWorldWord world.2 I outVat outBids := by
    simp [endSkipArtNewWorldWord, endGenericAddResult, u256_add_comm]
  exact ⟨aw4197, k4197, C4197, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack, endSkipAfterAddStack,
      hsum] using rd4197⟩

abbrev endSkipAfterArtNewState (evm : EVM.State) (I : ExecutionEnv)
    (outVat outBids : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (ArtSlot (endArg0Bytes32Key I))
    (endSkipArtNewWord evm I outVat outBids)

theorem endSkipAfterYankFrame_get_tab (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "tab" =
      some (endSkipTabValue outBids) := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "tab") = some (endSkipTabValue outBids)
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "tab") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "tab") = some (endSkipTabValue outBids)
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "tab") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "tab") = some (endSkipTabValue outBids)
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "tab") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "tab") = some (endSkipTabValue outBids)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "tab") (collapseReturns []) (by decide)]
  exact endSkipAfterTabFrame_get_tab I outCat outVat outBids

theorem endSkipAfterYankFrame_get_lot (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "lot" =
      some (endSkipLotValue outBids) := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "lot") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "lot") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "lot") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "lot") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "lot")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "lot") (endSkipUsrValue outBids) (by decide)]
  exact store_get_self (endSkipAfterBidFrame I outCat outVat outBids).locals
    "lot" (endSkipLotValue outBids)

theorem endSkipAfterYankFrame_get_usr (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "usr" =
      some (endSkipUsrValue outBids) := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "usr") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "usr") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "usr") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "usr") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "usr")
    (endSkipTabValue outBids) (by decide)]
  exact store_get_self (endSkipAfterLotFrame I outCat outVat outBids).locals
    "usr" (endSkipUsrValue outBids)

theorem endSkipAfterYankFrame_get_rate (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "rate") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "rate") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "rate") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "rate") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "rate") = some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "rate")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "rate") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "rate") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "rate") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "rate") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  exact store_get_self (endSkipAfterVatIlksFrame I outCat outVat).locals "rate"
    (endUIntValue (endFlowVatIlksRateWord outVat))

theorem endSkipAfterYankFrame_get_ilk (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "ilk") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "ilk") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "ilk") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "ilk") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "ilk")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "ilk") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "ilk") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "ilk") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "ilk") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "ilk")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "ilk") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact endSkipAfterFlipFrame_get_ilk I outCat

theorem endSkipAfterYankFrame_get_Art_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterYankFrame I outCat outVat outBids).locals.get? "Art" = none := by
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "Art") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "Art") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "Art") (collapseReturns []) (by decide)]
  change (((endSkipAfterTabFrame I outCat outVat outBids).locals.insert "_suck1"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSkipAfterTabFrame I outCat outVat outBids).locals
    (k := "_suck1") (a := "Art") (collapseReturns []) (by decide)]
  change ((((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
      (endSkipUsrValue outBids)).insert "tab" (endSkipTabValue outBids)).get?
      "Art") = none
  rw [store_get_ne ((endSkipAfterLotFrame I outCat outVat outBids).locals.insert "usr"
    (endSkipUsrValue outBids)) (k := "tab") (a := "Art")
    (endSkipTabValue outBids) (by decide)]
  rw [store_get_ne (endSkipAfterLotFrame I outCat outVat outBids).locals
    (k := "usr") (a := "Art") (endSkipUsrValue outBids) (by decide)]
  change (((endSkipAfterBidFrame I outCat outVat outBids).locals.insert "lot"
      (endSkipLotValue outBids)).get? "Art") = none
  rw [store_get_ne (endSkipAfterBidFrame I outCat outVat outBids).locals
    (k := "lot") (a := "Art") (endSkipLotValue outBids) (by decide)]
  change (((endSkipAfterBidsFrame I outCat outVat outBids).locals.insert "bid"
      (endSkipBidValue outBids)).get? "Art") = none
  rw [store_get_ne (endSkipAfterBidsFrame I outCat outVat outBids).locals
    (k := "bid") (a := "Art") (endSkipBidValue outBids) (by decide)]
  change (((endSkipAfterRateFrame I outCat outVat).locals.insert "flipBid"
      (collapseReturns (endSkipBidsValues outBids))).get? "Art") = none
  rw [store_get_ne (endSkipAfterRateFrame I outCat outVat).locals
    (k := "flipBid") (a := "Art") (collapseReturns (endSkipBidsValues outBids))
    (by decide)]
  change ((((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "Art") = none
  rw [store_get_ne ((endSkipAfterFlipFrame I outCat).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "Art")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSkipAfterFlipFrame I outCat).locals
    (k := "vatIlk") (a := "Art") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSkipAfterCatIlksFrame I outCat).locals.insert "flip"
      (endSkipFlipValue outCat)).get? "Art") = none
  rw [store_get_ne (endSkipAfterCatIlksFrame I outCat).locals
    (k := "flip") (a := "Art") (endSkipFlipValue outCat) (by decide)]
  change (((endSkipStore I).insert "catIlk"
      (collapseReturns (endSkipCatIlksValues outCat))).get? "Art") = none
  rw [store_get_ne (endSkipStore I)
    (k := "catIlk") (a := "Art") (collapseReturns (endSkipCatIlksValues outCat))
    (by decide)]
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
      (endUIntValue (endArg1Word I))).get? "Art") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "Art") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "Art")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalSkipTabAfterYank (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterYankFrame I outCat outVat outBids) evm (.var "tab") =
      .ok (endSkipTabValue outBids) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterYankFrame_get_tab I outCat outVat outBids

theorem endEvalSkipRateAfterYank (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterYankFrame I outCat outVat outBids) evm (.var "rate") =
      .ok (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSkipAfterYankFrame_get_rate I outCat outVat outBids

theorem endEvalSkipArt (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterYankFrame I outCat outVat outBids) evm
      (.binary .div (.var "tab") (.var "rate")) =
      .ok (endSkipArtValue outVat outBids) := by
  have hrateNatNe : (endFlowVatIlksRateWord outVat).toNat ≠ 0 := by
    intro hzero
    exact hrate (uint256_toNat_eq_zero hzero)
  have hrateIntNe : Int.ofNat (endFlowVatIlksRateWord outVat).toNat ≠ 0 := by
    intro hzero
    exact hrateNatNe (Int.ofNat_eq_zero.mp hzero)
  have hres :
      (endSkipArtWord outVat outBids).toNat =
        (endSkipBidsTabWord outBids).toNat / (endFlowVatIlksRateWord outVat).toNat := by
    unfold endSkipArtWord
    rw [udiv_toNat]
  have hdiv :
      Int.ofNat (endSkipBidsTabWord outBids).toNat /
          Int.ofNat (endFlowVatIlksRateWord outVat).toNat =
        Int.ofNat (endSkipArtWord outVat outBids).toNat := by
    rw [hres]
    change (((endSkipBidsTabWord outBids).toNat : Nat) : Int) /
        (((endFlowVatIlksRateWord outVat).toNat : Nat) : Int) =
      ((((endSkipBidsTabWord outBids).toNat /
        (endFlowVatIlksRateWord outVat).toNat : Nat) : Int))
    rw [← Int.natCast_div]
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipTabAfterYank evm I outCat outVat outBids]
  simp only [bind]
  rw [endEvalSkipRateAfterYank evm I outCat outVat outBids]
  change evalBinaryOp? BinaryOp.div (endSkipTabValue outBids)
      (endUIntValue (endFlowVatIlksRateWord outVat)) =
    EvalResult.ok (endSkipArtValue outVat outBids)
  change
    (if Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 then
        EvalResult.revert
      else
        EvalResult.ok (Value.int
          (Int.ofNat (endSkipBidsTabWord outBids).toNat /
            Int.ofNat (endFlowVatIlksRateWord outVat).toNat))) =
      EvalResult.ok (Value.int (Int.ofNat (endSkipArtWord outVat outBids).toNat))
  rw [if_neg hrateIntNe, hdiv]

theorem endEvalSkipArt_revert (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩) :
    evalExpr? config (endSkipAfterYankFrame I outCat outVat outBids) evm
      (.binary .div (.var "tab") (.var "rate")) = .revert := by
  have hrateInt : Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 := by
    rw [hrate]
    decide
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipTabAfterYank evm I outCat outVat outBids]
  simp only [bind]
  rw [endEvalSkipRateAfterYank evm I outCat outVat outBids]
  change evalBinaryOp? BinaryOp.div (endSkipTabValue outBids)
      (endUIntValue (endFlowVatIlksRateWord outVat)) =
    EvalResult.revert
  change
    (if Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 then
        EvalResult.revert
      else
        EvalResult.ok (Value.int
          (Int.ofNat (endSkipBidsTabWord outBids).toNat /
            Int.ofNat (endFlowVatIlksRateWord outVat).toNat))) =
      EvalResult.revert
  rw [if_pos hrateInt]

theorem endLetSkipArt (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩) :
    ExecStmt config (endSkipAfterYankFrame I outCat outVat outBids) evm
      (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      (.ok (endSkipAfterArtFrame I outCat outVat outBids) evm) := by
  simpa [endSkipAfterArtFrame] using
    ExecStmt.letDecl (endEvalSkipArt evm I outCat outVat outBids hrate)

theorem endLetSkipArtRevert (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩) :
    ExecStmt config (endSkipAfterYankFrame I outCat outVat outBids) evm
      (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      .reverted :=
  ExecStmt.letDeclRevert (endEvalSkipArt_revert evm I outCat outVat outBids hrate)

theorem endSkipAfterArtFrame_get_art (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtFrame I outCat outVat outBids).locals.get? "art" =
      some (endSkipArtValue outVat outBids) := by
  exact store_get_self (endSkipAfterYankFrame I outCat outVat outBids).locals
    "art" (endSkipArtValue outVat outBids)

theorem endSkipAfterArtFrame_get_ilk (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtFrame I outCat outVat outBids).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "ilk") (endSkipArtValue outVat outBids) (by decide)]
  exact endSkipAfterYankFrame_get_ilk I outCat outVat outBids

theorem endSkipAfterArtFrame_get_Art_none (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtFrame I outCat outVat outBids).locals.get? "Art" = none := by
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "Art") = none
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "Art") (endSkipArtValue outVat outBids) (by decide)]
  exact endSkipAfterYankFrame_get_Art_none I outCat outVat outBids

theorem endEvalSkipArtVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtFrame I outCat outVat outBids) evm
      (.var "art") = .ok (endSkipArtValue outVat outBids) := by
  rw [evalExpr?]
  rw [endSkipAfterArtFrame_get_art I outCat outVat outBids]
  rfl

theorem endEvalSkipIlkVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtFrame I outCat outVat outBids) evm
      (.var "ilk") = .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSkipAfterArtFrame_get_ilk I outCat outVat outBids]
  rfl

theorem endEvalSkipAddArgs (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endSkipAfterArtFrame I outCat outVat outBids) evm
      [.storage (ArtRef (.var "ilk")), .var "art"] =
      .ok [endUIntValue (endFlowArtWord evm I), endSkipArtValue outVat outBids] := by
  let frame : Frame := endSkipAfterArtFrame I outCat outVat outBids
  have hsz36 : 36 ≤ I.calldata.size := by omega
  have hcontract : frame.contract = contract := by
    dsimp [frame]
    rfl
  have hbase : frame.locals.get? "Art" = none := by
    dsimp [frame]
    exact endSkipAfterArtFrame_get_Art_none I outCat outVat outBids
  have hilk : evalExpr? config frame evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
    dsimp [frame]
    exact endEvalSkipIlkVarAfterArt evm I outCat outVat outBids
  have hArtStorage : evalExpr? config frame evm (.storage (ArtRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowArtWord evm I)) :=
    endEvalArtStorage_of_arg0 evm I frame hcontract hbase hilk hsz36
  change evalExprs? config frame evm [.storage (ArtRef (.var "ilk")), .var "art"] =
    .ok [endUIntValue (endFlowArtWord evm I), endSkipArtValue outVat outBids]
  rw [evalExprs?]
  rw [hArtStorage]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSkipArtVarAfterArt evm I outCat outVat outBids]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endBindParams_add_skip_Art_art (evm : EVM.State) (I : ExecutionEnv)
    (outVat outBids : ByteArray) :
    bindParams? addFunction.params
      [endUIntValue (endFlowArtWord evm I), endSkipArtValue outVat outBids] =
      some (endGenericMulStore (endFlowArtWord evm I)
        (endSkipArtWord outVat outBids)) := by
  simp [bindParams?, addFunction, endGenericMulStore, endSkipArtValue, endUIntValue]

theorem endSkipInternalAddOk (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endFlowArtWord evm I).toNat +
        (endSkipArtWord outVat outBids).toNat < UInt256.size) :
    ExecStmt config (endSkipAfterArtFrame I outCat outVat outBids) evm
      (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      (.ok (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkipAfterArtNewFrame,
    endSkipArtNewWord, endGenericAddResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkipAfterArtFrame I outCat outVat outBids)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "ArtNew")
      (args := [.storage (ArtRef (.var "ilk")), .var "art"])
      (argVals := [endUIntValue (endFlowArtWord evm I), endSkipArtValue outVat outBids])
      (callee := addFunction)
      (locals := endGenericMulStore (endFlowArtWord evm I)
        (endSkipArtWord outVat outBids))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericAddZStore (endFlowArtWord evm I)
            (endSkipArtWord outVat outBids) })
      (value := some [endUIntValue (endSkipArtNewWord evm I outVat outBids)])
      (endEvalSkipAddArgs evm I outCat outVat outBids hsz68)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_skip_Art_art evm I outVat outBids)
      (by
        simpa [endSkipArtNewWord, endGenericAddResult] using
          endGenericAddFunctionOk evm (endFlowArtWord evm I)
            (endSkipArtWord outVat outBids) hfit)

theorem endSkipInternalAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endFlowArtWord evm I).toNat +
        (endSkipArtWord outVat outBids).toNat) :
    ExecStmt config (endSkipAfterArtFrame I outCat outVat outBids) evm
      (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSkipAfterArtFrame I outCat outVat outBids)
    (evm := evm) (name := "add") (retVar := "ArtNew")
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (argVals := [endUIntValue (endFlowArtWord evm I), endSkipArtValue outVat outBids])
    (callee := addFunction)
    (locals := endGenericMulStore (endFlowArtWord evm I) (endSkipArtWord outVat outBids))
    (endEvalSkipAddArgs evm I outCat outVat outBids hsz68)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_skip_Art_art evm I outVat outBids)
    (endGenericAddFunctionRevert evm (endFlowArtWord evm I)
      (endSkipArtWord outVat outBids) hover)

theorem endSkipAfterArtNewFrame_get_ArtNew (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "ArtNew" =
      some (endUIntValue (endSkipArtNewWord evm I outVat outBids)) := by
  exact store_get_self (endSkipAfterArtFrame I outCat outVat outBids).locals "ArtNew"
    (endUIntValue (endSkipArtNewWord evm I outVat outBids))

theorem endSkipAfterArtNewFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "art" =
      some (endSkipArtValue outVat outBids) := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "art") =
    some (endSkipArtValue outVat outBids)
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "art")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  exact endSkipAfterArtFrame_get_art I outCat outVat outBids

theorem endSkipAfterArtNewFrame_get_lot (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "lot" =
      some (endSkipLotValue outBids) := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "lot") =
    some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "lot")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "lot") = some (endSkipLotValue outBids)
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "lot") (endSkipArtValue outVat outBids) (by decide)]
  exact endSkipAfterYankFrame_get_lot I outCat outVat outBids

theorem endSkipAfterArtNewFrame_get_usr (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "usr" =
      some (endSkipUsrValue outBids) := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "usr") =
    some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "usr")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "usr") = some (endSkipUsrValue outBids)
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "usr") (endSkipArtValue outVat outBids) (by decide)]
  exact endSkipAfterYankFrame_get_usr I outCat outVat outBids

theorem endSkipAfterArtNewFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "ilk")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  exact endSkipAfterArtFrame_get_ilk I outCat outVat outBids

theorem endSkipAfterArtNewFrame_get_Art_none (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "Art" = none := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "Art") = none
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "Art")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  exact endSkipAfterArtFrame_get_Art_none I outCat outVat outBids

theorem endEvalSkipArtNewVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.var "ArtNew") =
      .ok (endUIntValue (endSkipArtNewWord baseEvm I outVat outBids)) := by
  rw [evalExpr?]
  rw [endSkipAfterArtNewFrame_get_ArtNew baseEvm I outCat outVat outBids]
  rfl

theorem endEvalSkipArtVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.var "art") = .ok (endSkipArtValue outVat outBids) := by
  rw [evalExpr?]
  rw [endSkipAfterArtNewFrame_get_art baseEvm I outCat outVat outBids]
  rfl

theorem endEvalSkipLotVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.var "lot") = .ok (endSkipLotValue outBids) := by
  rw [evalExpr?]
  rw [endSkipAfterArtNewFrame_get_lot baseEvm I outCat outVat outBids]
  rfl

theorem endEvalSkipIlkVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.var "ilk") = .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSkipAfterArtNewFrame_get_ilk baseEvm I outCat outVat outBids]
  rfl

theorem endAssignSkipArtNew (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
        .storage (ArtRef (.var "ilk"))
        (endUIntValue (endSkipArtNewWord evm I outVat outBids)) =
      .ok (endSkipAfterArtNewFrame evm I outCat outVat outBids,
        endSkipAfterArtNewState evm I outVat outBids) := by
  let er : EvaledStorageRef := { base := "Art", steps := [.mindex (endArg0Bytes32Key I)] }
  let loc : StorageLoc := wordLoc (ArtSlot (endArg0Bytes32Key I))
  have hdrop : 32 ≤ I.calldata.toList.length - 4 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    omega
  have her : evalStorageRef config (endSkipAfterArtNewFrame evm I outCat outVat outBids)
      evm (ArtRef (.var "ilk")) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefStep, ArtRef, endArg0Bytes32Key,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      endEvalSkipIlkVarAfterAdd, bytes32Width, hdrop]
  have hty :
      storageTypeAt? (endSkipAfterArtNewFrame evm I outCat outVat outBids).contract.storage
          er =
        some (.elem (.int uint256Int)) := by
    unfold endSkipAfterArtNewFrame
    simp [er, storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simp [er, loc]
  have hstore :
      storageLocStore evm loc (endUIntValue (endSkipArtNewWord evm I outVat outBids)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (ArtSlot (endArg0Bytes32Key I)) (endSkipArtNewWord evm I outVat outBids)) := by
    simpa [loc, wordLoc, uint256Loc, endUIntValue] using
      storageLocStore_uint256 evm (ArtSlot (endArg0Bytes32Key I))
        (endSkipArtNewWord evm I outVat outBids)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endSkipAfterArtNewFrame evm I outCat outVat outBids)
    (evm := evm) (slot := ArtRef (.var "ilk")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endSkipArtNewWord evm I outVat outBids).toNat)
    (endSkipAfterArtNewFrame_get_Art_none evm I outCat outVat outBids)
    her hty hloc hstore
  simpa [endSkipAfterArtNewState, loc, endUIntValue] using hassign

theorem endEvalSkipLotLimit_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) := by
  have hlt : Int.ofNat (endSkipBidsLotWord outBids).toNat < int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hlot
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipLotVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [evalExpr?, evalBinaryOp?, endSkipLotValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hlt

theorem endEvalSkipLotLimit_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSkipBidsLotWord outBids).toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool false) := by
  have hle : int256Limit ≤ Int.ofNat (endSkipBidsLotWord outBids).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hlot
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipLotVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [evalExpr?, evalBinaryOp?, endSkipLotValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hle

theorem endEvalSkipArtLimit_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool true) := by
  have hlt : Int.ofNat (endSkipArtWord outVat outBids).toNat < int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipArtVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [evalExpr?, evalBinaryOp?, endSkipArtValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hlt

theorem endEvalSkipArtLimit_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSkipArtWord outVat outBids).toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool false) := by
  have hle : int256Limit ≤ Int.ofNat (endSkipArtWord outVat outBids).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkipArtVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [evalExpr?, evalBinaryOp?, endSkipArtValue, endUIntValue, EvalResult.bind,
    bind, pure]
  exact hle

theorem endEvalSkipLimitGuard_true (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool true) := by
  rw [evalExpr?]
  rw [endEvalSkipLotLimit_true baseEvm evm I outCat outVat outBids hlot]
  rw [endEvalSkipArtLimit_true baseEvm evm I outCat outVat outBids hart]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSkipLimitGuard_lot_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSkipBidsLotWord outBids).toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSkipLotLimit_false baseEvm evm I outCat outVat outBids hlot]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSkipLimitGuard_art_false (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSkipArtWord outVat outBids).toNat) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSkipLotLimit_true baseEvm evm I outCat outVat outBids hlot]
  rw [endEvalSkipArtLimit_false baseEvm evm I outCat outVat outBids hart]
  simp [EvalResult.bind, bind, pure]

def endSkipAfterAddStoreGuardStmts : List Stmt :=
  [ .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
    .require
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) ]

theorem endSkipAfterAddStoreGuardOk (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    ExecBlock config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
      endSkipAfterAddStoreGuardStmts
      (.ok (endSkipAfterArtNewFrame evm I outCat outVat outBids)
        (endSkipAfterArtNewState evm I outVat outBids)) := by
  simp [endSkipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSkipArtNewVarAfterAdd evm evm I outCat outVat outBids)
      (endAssignSkipArtNew evm I outCat outVat outBids (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (endEvalSkipLimitGuard_true evm
          (endSkipAfterArtNewState evm I outVat outBids) I outCat outVat outBids
          hlot hart)) <|
    ExecBlock.nil

theorem endSkipAfterAddStoreGuardLotRevert (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSkipBidsLotWord outBids).toNat) :
    ExecBlock config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
      endSkipAfterAddStoreGuardStmts .reverted := by
  simp [endSkipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSkipArtNewVarAfterAdd evm evm I outCat outVat outBids)
      (endAssignSkipArtNew evm I outCat outVat outBids (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSkipLimitGuard_lot_false evm
          (endSkipAfterArtNewState evm I outVat outBids) I outCat outVat outBids
          hlot))

theorem endSkipAfterAddStoreGuardArtRevert (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSkipArtWord outVat outBids).toNat) :
    ExecBlock config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
      endSkipAfterAddStoreGuardStmts .reverted := by
  simp [endSkipAfterAddStoreGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (endEvalSkipArtNewVarAfterAdd evm evm I outCat outVat outBids)
      (endAssignSkipArtNew evm I outCat outVat outBids (by omega : 36 ≤ I.calldata.size))) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSkipLimitGuard_art_false evm
          (endSkipAfterArtNewState evm I outVat outBids) I outCat outVat outBids
          hlot hart))

abbrev endSkipGrabGateRest (I : ExecutionEnv) (sel : UInt256)
    (outCat outVat outBids : ByteArray) : List UInt256 :=
  [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
    endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
    endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
    endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

theorem endX_skip_lot_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : endFreeInt256LimitWord.toNat ≤ (endSkipBidsLotWord outBids).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipAfterAddStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw4231, k4231, C4231, rd4231⟩ :=
    endRuntimeBlocks.endRuntime_block_4197_taken_packed
      (x0 := endSkipArtNewWorldWord world.2 I outVat outBids)
      (x1 := endSkipArtWord outVat outBids)
      (x2 := endSkipBidsTabWord outBids)
      (x3 := endSkipBidsUsrWord outBids)
      (x4 := endSkipBidsLotWord outBids)
      (x5 := endSkipBidsBidWord outBids)
      (x6 := endFlowVatIlksRateWord outVat)
      (x7 := endSkipCatIlksFlipWord outCat)
      (x8 := endSkipCatIlksFlipWord outCat)
      (x9 := endArg1Word I) (x10 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltNonzero_of_ge_limit (endSkipBidsLotWord outBids) hlot)
      (by jump_dest)
      (by simpa [endSkipAfterAddStack] using rd)
  have hslot :=
    endSkipArtHashSlot
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids) I
  have rd4231' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4231⟩
        [UInt256.isZero (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)),
          endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
        aw4231 rdata (endSkipArtStoredWorld world I outVat outBids) k4231 C4231 := by
    simpa [endRuntimeBlocks.endRuntime_block_4197_taken_stack,
      endRuntimeBlocks.endRuntime_block_4197_taken_memory, endSkipAfterArtStoreMem,
      endSkipArtStoredWorld, hslot] using rd4231
  obtain ⟨aw4236, k4236, C4236, rd4236⟩ :=
    endRuntimeBlocks.endRuntime_block_4231_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)))
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagFail (endSkipBidsLotWord outBids) hlot)
      rd4231'
  exact endRuntimeBlocks.endRuntime_block_4236
    (R := endRuntimeBlocks.endRuntime_block_4231_fallthrough_stack
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4231_fallthrough_stack])
    rd4236

theorem endX_skip_art_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat ≤ (endSkipArtWord outVat outBids).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipAfterAddStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw4225, k4225, C4225, rd4225⟩ :=
    endRuntimeBlocks.endRuntime_block_4197_fallthrough_packed
      (x0 := endSkipArtNewWorldWord world.2 I outVat outBids)
      (x1 := endSkipArtWord outVat outBids)
      (x2 := endSkipBidsTabWord outBids)
      (x3 := endSkipBidsUsrWord outBids)
      (x4 := endSkipBidsLotWord outBids)
      (x5 := endSkipBidsBidWord outBids)
      (x6 := endFlowVatIlksRateWord outVat)
      (x7 := endSkipCatIlksFlipWord outCat)
      (x8 := endSkipCatIlksFlipWord outCat)
      (x9 := endArg1Word I) (x10 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltZero_of_lt_limit (endSkipBidsLotWord outBids) hlot)
      (by simpa [endSkipAfterAddStack] using rd)
  have hslot :=
    endSkipArtHashSlot
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids) I
  have rd4225' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4225⟩
        [UInt256.isZero (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)),
          endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
        aw4225 rdata (endSkipArtStoredWorld world I outVat outBids) k4225 C4225 := by
    simpa [endRuntimeBlocks.endRuntime_block_4197_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_4197_fallthrough_memory, endSkipAfterArtStoreMem,
      endSkipArtStoredWorld, hslot] using rd4225
  obtain ⟨aw4231, k4231, C4231, rd4231⟩ :=
    endRuntimeBlocks.endRuntime_block_4225_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)))
      (x1 := endSkipArtWord outVat outBids)
      (R := [endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd4225'
  obtain ⟨aw4236, k4236, C4236, rd4236⟩ :=
    endRuntimeBlocks.endRuntime_block_4231_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSkipArtWord outVat outBids) (UInt256.ofNat 0)))
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagFail (endSkipArtWord outVat outBids) hart)
      (by simpa [endRuntimeBlocks.endRuntime_block_4225_stack] using rd4231)
  exact endRuntimeBlocks.endRuntime_block_4236
    (R := endRuntimeBlocks.endRuntime_block_4231_fallthrough_stack
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4231_fallthrough_stack])
    rd4236

theorem endX_skip_art_guards_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipAfterAddStack world.2 I outCat outVat outBids sel)
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipGrabGateRest I sel outCat outVat outBids)
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw' rdata (endSkipArtStoredWorld world I outVat outBids) k' C' := by
  obtain ⟨aw4225, k4225, C4225, rd4225⟩ :=
    endRuntimeBlocks.endRuntime_block_4197_fallthrough_packed
      (x0 := endSkipArtNewWorldWord world.2 I outVat outBids)
      (x1 := endSkipArtWord outVat outBids)
      (x2 := endSkipBidsTabWord outBids)
      (x3 := endSkipBidsUsrWord outBids)
      (x4 := endSkipBidsLotWord outBids)
      (x5 := endSkipBidsBidWord outBids)
      (x6 := endFlowVatIlksRateWord outVat)
      (x7 := endSkipCatIlksFlipWord outCat)
      (x8 := endSkipCatIlksFlipWord outCat)
      (x9 := endArg1Word I) (x10 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hperm
      (endSnipSltZero_of_lt_limit (endSkipBidsLotWord outBids) hlot)
      (by simpa [endSkipAfterAddStack] using rd)
  have hslot :=
    endSkipArtHashSlot
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids) I
  have rd4225' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4225⟩
        [UInt256.isZero (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)),
          endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
          endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
          endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
          endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
        aw4225 rdata (endSkipArtStoredWorld world I outVat outBids) k4225 C4225 := by
    simpa [endRuntimeBlocks.endRuntime_block_4197_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_4197_fallthrough_memory, endSkipAfterArtStoreMem,
      endSkipArtStoredWorld, hslot] using rd4225
  obtain ⟨aw4231, k4231, C4231, rd4231⟩ :=
    endRuntimeBlocks.endRuntime_block_4225_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSkipBidsLotWord outBids) (UInt256.ofNat 0)))
      (x1 := endSkipArtWord outVat outBids)
      (R := [endSkipBidsTabWord outBids, endSkipBidsUsrWord outBids,
        endSkipBidsLotWord outBids, endSkipBidsBidWord outBids,
        endFlowVatIlksRateWord outVat, endSkipCatIlksFlipWord outCat,
        endSkipCatIlksFlipWord outCat, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd4225'
  obtain ⟨aw4295, k4295, C4295, rd4295⟩ :=
    endRuntimeBlocks.endRuntime_block_4231_taken_packed
      (x0 := UInt256.isZero
        (UInt256.slt (endSkipArtWord outVat outBids) (UInt256.ofNat 0)))
      (R := [endSkipArtWord outVat outBids, endSkipBidsTabWord outBids,
        endSkipBidsUsrWord outBids, endSkipBidsLotWord outBids,
        endSkipBidsBidWord outBids, endFlowVatIlksRateWord outVat,
        endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (endSnipSignedFlagPass (endSkipArtWord outVat outBids) hart)
      (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_4225_stack] using rd4231)
  exact ⟨aw4295, k4295, C4295, by
    simpa [endRuntimeBlocks.endRuntime_block_4231_taken_stack,
      endSkipGrabGateRest] using rd4295⟩

end Benchmarks.Dss.End
