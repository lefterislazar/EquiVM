import Benchmarks.Dss.End.SkipGrab

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)`: body composition -/

def endSkipAfterYankArtAddStmts : List Stmt :=
  [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
    .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew" ]

def endSkipAfterYankPrefixStmts : List Stmt :=
  endSkipAfterYankArtAddStmts ++ endSkipAfterAddStoreGuardStmts

def endSkipAfterYankSuffixStmts : List Stmt :=
  endSkipAfterYankPrefixStmts ++ endSkipGrabCheckedStmts

set_option maxHeartbeats 12000000 in
theorem endSkipAfterYankSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (hpc : cur.pc = ⟨4152⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP : endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat
      cur frame evm) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSkipAfterYankSuffixStmts (runtimeExit (.abi [])) ∨
      (ExecBlock config frame evm endSkipAfterYankSuffixStmts .reverted ∧
        RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with
    ⟨preSuck1σ, preSuck2σ, outVat, outBids, awYank, hframe, hrel, houtVat,
      h160, houtBids, h256, hstack, hmem, haw⟩
  cases hframe
  have rd4152 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4152⟩
        (endSkipAfterYankStack I outCat outVat outBids sel)
        (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids)
        (endSkipYankCallAw awYank) cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  by_cases hrateZero : endFlowVatIlksRateWord outVat = ⟨0⟩
  · have hsource :
        ExecBlock config (endSkipAfterYankFrame I outCat outVat outBids) evm
          endSkipAfterYankSuffixStmts .reverted := by
      simpa [endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
        endSkipAfterYankArtAddStmts] using
        (ExecBlock.consRevert
          (endLetSkipArtRevert evm I outCat outVat outBids hrateZero))
    have hinv := endX_skip_after_yank_rate_invalid
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (sel := sel) (aw := endSkipYankCallAw awYank) (rdata := cur.rdata)
      (outCat := outCat) (outVat := outVat) (outBids := outBids)
      (world := cur.world) (k := k) (C := C) hrateZero rd4152
    exact Or.inr ⟨hsource, hinv⟩
  · have hsourceLet := endLetSkipArt evm I outCat outVat outBids hrateZero
    obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
      endX_skip_after_yank_to_add
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (sel := sel) (aw := endSkipYankCallAw awYank) (rdata := cur.rdata)
        (outCat := outCat) (outVat := outVat) (outBids := outBids)
        (world := cur.world) (k := k) (C := C) hrateZero rd4152
    have hArtEq := endFlowArtWord_eq_world_of_callRel hrel (by omega : 36 ≤ I.calldata.size)
    by_cases hfit :
        (endFlowArtWorldWord cur.world.2 I).toNat +
          (endSkipArtWord outVat outBids).toNat < UInt256.size
    · have hfitSource :
          (endFlowArtWord evm I).toNat +
            (endSkipArtWord outVat outBids).toNat < UInt256.size := by
        simpa [hArtEq] using hfit
      have hsourceAdd :=
        endSkipInternalAddOk evm I outCat outVat outBids hsz68 hfitSource
      obtain ⟨aw4197, k4197, C4197, rd4197⟩ :=
        endX_skip_art_add_ok
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (preSuck1σ := preSuck1σ)
          (preSuck2σ := preSuck2σ) (sel := sel) (aw := aw10092)
          (rdata := cur.rdata) (outCat := outCat) (outVat := outVat)
          (outBids := outBids) (world := cur.world) (k := k10092)
          (C := C10092) hfit rd10092
      by_cases hlot :
          (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat
      · by_cases hart :
            (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat
        · have hsourceStore :=
            endSkipAfterAddStoreGuardOk evm I outCat outVat outBids hsz68 hlot hart
          obtain ⟨aw4295, k4295, C4295, rd4295⟩ :=
            endX_skip_art_guards_ok
              (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (preSuck1σ := preSuck1σ)
              (preSuck2σ := preSuck2σ) (sel := sel) (aw := aw4197)
              (rdata := cur.rdata) (outCat := outCat) (outVat := outVat)
              (outBids := outBids) (world := cur.world) (k := k4197)
              (C := C4197) hperm hlot hart rd4197
          have hsourcePrefix :
              ExecBlock config (endSkipAfterYankFrame I outCat outVat outBids) evm
                endSkipAfterYankPrefixStmts
                (.ok (endSkipAfterArtNewFrame evm I outCat outVat outBids)
                  (endSkipAfterArtNewState evm I outVat outBids)) := by
            simpa [endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts] using
              (ExecBlock.consNormal hsourceLet
                (ExecBlock.consNormal hsourceAdd hsourceStore))
          have hNewEq :
              endSkipArtNewWord evm I outVat outBids =
                endSkipArtNewWorldWord cur.world.2 I outVat outBids := by
            simp [endSkipArtNewWord, endSkipArtNewWorldWord, hArtEq]
          have hstored :=
            hrel.storageStore_codeOwner (ArtSlot (endArg0Bytes32Key I))
              (endSkipArtNewWord evm I outVat outBids)
          have hrelPost :
              CallStateRel (initState cA gh bl σ σ₀ g A I) I
                (endSkipArtStoredWorld cur.world I outVat outBids)
                (endSkipAfterArtNewState evm I outVat outBids) := by
            simpa [endSkipArtStoredWorld, endSkipAfterArtNewState, storageWrite,
              hNewEq, endFlowArtWorldSlot, endArtSlot_eq I (by omega : 36 ≤ I.calldata.size)]
              using hstored
          have htailProgress :
              BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
                (endSkipAfterArtNewFrame evm I outCat outVat outBids)
                (endSkipAfterArtNewState evm I outVat outBids)
                endSkipGrabCheckedStmts (runtimeExit (.abi [])) := by
            simpa [endSkipGrabCheckedStmts] using
              endSkipGrabCheckedCallRefines
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := sel) (aw := aw4295)
                (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
                (baseEvm := evm) (outCat := outCat) (outVat := outVat)
                (outBids := outBids)
                hperm hsz68 houtCat h96 houtVat h160 houtBids h256 hlot hart
                { pc := ⟨4295⟩,
                  stack := endSkipGrabGateRest I sel outCat outVat outBids,
                  mem := endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids,
                  aw := aw4295,
                  rdata := cur.rdata,
                  world := endSkipArtStoredWorld cur.world I outVat outBids }
                k4295 C4295
                (endSkipAfterArtNewFrame evm I outCat outVat outBids)
                (endSkipAfterArtNewState evm I outVat outBids)
                rfl rd4295 ⟨rfl, hrelPost, rfl, rfl, rfl⟩
          exact Or.inl <| by
            simpa [endSkipAfterYankSuffixStmts] using
              BlockProgress.prepend hsourcePrefix htailProgress
        · have hartGe :
              endFreeInt256LimitWord.toNat ≤ (endSkipArtWord outVat outBids).toNat := by
            omega
          have hguard :=
            endSkipAfterAddStoreGuardArtRevert evm I outCat outVat outBids hsz68 hlot hartGe
          have hguardFull :
              ExecBlock config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
                (endSkipAfterAddStoreGuardStmts ++ endSkipGrabCheckedStmts) .reverted :=
            Reasoning.Theory.execBlock_append_term hguard (by intros; intro h; cases h)
          have hsourceFull :
              ExecBlock config (endSkipAfterYankFrame I outCat outVat outBids) evm
                endSkipAfterYankSuffixStmts .reverted := by
            simpa [endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
              endSkipAfterYankArtAddStmts, List.append_assoc] using
              (ExecBlock.consNormal hsourceLet
                (ExecBlock.consNormal hsourceAdd hguardFull))
          have hrev := endX_skip_art_guard_fail
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (preSuck1σ := preSuck1σ)
            (preSuck2σ := preSuck2σ) (sel := sel) (aw := aw4197)
            (rdata := cur.rdata) (outCat := outCat) (outVat := outVat)
            (outBids := outBids) (world := cur.world) (k := k4197) (C := C4197)
            hperm hlot hartGe rd4197
          exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)
      · have hlotGe :
            endFreeInt256LimitWord.toNat ≤ (endSkipBidsLotWord outBids).toNat := by
          omega
        have hguard :=
          endSkipAfterAddStoreGuardLotRevert evm I outCat outVat outBids hsz68 hlotGe
        have hguardFull :
            ExecBlock config (endSkipAfterArtNewFrame evm I outCat outVat outBids) evm
              (endSkipAfterAddStoreGuardStmts ++ endSkipGrabCheckedStmts) .reverted :=
          Reasoning.Theory.execBlock_append_term hguard (by intros; intro h; cases h)
        have hsourceFull :
            ExecBlock config (endSkipAfterYankFrame I outCat outVat outBids) evm
              endSkipAfterYankSuffixStmts .reverted := by
          simpa [endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
            endSkipAfterYankArtAddStmts, List.append_assoc] using
            (ExecBlock.consNormal hsourceLet
              (ExecBlock.consNormal hsourceAdd hguardFull))
        have hrev := endX_skip_lot_guard_fail
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (preSuck1σ := preSuck1σ)
          (preSuck2σ := preSuck2σ) (sel := sel) (aw := aw4197)
          (rdata := cur.rdata) (outCat := outCat) (outVat := outVat)
          (outBids := outBids) (world := cur.world) (k := k4197) (C := C4197)
          hperm hlotGe rd4197
        exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)
    · have hover :
          UInt256.size ≤ (endFlowArtWorldWord cur.world.2 I).toNat +
            (endSkipArtWord outVat outBids).toNat := by
        omega
      have hoverSource :
          UInt256.size ≤ (endFlowArtWord evm I).toNat +
            (endSkipArtWord outVat outBids).toNat := by
        simpa [hArtEq] using hover
      have hsourceFull :
          ExecBlock config (endSkipAfterYankFrame I outCat outVat outBids) evm
            endSkipAfterYankSuffixStmts .reverted := by
        simpa [endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
          endSkipAfterYankArtAddStmts, List.append_assoc] using
          (ExecBlock.consNormal hsourceLet
            (ExecBlock.consRevert
              (endSkipInternalAddRevert evm I outCat outVat outBids hsz68 hoverSource)))
      have hrev := endX_skip_art_add_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (sel := sel) (aw := aw10092) (rdata := cur.rdata) (outCat := outCat)
        (outVat := outVat) (outBids := outBids) (world := cur.world)
        (k := k10092) (C := C10092) hover rd10092
      exact Or.inl (BlockProgress.ofRDrev hsourceFull hrev)

def endSkipAfterHopeYankStmts : List Stmt :=
  checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank"

def endSkipAfterSuck2HopeStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope"

def endSkipAfterSuck2ToYankStmts : List Stmt :=
  endSkipAfterSuck2HopeStmts ++ endSkipAfterHopeYankStmts

def endSkipAfterSuck1Suck2Stmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
    [vowAddr, thisAddr, .var "bid"] "_suck2"

def endSkipAfterSuck1ToYankStmts : List Stmt :=
  endSkipAfterSuck1Suck2Stmts ++ endSkipAfterSuck2ToYankStmts

def endSkipAfterBidsSuck1Stmts : List Stmt :=
  [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
    .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
    .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
    .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck1"

def endSkipAfterBidsToYankStmts : List Stmt :=
  endSkipAfterBidsSuck1Stmts ++ endSkipAfterSuck1ToYankStmts

def endSkipAfterVatIlksBidsStmts : List Stmt :=
  [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
    checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
      "flipBid" (perm := false)

def endSkipAfterVatIlksToYankStmts : List Stmt :=
  endSkipAfterVatIlksBidsStmts ++ endSkipAfterBidsToYankStmts

def endSkipAfterCatIlksVatIlksStmts : List Stmt :=
  [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
    checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
      [.var "ilk"] "vatIlk"

def endSkipAfterCatIlksToYankStmts : List Stmt :=
  endSkipAfterCatIlksVatIlksStmts ++ endSkipAfterVatIlksToYankStmts

theorem endSkipAfterSuck2ToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3956⟩
      (endSkipAfterSuck2Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      endSkipAfterSuck2ToYankStmts
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSkipAfterSuck2ToHopeRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (outCat := outCat)
      hperm houtCat h96 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSkipAfterSuck2HopeStmts
        (sequenceExit ⟨4058⟩
          (endSkipAfterHopeRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit, endSkipAfterSuck2HopeStmts] using hQ
  have htail :=
    endSkipAfterHopeToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (outCat := outCat)
      hperm houtCat h96
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
    endSkipAfterHopeYankStmts, List.append_assoc] using hcombined

theorem endSkipAfterSuck1ToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3837⟩
      (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      endSkipAfterSuck1ToYankStmts
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSkipAfterSuck1ToSuck2Refines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (outCat := outCat)
      hperm houtCat h96 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSkipAfterSuck1Suck2Stmts
        (sequenceExit ⟨3956⟩
          (endSkipAfterSuck2Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit, endSkipAfterSuck1Suck2Stmts] using hQ
  have htail :=
    endSkipAfterSuck2ToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      hperm houtCat h96
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
    endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
    endSkipAfterHopeYankStmts, List.append_assoc] using hcombined

theorem endSkipAfterBidsToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3692⟩
      (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
      endSkipAfterBidsToYankStmts
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSkipAfterBidsToSuck1Refines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      hperm houtCat h96 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSkipAfterBidsSuck1Stmts
        (sequenceExit ⟨3837⟩
          (endSkipAfterSuck1Rel (initState cA gh bl σ σ₀ g A I) I sel outCat)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit, endSkipAfterBidsSuck1Stmts] using hQ
  have htail :=
    endSkipAfterSuck1ToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      hperm houtCat h96
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
    endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
    endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
    endSkipAfterHopeYankStmts, List.append_assoc] using hcombined

theorem endSkipAfterVatIlksToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true)
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
      endSkipAfterVatIlksToYankStmts
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  have hfrontProgress0 :=
    endSkipAfterVatIlksToBidsRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      houtCat h96 cur k C frame evm hpc rd hP
  have hfrontProgress :
      BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
        frame evm endSkipAfterVatIlksBidsStmts
        (sequenceExit ⟨3692⟩
          (endSkipAfterBidsRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi [])))) := by
    rcases hfrontProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
    refine ⟨result, endpoint, hb, hr, ?_⟩
    cases result <;> simpa [sequenceExit, endSkipAfterVatIlksBidsStmts] using hQ
  have htail :=
    endSkipAfterBidsToYankRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      hperm houtCat h96
  have hcombined := BlockProgress.seqOrExit hfrontProgress htail
  simpa [endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
    endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
    endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
    endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
    endSkipAfterHopeYankStmts, List.append_assoc] using hcombined

set_option maxHeartbeats 12000000 in
theorem endSkipAfterCatIlksToYankRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outCat : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3433⟩
      (fun cur frame e =>
        frame = endSkipAfterCatIlksFrame I outCat ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata = outCat ∧
        cur.stack =
          [UInt256.ofNat outCat.size,
            memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat),
            ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSkipCatIlksReturnMem I outCat ∧
        cur.aw = endSkipAfterCatIlksAw aw)
      endSkipAfterCatIlksToYankStmts
      (sequenceExit ⟨4152⟩
        (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hrdata, hstack, hmem, haw⟩
  cases hframe
  have rd3433 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3433⟩
        [UInt256.ofNat outCat.size,
          memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I outCat),
          ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSkipCatIlksReturnMem I outCat) (endSkipAfterCatIlksAw aw) outCat
        cur0.world k C := by
    simpa [hpc, hstack, hmem, haw, hrdata] using rd
  have hsourceFlip :
      ExecBlock config (endSkipAfterCatIlksFrame I outCat) evm
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ]
        (.ok (endSkipAfterFlipFrame I outCat) evm) :=
    ExecBlock.consNormal (endLetSkipFlip evm I outCat) ExecBlock.nil
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
        ExecBlock config (endSkipAfterFlipFrame I outCat) evm
          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
            [.var "ilk"] "vatIlk")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skipAfterFlip_false evm I outCat hsrcNoCode)))
    have hsourcePrefix :
        ExecBlock config (endSkipAfterCatIlksFrame I outCat) evm
          endSkipAfterCatIlksVatIlksStmts .reverted := by
      simpa [endSkipAfterCatIlksVatIlksStmts] using
        Reasoning.Theory.execBlock_append hsourceFlip hsourceChecked
    have hsourceFull :
        ExecBlock config (endSkipAfterCatIlksFrame I outCat) evm
          endSkipAfterCatIlksToYankStmts .reverted := by
      simpa [endSkipAfterCatIlksToYankStmts, List.append_assoc] using
        (Reasoning.Theory.execBlock_append_term
          (s2 := endSkipAfterVatIlksToYankStmts) hsourcePrefix
          (by intros; intro h; cases h))
    have hrev := endX_skip_vat_no_code_after_cat
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
      (k := k) (C := C) (world := cur0.world)
      houtCat h96 hvatNoCode rd3433
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
        ExecBlock config (endSkipAfterFlipFrame I outCat) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkipAfterFlipFrame I outCat) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skipAfterFlip_true evm I outCat hsrcCode))
        ExecBlock.nil
    obtain ⟨aw3519, k3519, C3519, rd3519⟩ :=
      endX_skip_after_cat_to_vat_ilks_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outCat := outCat)
        (k := k) (C := C) (world := cur0.world)
        houtCat h96 hvatNoCode rd3433
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipVatIlksCallCursor cur0.world I sel aw3519 outCat outCat)
          k3519 C3519 (endSkipAfterFlipFrame I outCat) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ] ++
            endSkipAfterVatIlksToYankStmts)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      intro rdCall hCallRel
      have hcallProgress0 :=
        (endSkipVatIlksExternalCallRefines
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw3519) (outCat := outCat)
          (rdata := outCat) (k := k3519) (C := C3519) (evm := evm)
          (world := cur0.world)
          hperm hsz68 houtCat h96) rdCall hCallRel
      have hcallProgress :
          BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
            (endSkipAfterFlipFrame I outCat) evm
            [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
            (sequenceExit ⟨3559⟩
              (fun cur frame e =>
                frame = endSkipAfterVatIlksFrame I outCat cur.rdata ∧
                CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
                cur.rdata.size < UInt256.size ∧
                160 ≤ cur.rdata.size ∧
                cur.stack =
                  [UInt256.ofNat cur.rdata.size,
                    memLoad (UInt256.ofNat 64)
                      (endSkipVatIlksReturnMem I outCat cur.rdata),
                    ⟨0⟩, endSkipCatIlksFlipWord outCat, endSkipCatIlksFlipWord outCat,
                    endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                cur.mem = endSkipVatIlksReturnMem I outCat cur.rdata ∧
                cur.aw = endSkipAfterVatIlksAw aw3519)
              (sequenceExit ⟨4152⟩
                (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
                (runtimeExit (.abi [])))) := by
        rcases hcallProgress0 with ⟨result, endpoint, hb, hr, hQ⟩
        refine ⟨result, endpoint, hb, hr, ?_⟩
        cases result <;> simpa [sequenceExit] using hQ
      exact BlockProgress.seqOrExit hcallProgress
        (endSkipAfterVatIlksToYankRefines
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw3519) (outCat := outCat)
          hperm houtCat h96)
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterFlipFrame I outCat) evm
          ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ] ++
            endSkipAfterVatIlksToYankStmts)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) :=
      htail (by simpa [endSkipVatIlksCallCursor] using rd3519) hrel
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterFlipFrame I outCat) evm
          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
              [.var "ilk"] "vatIlk" ++
            endSkipAfterVatIlksToYankStmts)
          (sequenceExit ⟨4152⟩
            (endSkipAfterYankRel (initState cA gh bl σ σ₀ g A I) I sel outCat)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts, List.append_assoc] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa [endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
      List.append_assoc] using
      BlockProgress.prepend hsourceFlip hcheckedProgress

def endSkipPostCatIlksSuffixStmts : List Stmt :=
  endSkipAfterCatIlksToYankStmts ++ endSkipAfterYankSuffixStmts

def endSkipAfterPrefixStmts : List Stmt :=
  [ .externalCall (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"] "catIlk" ] ++
    endSkipPostCatIlksSuffixStmts

theorem endSkipBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 25))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨672⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 25 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some skipTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 25 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some skipTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (skipTransition.params.map Param.name) (transitionSignature skipTransition).paramTypes
        I.calldata = some (endSkipStore I) := by
      simpa [config, skipTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_skip_ok (I := I) hsz68
    have hTagWord :
        endSkipTagWorldWord σ_evm I = endSkipTagWorldWord σ_solm I := by
      simpa [endSkipTagWorldWord, endSkimTagWorldWord, storageRead_eq] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSnipTagWorldSlot I)
          (default : UInt256)
    by_cases htagZeroEvm : endSkipTagWorldWord σ_evm I = ⟨0⟩
    · have htagZeroSolm : endSkipTagWorldWord σ_solm I = ⟨0⟩ :=
        hTagWord.symm.trans htagZeroEvm
      have htagSrc :
          endSkipTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
            ⟨0⟩ := by
        change endSnipTagWord
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
          ⟨0⟩
        rw [endSnipTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagZeroSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endSkipStore I) skipTransition.body .reverted := by
        simpa [initState] using
          endSkipBodyTagFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc
      exact (endX_skip_tag_fail (g := Sat256.ofUInt256 g)
          hsz68 hsize htagZeroEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have htagNonzeroSolm : endSkipTagWorldWord σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact htagZeroEvm (hTagWord.trans hzero)
      have htagSrc :
          endSkipTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠
            ⟨0⟩ := by
        change endSnipTagWord
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠
          ⟨0⟩
        rw [endSnipTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagNonzeroSolm
      have hCatCodeEq :
          extCodeSizeWord σ_evm (endSkipCatTarget σ_evm I) =
            extCodeSizeWord σ_solm (endSkipCatTarget σ_solm I) :=
        endSkipCatCodeSize_accountMapEquiv (I := I) hAccounts
      by_cases hcatNoCodeEvm :
          extCodeSizeWord σ_evm (endSkipCatTarget σ_evm I) = ⟨0⟩
      · have hcatNoCodeSolm :
            extCodeSizeWord σ_solm (endSkipCatTarget σ_solm I) = ⟨0⟩ :=
          hCatCodeEq.symm.trans hcatNoCodeEvm
        have hcatNoCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨2⟩)
                solcAddrMask) = ⟨0⟩ := by
          rw [endSkipCatTarget_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g)]
          simpa [initState] using hcatNoCodeSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endSkipStore I) skipTransition.body .reverted := by
          simpa [initState] using
            endSkipBodyCatNoCode
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz68 htagSrc hcatNoCodeSrc
        exact (endX_skip_cat_no_code (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hcatNoCodeEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hcatCodeSolm :
            extCodeSizeWord σ_solm (endSkipCatTarget σ_solm I) ≠ ⟨0⟩ := by
          intro hzero
          exact hcatNoCodeEvm (hCatCodeEq.trans hzero)
        have hcatCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨2⟩)
                solcAddrMask) ≠ ⟨0⟩ := by
          rw [endSkipCatTarget_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g)]
          simpa [initState] using hcatCodeSolm
        obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
          endX_skip_to_cat_ilks_call (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hcatNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := endSkipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++
                [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := endSkipStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
          endSkipBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc hcatCodeSrc
        have hpostRel :
            CallStateRel
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
              (cA, σ_evm)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
          CallStateRel.initState hAccounts
        have finishProgress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endSkipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              skipTransition.body (runtimeExit (.abi [])) →
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
              config { contract := contract, locals := endSkipStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              [ .externalCall (.storage catRef) "catIlks" (.intLit 0)
                  [.var "ilk"] "catIlk" ]
              (sequenceExit ⟨3433⟩
                (fun cur frame e =>
                  frame = endSkipAfterCatIlksFrame I cur.rdata ∧
                  CallStateRel
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    I cur.world e ∧
                  cur.rdata.size < UInt256.size ∧
                  96 ≤ cur.rdata.size ∧
                  cur.stack =
                    [UInt256.ofNat cur.rdata.size,
                      memLoad (UInt256.ofNat 64) (endSkipCatIlksReturnMem I cur.rdata),
                      ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                  cur.mem = endSkipCatIlksReturnMem I cur.rdata ∧
                  cur.aw = endSkipAfterCatIlksAw awCall)
                (runtimeExit (.abi []))) :=
          (endSkipCatIlksExternalCallRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
            (aw := awCall) (rdata := ByteArray.empty) (k := kCall) (C := CCall)
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            hperm hsz68)
            (by simpa [endSkipCatIlksCallCursor] using rdCall)
            hpostRel
        rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
        cases result with
        | ok frameCat evmCat =>
            cases endpoint with
            | reached curCat =>
                simp only [sequenceExit, fallthrough] at hQ
                rcases hQ with
                  ⟨hpcCat, hframeCat, hrelCat, houtCat, h96, hstackCat, hmemCat, hawCat⟩
                rcases hreachEndpoint with ⟨kCat, CCat, rdCat⟩
                have hcatRel :
                    (fun cur frame e =>
                      frame = endSkipAfterCatIlksFrame I curCat.rdata ∧
                      CallStateRel
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        I cur.world e ∧
                      cur.rdata = curCat.rdata ∧
                      cur.stack =
                        [UInt256.ofNat curCat.rdata.size,
                          memLoad (UInt256.ofNat 64)
                            (endSkipCatIlksReturnMem I curCat.rdata),
                          ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
                      cur.mem = endSkipCatIlksReturnMem I curCat.rdata ∧
                      cur.aw = endSkipAfterCatIlksAw awCall)
                      curCat frameCat evmCat :=
                  ⟨hframeCat, hrelCat, rfl, hstackCat, hmemCat, hawCat⟩
                have hyankProgress :=
                  (endSkipAfterCatIlksToYankRefines
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                    (aw := awCall) (outCat := curCat.rdata)
                    hperm hsz68 houtCat h96
                    curCat kCat CCat frameCat evmCat hpcCat) rdCat hcatRel
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
                          endSkipAfterYankSuffixProgressOrInvalid
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                            (aw := awCall) (outCat := curCat.rdata) (cur := curYank)
                            (k := kYank) (C := CYank) (frame := frameYank)
                            (evm := evmYank) hperm hsz68 houtCat h96 hpcYank
                            rdYank hrelYank
                        cases hsuffix with
                        | inl hsuffixProgress =>
                            have hyankSuffixProgress :
                                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  config frameCat evmCat
                                  endSkipPostCatIlksSuffixStmts
                                  (runtimeExit (.abi [])) := by
                              simpa [endSkipPostCatIlksSuffixStmts] using
                                BlockProgress.prepend hyankBlock hsuffixProgress
                            have hcallSuffixProgress :
                                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  config { contract := contract, locals := endSkipStore I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  endSkipAfterPrefixStmts
                                  (runtimeExit (.abi [])) := by
                              simpa [endSkipAfterPrefixStmts] using
                                BlockProgress.prepend hcallBlock hyankSuffixProgress
                            have hprogress :=
                              BlockProgress.prepend hprefix hcallSuffixProgress
                            exact finishProgress (by
                              simpa [skipTransition, checkedExternalCallStmts,
                                endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                                endSkipAfterCatIlksToYankStmts,
                                endSkipAfterCatIlksVatIlksStmts,
                                endSkipAfterVatIlksToYankStmts,
                                endSkipAfterVatIlksBidsStmts,
                                endSkipAfterBidsToYankStmts,
                                endSkipAfterBidsSuck1Stmts, endSkipAfterSuck1ToYankStmts,
                                endSkipAfterSuck1Suck2Stmts, endSkipAfterSuck2ToYankStmts,
                                endSkipAfterSuck2HopeStmts, endSkipAfterHopeYankStmts,
                                endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
                                endSkipAfterYankArtAddStmts, endSkipGrabCheckedStmts,
                                endSkipAfterAddStoreGuardStmts, nonpayable, List.append_assoc]
                                using hprogress)
                        | inr hinvalid =>
                            rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                            have hyankSuffixBlock :
                                ExecBlock config frameCat evmCat
                                  endSkipPostCatIlksSuffixStmts .reverted := by
                              simpa [endSkipPostCatIlksSuffixStmts] using
                                Reasoning.Theory.execBlock_append hyankBlock hsuffixBlock
                            have hcallSuffixBlock :
                                ExecBlock config { contract := contract, locals := endSkipStore I }
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  endSkipAfterPrefixStmts .reverted := by
                              simpa [endSkipAfterPrefixStmts] using
                                Reasoning.Theory.execBlock_append hcallBlock hyankSuffixBlock
                            have hfullBlock :=
                              Reasoning.Theory.execBlock_append hprefix hcallSuffixBlock
                            have hbody :
                                ExecTransitionBody config contract
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  (endSkipStore I) skipTransition.body .reverted := by
                              have hblock :
                                  ExecBlock config { contract := contract, locals := endSkipStore I }
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    skipTransition.body .reverted := by
                                simpa [skipTransition, checkedExternalCallStmts,
                                  endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                                  endSkipAfterCatIlksToYankStmts,
                                  endSkipAfterCatIlksVatIlksStmts,
                                  endSkipAfterVatIlksToYankStmts,
                                  endSkipAfterVatIlksBidsStmts,
                                  endSkipAfterBidsToYankStmts,
                                  endSkipAfterBidsSuck1Stmts, endSkipAfterSuck1ToYankStmts,
                                endSkipAfterSuck1Suck2Stmts, endSkipAfterSuck2ToYankStmts,
                                endSkipAfterSuck2HopeStmts, endSkipAfterHopeYankStmts,
                                  endSkipAfterYankSuffixStmts, endSkipAfterYankPrefixStmts,
                                  endSkipAfterYankArtAddStmts, endSkipGrabCheckedStmts,
                                  endSkipAfterAddStoreGuardStmts, nonpayable,
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
                          config frameCat evmCat endSkipPostCatIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.returned frameRet evmRet value, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSkipPostCatIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSkipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSkipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSkipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [skipTransition, checkedExternalCallStmts,
                        endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                        endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                        endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                        endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                        endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                        endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                        endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                        endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                        endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | reverted =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameCat evmCat endSkipPostCatIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.reverted, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSkipPostCatIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSkipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSkipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSkipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [skipTransition, checkedExternalCallStmts,
                        endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                        endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                        endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                        endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                        endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                        endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                        endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                        endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                        endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | «break» frameBreak evmBreak =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameCat evmCat endSkipPostCatIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.break frameBreak evmBreak, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSkipPostCatIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSkipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSkipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSkipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [skipTransition, checkedExternalCallStmts,
                        endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                        endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                        endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                        endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                        endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                        endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                        endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                        endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                        endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts,
                        nonpayable, List.append_assoc] using
                        BlockProgress.prepend hprefix hcallSuffixProgress)
                | «continue» frameCont evmCont =>
                    have hyankSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config frameCat evmCat endSkipPostCatIlksSuffixStmts
                          (runtimeExit (.abi [])) := by
                      refine ⟨.continue frameCont evmCont, endpointYank, ?_, hreachYank, ?_⟩
                      · simpa [endSkipPostCatIlksSuffixStmts] using
                          (Reasoning.Theory.execBlock_append_term
                            (s2 := endSkipAfterYankSuffixStmts) hyankBlock
                            (by intros; intro h; cases h))
                      · simpa [sequenceExit] using hQYank
                    have hcallSuffixProgress :
                        BlockProgress endBytecode I (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                          config { contract := contract, locals := endSkipStore I }
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
                      simpa [endSkipAfterPrefixStmts] using
                        BlockProgress.prepend hcallBlock hyankSuffixProgress
                    exact finishProgress (by
                      simpa [skipTransition, checkedExternalCallStmts,
                        endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                        endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                        endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                        endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                        endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                        endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                        endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                        endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                        endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts,
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
                  config { contract := contract, locals := endSkipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSkipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSkipPostCatIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [skipTransition, checkedExternalCallStmts,
                endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | reverted =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSkipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSkipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSkipPostCatIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [skipTransition, checkedExternalCallStmts,
                endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | «break» frameBreak evmBreak =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSkipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSkipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSkipPostCatIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [skipTransition, checkedExternalCallStmts,
                endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
        | «continue» frameCont evmCont =>
            have hcallSuffixProgress :
                BlockProgress endBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := endSkipStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  endSkipAfterPrefixStmts (runtimeExit (.abi [])) := by
              refine ⟨.continue frameCont evmCont, endpoint, ?_, hreachEndpoint, ?_⟩
              · simpa [endSkipAfterPrefixStmts] using
                  (Reasoning.Theory.execBlock_append_term
                    (s2 := endSkipPostCatIlksSuffixStmts) hcallBlock
                    (by intros; intro h; cases h))
              · simpa [sequenceExit] using hQ
            exact finishProgress (by
              simpa [skipTransition, checkedExternalCallStmts,
                endSkipAfterPrefixStmts, endSkipPostCatIlksSuffixStmts,
                endSkipAfterCatIlksToYankStmts, endSkipAfterCatIlksVatIlksStmts,
                endSkipAfterVatIlksToYankStmts, endSkipAfterVatIlksBidsStmts,
                endSkipAfterBidsToYankStmts, endSkipAfterBidsSuck1Stmts,
                endSkipAfterSuck1ToYankStmts, endSkipAfterSuck1Suck2Stmts,
                endSkipAfterSuck2ToYankStmts, endSkipAfterSuck2HopeStmts,
                endSkipAfterHopeYankStmts, endSkipAfterYankSuffixStmts,
                endSkipAfterYankPrefixStmts, endSkipAfterYankArtAddStmts,
                endSkipGrabCheckedStmts, endSkipAfterAddStoreGuardStmts, nonpayable,
                List.append_assoc] using
                BlockProgress.prepend hprefix hcallSuffixProgress)
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (skipTransition.params.map Param.name) (transitionSignature skipTransition).paramTypes
        I.calldata = none := by
      simpa [config, skipTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_skip_none_short (I := I) hsz4 hshort
    exact (endX_skip_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec


end Benchmarks.Dss.End
