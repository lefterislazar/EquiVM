import Benchmarks.Dss.End.Cage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endCageCureAndFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hmemRead : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmemSize : 96 ≤ mem.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterPotCheckedCursor preWorld I sel aw rdata mem world)
      k C endCageAfterPotFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageCureCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (mem := mem) (preWorld := preWorld) (world := world)
      hperm hmemLoad hmemRead hmemSize) ?_
  intro cur' k' C' frame' evm' hpc'
  intro rd' hP'
  cases hP'.1
  have rd562 := endRuntimeBlocks.endRuntime_block_6298
    (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
    (x2 := (⟨1763987465⟩ : UInt256))
    (x3 := endCageSlotTarget world.2 I (UInt256.ofNat 7))
    (x4 := (⟨562⟩ : UInt256)) (R := [sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega) hperm (by native_decide)
    (by
      simpa [hpc', hP'.2.2.1, endRuntimeBlocks.endRuntime_block_6282_taken_stack,
        endCageSlotCallRest] using rd')
  have rdret := endRuntimeBlocks.endRuntime_block_562
    (R := [sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    (by simpa [endRuntimeBlocks.endRuntime_block_6298_stack] using rd562)
  exact BlockProgress.ofRDret ExecBlock.nil rdret
    hP'.2.1.created.symm hP'.2.1.accounts abiVoidFallthrough

theorem endCagePotThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hmemRead : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmemSize : 96 ≤ mem.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterSpotCheckedCursor preWorld I sel aw rdata mem world)
      k C endCageAfterSpotFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
        checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCagePotCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (mem := mem) (preWorld := preWorld) (world := world)
      hperm hmemLoad hmemRead hmemSize) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  have hcurMemLoad : memLoad (UInt256.ofNat 64) cur'.mem = ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hcurMemRead : cur'.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_read64 hmemSize hmemRead hmemLoad
  have hcurMemSize : 96 ≤ cur'.mem.size := by
    rw [hP'.2.2.2]
    exact endCageCallMem_size_ge96 hmemLoad
  exact endCageCureAndFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := cur'.aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (mem := cur'.mem)
    (preWorld := world) (world := cur'.world)
    hperm hcurMemLoad hcurMemRead hcurMemSize
    (by
      simpa [endCageAfterPotCheckedCursor, hpc', hP'.2.2.1] using rd')
    (by simpa [endCageAfterPotCheckedCursor] using hP'.2.1)

theorem endCageSpotThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hmemRead : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmemSize : 96 ≤ mem.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterVowCheckedCursor preWorld I sel aw rdata mem world)
      k C endCageAfterVowFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
        (
        checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
        checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage"))
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageSpotCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (mem := mem) (preWorld := preWorld) (world := world)
      hperm hmemLoad hmemRead hmemSize) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  have hcurMemLoad : memLoad (UInt256.ofNat 64) cur'.mem = ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hcurMemRead : cur'.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_read64 hmemSize hmemRead hmemLoad
  have hcurMemSize : 96 ≤ cur'.mem.size := by
    rw [hP'.2.2.2]
    exact endCageCallMem_size_ge96 hmemLoad
  exact endCagePotThroughFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := cur'.aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (mem := cur'.mem)
    (preWorld := world) (world := cur'.world)
    hperm hcurMemLoad hcurMemRead hcurMemSize
    (by
      simpa [endCageAfterSpotCheckedCursor, hpc', hP'.2.2.1] using rd')
    (by simpa [endCageAfterSpotCheckedCursor] using hP'.2.1)

theorem endCageVowThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hmemRead : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmemSize : 96 ≤ mem.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterDogCheckedCursor preWorld I sel aw rdata mem world)
      k C endCageAfterDogFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
        (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
          (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
            checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")))
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageVowCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (mem := mem) (preWorld := preWorld) (world := world)
      hperm hmemLoad hmemRead hmemSize) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  have hcurMemLoad : memLoad (UInt256.ofNat 64) cur'.mem = ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hcurMemRead : cur'.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_read64 hmemSize hmemRead hmemLoad
  have hcurMemSize : 96 ≤ cur'.mem.size := by
    rw [hP'.2.2.2]
    exact endCageCallMem_size_ge96 hmemLoad
  exact endCageSpotThroughFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := cur'.aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (mem := cur'.mem)
    (preWorld := world) (world := cur'.world)
    hperm hcurMemLoad hcurMemRead hcurMemSize
    (by
      simpa [endCageAfterVowCheckedCursor, hpc', hP'.2.2.1] using rd')
    (by simpa [endCageAfterVowCheckedCursor] using hP'.2.1)

theorem endCageDogThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hmemRead : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmemSize : 96 ≤ mem.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterCatCheckedCursor preWorld I sel aw rdata mem world)
      k C endCageAfterCatFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
        (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
          (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
            (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
              checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage"))))
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageDogCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (mem := mem) (preWorld := preWorld) (world := world)
      hperm hmemLoad hmemRead hmemSize) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  have hcurMemLoad : memLoad (UInt256.ofNat 64) cur'.mem = ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hcurMemRead : cur'.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_read64 hmemSize hmemRead hmemLoad
  have hcurMemSize : 96 ≤ cur'.mem.size := by
    rw [hP'.2.2.2]
    exact endCageCallMem_size_ge96 hmemLoad
  exact endCageVowThroughFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := cur'.aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (mem := cur'.mem)
    (preWorld := world) (world := cur'.world)
    hperm hcurMemLoad hcurMemRead hcurMemSize
    (by
      simpa [endCageAfterDogCheckedCursor, hpc', hP'.2.2.1] using rd')
    (by simpa [endCageAfterDogCheckedCursor] using hP'.2.1)

theorem endCageCatThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterVatStatusCursor σ I sel aw rdata world)
      k C endCageAfterVatFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage" ++
        (checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
          (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
            (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
              (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
                checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")))))
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageCatCheckedCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) (world := world) hperm) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  let mem0 := endCageCallMem (endCageAuthMem I)
  have hmem0Load : memLoad (UInt256.ofNat 64) mem0 = ⟨128⟩ :=
    endCageCallMem_mload64 (by rw [endCageAuthMem_size I])
      (endCageAuthMem_read64 I) (endCageAuthMem_mload64 I)
  have hmem0Read : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    endCageCallMem_read64 (by rw [endCageAuthMem_size I])
      (endCageAuthMem_read64 I) (endCageAuthMem_mload64 I)
  have hmem0Size : 96 ≤ mem0.size := by
    dsimp [mem0]
    exact endCageCallMem_size_ge96 (endCageAuthMem_mload64 I)
  have hcurMemLoad : memLoad (UInt256.ofNat 64) cur'.mem = ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_mload64 hmem0Size hmem0Read hmem0Load
  have hcurMemRead : cur'.mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hP'.2.2.2]
    exact endCageCallMem_read64 hmem0Size hmem0Read hmem0Load
  have hcurMemSize : 96 ≤ cur'.mem.size := by
    rw [hP'.2.2.2]
    exact endCageCallMem_size_ge96 hmem0Load
  exact endCageDogThroughFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := cur'.aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (mem := cur'.mem)
    (preWorld := world) (world := cur'.world)
    hperm hcurMemLoad hcurMemRead hcurMemSize
    (by
      simpa [endCageAfterCatCheckedCursor, hpc', hP'.2.2.1] using rd')
    (by simpa [endCageAfterCatCheckedCursor] using hP'.2.1)

theorem endCageVatThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageVatCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := (∅ : Store) } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      ([ .externalCall (.storage vatRef) "cage" (.intLit 0) [] "_vatCage" ] ++
        (checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage" ++
          (checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
            (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
              (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
                (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
                  checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage"))))))
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.seqOrExit
    (endCageVatExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (rdata := rdata) (k := k)
      (C := C) (evm := evm) hperm) ?_
  intro cur' k' C' frame' evm' hpc' rd' hP'
  cases hP'.1
  exact endCageCatThroughFinalRefines
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (aw := aw) (rdata := cur'.rdata)
    (k := k') (C := C') (evm := evm') (world := cur'.world)
    hperm
    (by
      simpa [endCageAfterVatStatusCursor, hpc', hP'.2.2.1, hP'.2.2.2.1,
        hP'.2.2.2.2] using rd')
    (by simpa [endCageAfterVatStatusCursor] using hP'.2.1)

theorem endCageStorageLoad_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
    Account.lookupStorage, Batteries.RBMap.findD]

theorem endCagePostCallStateRel {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    CallStateRel (initState cA gh bl σ_evm σ₀ g A I) I
      (cA, endCagePostAccountMap σ_evm I)
      (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)) := by
  have hinit :
      CallStateRel (initState cA gh bl σ_evm σ₀ g A I) I (cA, σ_evm)
        (initState cA gh bl σ_solm σ₀ g A I) :=
    CallStateRel.initState hAccounts
  have hstores :=
    ((hinit.storageStore_codeOwner (UInt256.ofNat 8) (UInt256.ofNat 0)).storageStore_codeOwner
      (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
  simpa [endCagePostAccountMap, endCagePostState, endCageAfterLiveState, initState,
    storageWrite, storageStore_accountMap, storageStore_executionEnv] using hstores

theorem endCagePostVatTarget_eq {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    UInt256.land
        (Solm.EVM.storageLoad
          (endCagePostState (initState cA gh bl σ_solm σ₀ g A I))
          (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
          ⟨1⟩)
        solcAddrMask =
      endCageVatTarget σ_evm I := by
  have hpost := endCagePostCallStateRel
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have howner :
      (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner =
        I.codeOwner := by
    simp [endCagePostState, endCageAfterLiveState, initState, storageStore_executionEnv]
  have hslot :
      storageRead I.codeOwner σ_evm ⟨1⟩ =
        Solm.EVM.storageLoad
          (endCagePostState (initState cA gh bl σ_solm σ₀ g A I))
          I.codeOwner ⟨1⟩ := by
    have hread := accountMapEquiv_storage_findD hpost.accounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hread' :
        storageRead I.codeOwner (endCagePostAccountMap σ_evm I) ⟨1⟩ =
          Solm.EVM.storageLoad
            (endCagePostState (initState cA gh bl σ_solm σ₀ g A I))
            I.codeOwner ⟨1⟩ := by
      unfold storageRead Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
      exact hread
    have hprePost :
        storageRead I.codeOwner σ_evm ⟨1⟩ =
          storageRead I.codeOwner (endCagePostAccountMap σ_evm I) ⟨1⟩ := by
      simpa using (endCagePostAccountMap_read_vat σ_evm I).symm
    exact hprePost.trans hread'
  rw [endCageVatTarget_eq_pre, howner, hslot]

theorem endCagePostVatNoCode_solm_of_evm
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatNoCode :
      extCodeSizeWord (endCagePostAccountMap σ_evm I) (endCageVatTarget σ_evm I) = ⟨0⟩) :
    extCodeSizeWord
        (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).accountMap
        (UInt256.land
          (Solm.EVM.storageLoad
            (endCagePostState (initState cA gh bl σ_solm σ₀ g A I))
            (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
            ⟨1⟩)
          solcAddrMask) = ⟨0⟩ := by
  have hpost := endCagePostCallStateRel
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have htarget := endCagePostVatTarget_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have hcode :=
    (extCodeSizeWord_accountMapEquiv hpost.accounts (endCageVatTarget σ_evm I)).symm.trans
      hvatNoCode
  simpa [htarget] using hcode

theorem endCagePostVatCode_solm_of_evm
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hvatCode :
      extCodeSizeWord (endCagePostAccountMap σ_evm I) (endCageVatTarget σ_evm I) ≠ ⟨0⟩) :
    extCodeSizeWord
        (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).accountMap
        (UInt256.land
          (Solm.EVM.storageLoad
            (endCagePostState (initState cA gh bl σ_solm σ₀ g A I))
            (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).executionEnv.codeOwner
            ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩ := by
  intro hzero
  have hpost := endCagePostCallStateRel
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have htarget := endCagePostVatTarget_eq
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have hzero' :
      extCodeSizeWord
          (endCagePostState (initState cA gh bl σ_solm σ₀ g A I)).accountMap
          (endCageVatTarget σ_evm I) = ⟨0⟩ := by
    simpa [htarget] using hzero
  exact hvatCode
    ((extCodeSizeWord_accountMapEquiv hpost.accounts (endCageVatTarget σ_evm I)).trans hzero')

theorem endCageBodyPrefixOk (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvatCode : extCodeSizeWord (endCagePostState evm).accountMap
        (UInt256.land
          (Solm.EVM.storageLoad (endCagePostState evm)
            (endCagePostState evm).executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := (∅ : Store) } evm
      (nonpayable ++ auth ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage liveRef (.intLit 0),
          .assign .storage whenRef nowT,
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := (∅ : Store) } (endCagePostState evm)) := by
  simpa [nonpayable, auth, endCagePostState, endCageAfterLiveState] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_cage_true evm hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_cage_true evm hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (endAssignLiveZero_cage evm)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (endEvalNow_cage
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩))
          (endAssignWhenNow_cage
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩))) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_cage_true (endCagePostState evm)
          hvatCode)) <|
      ExecBlock.nil)

theorem endCageBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 22))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 22 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some cageTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 22 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some cageTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (cageTransition.params.map Param.name) (transitionSignature cageTransition).paramTypes
      I.calldata = some ∅ := by
    simpa [config, cageTransition, transitionSignature] using endDecode_noArgs (I := I) hsz4
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
    have hLiveWord :
        solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hliveSolm : solcSlotWord σ_solm I ⟨8⟩ = ⟨1⟩
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ = ⟨1⟩ :=
        hLiveWord.trans hliveSolm
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ = ⟨1⟩ := by
        rw [endCageStorageLoad_init_eq]
        exact hliveSolm
      by_cases hvatNoCodeEvm :
          extCodeSizeWord (endCagePostAccountMap σ_evm I) (endCageVatTarget σ_evm I) = ⟨0⟩
      · have hvatNoCodeSolm :=
          endCagePostVatNoCode_solm_of_evm
            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) hAccounts hvatNoCodeEvm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ∅ cageTransition.body .reverted := by
          exact endCageBodyVatNoCode
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvatNoCodeSolm
        exact (endX_cage_vat_no_code (g := Sat256.ofUInt256 g) hperm hauthEvm hliveEvm
            hvatNoCodeEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hvatCodeSolm :=
          endCagePostVatCode_solm_of_evm
            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) hAccounts hvatNoCodeEvm
        obtain ⟨awVat, kVat, CVat, rdVat⟩ :=
          endX_cage_to_vat_call (g := Sat256.ofUInt256 g) hperm hauthEvm hliveEvm
            hvatNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := (∅ : Store) }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++ auth ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                  .assign .storage liveRef (.intLit 0),
                  .assign .storage whenRef nowT,
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := (∅ : Store) }
                (endCagePostState
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))) :=
          endCageBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvatCodeSolm
        have hpostRel :=
          endCagePostCallStateRel
            (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) hAccounts
        have hprogress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := (∅ : Store) }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((nonpayable ++ auth ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                  .assign .storage liveRef (.intLit 0),
                  .assign .storage whenRef nowT,
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                ([ .externalCall (.storage vatRef) "cage" (.intLit 0) [] "_vatCage" ] ++
                  (checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage" ++
                    (checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
                      (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
                        (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
                          (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
                            checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")))))))
              (runtimeExit (.abi [])) :=
          BlockProgress.seqOfRD
            (R := fun cur _ e =>
              CallStateRel (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I cur.world e)
            hprefix
            (by
              simpa [endCageVatCallCursor] using rdVat)
            hpostRel
            (endCageVatThroughFinalRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
              (I := I) (g := Sat256.ofUInt256 g) (sel := sel) (aw := awVat)
              (rdata := ByteArray.empty) (k := kVat) (C := CVat)
              (evm := endCagePostState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
              hperm)
        have hprogressBody :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := (∅ : Store) }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              cageTransition.body (runtimeExit (.abi [])) := by
          simpa [cageTransition, checkedExternalCallStmts, List.append_assoc] using hprogress
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
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ ≠ ⟨1⟩ := by
        intro hbad
        exact hliveSolm (hLiveWord.symm.trans hbad)
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ ≠ ⟨1⟩ := by
        rw [endCageStorageLoad_init_eq]
        exact hliveSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            ∅ cageTransition.body .reverted := by
        exact endCageBodyLiveFail
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv) hauthSrc hliveSrc
      exact (endX_cage_live_fail (g := Sat256.ofUInt256 g) hauthEvm hliveEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
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
          ∅ cageTransition.body .reverted := by
      exact endCageBodyAuthFail
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv) hauthSrc
    exact (endX_cage_auth_fail (g := Sat256.ofUInt256 g) hauthEvm hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.Dss.End
