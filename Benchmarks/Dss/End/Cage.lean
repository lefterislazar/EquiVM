import Benchmarks.Dss.End.Admin
import Benchmarks.Dss.End.SimpleGetters
import Benchmarks.Dss.End.RuntimeBlocks_003
import Benchmarks.Dss.End.RuntimeBlocks_009
import Benchmarks.Dss.End.RuntimeBlocks_010
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `cage()` -/

abbrev endCagePostAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (storageWrite I.codeOwner σ ⟨8⟩ ⟨0⟩) ⟨9⟩
    (UInt256.ofNat I.header.timestamp)

theorem endCagePostAccountMap_read_vat (σ : AccountMap) (I : ExecutionEnv) :
    storageRead I.codeOwner (endCagePostAccountMap σ I) (UInt256.ofNat 1) =
      storageRead I.codeOwner σ (UInt256.ofNat 1) := by
  unfold endCagePostAccountMap
  rw [show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from by native_decide]
  rw [show (⟨0⟩ : UInt256) = UInt256.ofNat 0 from by native_decide]
  rw [show (⟨9⟩ : UInt256) = UInt256.ofNat 9 from by native_decide]
  rw [storageRead_storageWrite_ne I.codeOwner
    (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
    (by native_decide)]
  rw [storageRead_storageWrite_ne I.codeOwner σ (by native_decide)]

abbrev endCageVatTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner (endCagePostAccountMap σ I) ⟨1⟩) solcAddrMask

theorem endCageVatTarget_eq_pre (σ : AccountMap) (I : ExecutionEnv) :
    endCageVatTarget σ I =
      UInt256.land (storageRead I.codeOwner σ (⟨1⟩ : UInt256)) solcAddrMask := by
  unfold endCageVatTarget
  rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from by native_decide]
  rw [endCagePostAccountMap_read_vat]

abbrev endCageSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)

theorem endCageSelectorWord_prefix :
    (UInt256.toByteArray endCageSelectorWord).extract 0 4 = cageSelector := by
  native_decide

theorem endExternalEncode_cage :
    config.externalABI.encode? "cage" [] = some cageSelector := by
  rfl

theorem endExternalDecode_cage (out : ByteArray) :
    config.externalABI.decode? "cage" out = some [] := by
  rfl

abbrev endCageCallMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray endCageSelectorWord).write 0 mem
    (memLoad (UInt256.ofNat 64) mem).toNat 32

theorem endCageCallMem_readSelector {mem : ByteArray}
    (hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    (endCageCallMem mem).readWithPadding 128 4 = cageSelector := by
  unfold endCageCallMem
  rw [hload]
  change ((UInt256.toByteArray endCageSelectorWord).write 0 mem 128 32).readWithPadding
      (128 + 0) 4 = cageSelector
  rw [toByteArray_write_read_window_of_gap_unbounded
    endCageSelectorWord mem 128 0 4 (by omega) (by omega) (by omega)]
  exact endCageSelectorWord_prefix

theorem endCageCallMem_read64 {mem : ByteArray}
    (hsize : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    (endCageCallMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endCageCallMem
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endCageSelectorWord mem 128 64 (by omega) (by omega)]
  exact hread

theorem endCageCallMem_mload64 {mem : ByteArray}
    (hsize : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hge := toByteArray_write_size_ge_off_add32_unbounded
        endCageSelectorWord mem 128
      unfold endCageCallMem
      rw [hload]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
      omega)
    (endCageCallMem_read64 hsize hread hload)

theorem endCageCallMem_size_ge96 {mem : ByteArray}
    (hload : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    96 ≤ (endCageCallMem mem).size := by
  have hge := toByteArray_write_size_ge_off_add32_unbounded
    endCageSelectorWord mem 128
  unfold endCageCallMem
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  omega

abbrev endCageAuthMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_5433_taken_memory (ee := I) (mem := solcFreePtrMem)

theorem endCageAuthMem_size (I : ExecutionEnv) :
    (endCageAuthMem I).size = 96 := by
  simpa [endCageAuthMem, endRuntimeBlocks.endRuntime_block_5433_taken_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    (twoWordHashMem_size_96 (UInt256.ofNat I.source.val) (UInt256.ofNat 0)
      solcFreePtrMem_size)

theorem endCageAuthMem_read64 (I : ExecutionEnv) :
    (endCageAuthMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [endCageAuthMem, endRuntimeBlocks.endRuntime_block_5433_taken_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    (twoWordHashMem_read64 (UInt256.ofNat I.source.val) (UInt256.ofNat 0)
      solcFreePtrMem_size solcFreePtrMem_read64)

theorem endCageAuthMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endCageAuthMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [endCageAuthMem_size I]; decide) (endCageAuthMem_read64 I)

theorem endCageCallCopyZero (out mem : ByteArray) (off : UInt256) :
    out.write 0 mem off.toNat (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = mem := by
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero]

theorem endCageSlotLoad_eq_of_callRel {s0 cA σ I evm}
    (h : CallStateRel s0 I (cA, σ) evm) (slot : UInt256) :
    UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask =
      UInt256.land (storageRead I.codeOwner σ slot) solcAddrMask := by
  have hraw :
      Solm.EVM.storageLoad evm I.codeOwner slot = storageRead I.codeOwner σ slot := by
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, storageRead_eq]
      using (accountMapEquiv_storage_findD h.accounts I.codeOwner slot (default : UInt256)).symm
  rw [h.env]
  exact congrArg (fun w => UInt256.land w solcAddrMask) hraw

theorem endEvalAddressSlot_cage {locals : Store} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {wordSlot : UInt256}
    (hbase : locals.get? slot.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm slot = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc wordSlot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage slot) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner wordSlot)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc), endRuntimeStorageLocLoad_address_offset0]

theorem endEvalCodeSizeGuard_cage_true {locals : Store} {evm : EVM.State}
    {receiver : Expr} {target : UInt256}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address (AccountAddress.ofNat target.toNat)))
    (hcode : extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  have hext :
      evalExpr? config { contract := contract, locals := locals } evm (.extCodeSize receiver) =
        .ok (.int (Int.ofNat (extCodeSizeWord evm.accountMap target).toNat)) := by
    rw [evalExpr?]
    rw [hreceiver]
    simp only [EvalResult.bind, bind, pure, extCodeSizeWord, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat]
    cases evm.accountMap.find? (AccountAddress.ofNat target.toNat) <;> rfl
  rw [hext]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap target).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalCodeSizeGuard_cage_false {locals : Store} {evm : EVM.State}
    {receiver : Expr} {target : UInt256}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address (AccountAddress.ofNat target.toNat)))
    (hnocode : extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  have hext :
      evalExpr? config { contract := contract, locals := locals } evm (.extCodeSize receiver) =
        .ok (.int (Int.ofNat (extCodeSizeWord evm.accountMap target).toNat)) := by
    rw [evalExpr?]
    rw [hreceiver]
    simp only [EvalResult.bind, bind, pure, extCodeSizeWord, State.lookupAccount,
      accountAddress_ofUInt256_eq_ofNat_toNat]
    cases evm.accountMap.find? (AccountAddress.ofNat target.toNat) <;> rfl
  rw [hext]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hzero : (extCodeSizeWord evm.accountMap target).toNat = 0 := by
    rw [hnocode]
    rfl
  simp [evalBinaryOp?, hzero]

abbrev endCageSlotTarget (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ slot) solcAddrMask

theorem endCagePackedSlotTarget_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (UInt256.div (storageRead I.codeOwner σ slot)
          (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))) =
      endCageSlotTarget σ I slot := by
  unfold endCageSlotTarget
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hdiv :
      UInt256.div (storageRead I.codeOwner σ slot)
          (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)) =
        storageRead I.codeOwner σ slot := by
    rw [show UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0) = (⟨1⟩ : UInt256)
      from by native_decide]
    apply u256_inj
    rw [udiv_toNat]
    exact Nat.div_one _
  rw [hmask, hdiv]
  let w := storageRead I.codeOwner σ slot
  calc
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w)
        = UInt256.land solcAddrMask (UInt256.land w solcAddrMask) := by
            rw [u256_land_comm solcAddrMask w]
    _ = UInt256.land (UInt256.land w solcAddrMask) solcAddrMask := by
            rw [u256_land_comm solcAddrMask (UInt256.land w solcAddrMask)]
    _ = UInt256.land w solcAddrMask :=
            solcAddrMask_clean (solcAddrMask_result_canonical w)

theorem endCageSimpleSlotTarget_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    UInt256.land (storageRead I.codeOwner σ slot)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) =
      endCageSlotTarget σ I slot := by
  unfold endCageSlotTarget
  rw [show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask from by native_decide]

abbrev endCageSlotCallRest (σ : AccountMap) (I : ExecutionEnv)
    (slot sel : UInt256) : List UInt256 :=
  [⟨132⟩, ⟨1763987465⟩, endCageSlotTarget σ I slot, ⟨562⟩, sel]

abbrev endCageSlotCallStack (σ : AccountMap) (I : ExecutionEnv)
    (slot sel : UInt256) : List UInt256 :=
  [endCageSlotTarget σ I slot, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨0⟩] ++
    endCageSlotCallRest σ I slot sel

abbrev endCageSlotCallCursor (pc : UInt256)
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (slot sel aw : UInt256) (rdata mem : ByteArray) : Cursor :=
  { pc := pc, stack := endCageSlotCallStack world.2 I slot sel,
    mem := endCageCallMem mem, aw := aw, rdata := rdata, world := world }

abbrev endCageAfterCatStatusCursor (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5791⟩,
    stack := endRuntimeBlocks.endRuntime_block_5775_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 2) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageAfterVatFrame : Frame :=
  { contract := contract,
    locals := (∅ : Store).insert "_vatCage" (collapseReturns []) }

abbrev endCageAfterCatFrame : Frame :=
  { contract := contract,
    locals := ((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns []) }

abbrev endCageAfterDogStatusCursor (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5895⟩,
    stack := endRuntimeBlocks.endRuntime_block_5879_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 3) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageAfterCatCheckedCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (rdata mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5791⟩,
    stack := endRuntimeBlocks.endRuntime_block_5775_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 2) sel),
    mem := mem,
    aw := aw, rdata := rdata, world := world }

abbrev endCageAfterDogFrame : Frame :=
  { contract := contract,
    locals := (((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns [])).insert "_dogCage" (collapseReturns []) }

abbrev endCageAfterVowStatusCursor (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5986⟩,
    stack := endRuntimeBlocks.endRuntime_block_5970_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 4) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageAfterDogCheckedCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (rdata mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5895⟩,
    stack := endRuntimeBlocks.endRuntime_block_5879_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 3) sel),
    mem := mem,
    aw := aw, rdata := rdata, world := world }

abbrev endCageAfterVowFrame : Frame :=
  { contract := contract,
    locals := ((((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns [])).insert "_dogCage" (collapseReturns [])).insert "_vowCage"
      (collapseReturns []) }

abbrev endCageAfterVowCheckedCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (rdata mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5986⟩,
    stack := endRuntimeBlocks.endRuntime_block_5970_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 4) sel),
    mem := mem,
    aw := aw, rdata := rdata, world := world }

abbrev endCageAfterSpotFrame : Frame :=
  { contract := contract,
    locals := (((((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns [])).insert "_dogCage" (collapseReturns [])).insert "_vowCage"
      (collapseReturns [])).insert "_spotCage" (collapseReturns []) }

abbrev endCageAfterSpotStatusCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6090⟩,
    stack := endRuntimeBlocks.endRuntime_block_6074_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 6) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageAfterSpotCheckedCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (rdata mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6090⟩,
    stack := endRuntimeBlocks.endRuntime_block_6074_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 6) sel),
    mem := mem,
    aw := aw, rdata := rdata, world := world }

abbrev endCageAfterPotFrame : Frame :=
  { contract := contract,
    locals := ((((((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns [])).insert "_dogCage" (collapseReturns [])).insert "_vowCage"
      (collapseReturns [])).insert "_spotCage" (collapseReturns [])).insert "_potCage"
      (collapseReturns []) }

abbrev endCageAfterPotStatusCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6194⟩,
    stack := endRuntimeBlocks.endRuntime_block_6178_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 5) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageAfterPotCheckedCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (rdata mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6194⟩,
    stack := endRuntimeBlocks.endRuntime_block_6178_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 5) sel),
    mem := mem,
    aw := aw, rdata := rdata, world := world }

abbrev endCageAfterCureFrame : Frame :=
  { contract := contract,
    locals := (((((((∅ : Store).insert "_vatCage" (collapseReturns [])).insert "_catCage"
      (collapseReturns [])).insert "_dogCage" (collapseReturns [])).insert "_vowCage"
      (collapseReturns [])).insert "_spotCage" (collapseReturns [])).insert "_potCage"
      (collapseReturns [])).insert "_cureCage" (collapseReturns []) }

abbrev endCageAfterCureStatusCursor
    (preWorld : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out mem : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6298⟩,
    stack := endRuntimeBlocks.endRuntime_block_6282_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest preWorld.2 I (UInt256.ofNat 7) sel),
    mem := endCageCallMem mem,
    aw := UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
        (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat),
    rdata := out,
    world := world }

abbrev endCageVatCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨132⟩, ⟨1763987465⟩, endCageVatTarget σ I, ⟨562⟩, sel]

abbrev endCageVatCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endCageVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨0⟩] ++
    endCageVatCallRest σ I sel

abbrev endCageVatCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨5669⟩, stack := endCageVatCallStack σ I sel,
    mem := endCageCallMem (endCageAuthMem I), aw := aw, rdata := rdata,
    world := (cA, endCagePostAccountMap σ I) }

abbrev endCageNoOutCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endCageAfterVatStatusCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5687⟩,
    stack := endRuntimeBlocks.endRuntime_block_5671_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCageVatCallRest σ I sel),
    mem := endCageCallMem (endCageAuthMem I), aw := endCageNoOutCallAw aw, rdata := out,
    world := world }

abbrev endCageAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩

abbrev endCagePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (endCageAfterLiveState evm)
    (endCageAfterLiveState evm).executionEnv.codeOwner ⟨9⟩
    (UInt256.ofNat (endCageAfterLiveState evm).executionEnv.header.timestamp)

theorem endEvalAuthStorage_cage (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage (wardsRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (wardsSlot (.address evm.executionEnv.source))).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [wardsRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wards (.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalAuthGuard_cage_true (evm : EVM.State)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_cage evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat = 1 := by
    rw [hauth]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalAuthGuard_cage_false (evm : EVM.State)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_cage evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat ≠ 1 := by
    intro hnat
    exact hauth (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalLiveStorage_cage (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage liveRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [liveRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, liveRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_live)]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalLiveGuard_cage_true (evm : EVM.State)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_cage evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat = 1 := by
    rw [hlive]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalLiveGuard_cage_false (evm : EVM.State)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_cage evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat ≠ 1 := by
    intro hnat
    exact hlive (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalNow_cage (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm nowT =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
  simp only [nowT, evalExpr?, envValue]
  rfl

theorem endAssignLiveZero_cage (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm
        .storage liveRef (.int (Int.ofNat (UInt256.ofNat 0).toNat)) =
      .ok ({ contract := contract, locals := (∅ : Store) },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩) := by
  rw [assignStorageRef_storage_scalar
    (slot := liveRef)
    (er := { base := "live", steps := [] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨8⟩)
    (n := Int.ofNat (UInt256.ofNat 0).toNat)
    (hbase := by simp [liveRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, liveRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_live)
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm ⟨8⟩ ⟨0⟩)]

theorem endAssignWhenNow_cage (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := (∅ : Store) } evm
        .storage whenRef
        (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) =
      .ok ({ contract := contract, locals := (∅ : Store) },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
          (UInt256.ofNat evm.executionEnv.header.timestamp)) := by
  rw [assignStorageRef_storage_scalar
    (slot := whenRef)
    (er := { base := "when", steps := [] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨9⟩)
    (n := Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbase := by simp [whenRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, whenRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_when)
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm ⟨9⟩ (UInt256.ofNat evm.executionEnv.header.timestamp))]

theorem endEvalVatAddress_cage (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := (∅ : Store) } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp [vatRef]) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat), endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_cage (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_cage evm]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases hacc : evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)
  · rfl
  · rfl

theorem endEvalVatCodeGuard_cage_false (evm : EVM.State)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_cage evm, hnocode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_cage_true (evm : EVM.State)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_cage evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endCageBodyAuthFail (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (∅ : Store) cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalAuthGuard_cage_false evm hauth)))

theorem endCageBodyLiveFail (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (∅ : Store) cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_cage_true evm hauth)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveGuard_cage_false evm hlive)))

theorem endCageBodyVatNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvatNoCode : extCodeSizeWord (endCagePostState evm).accountMap
        (UInt256.land
          (Solm.EVM.storageLoad (endCagePostState evm)
            (endCagePostState evm).executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (∅ : Store) cageTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth, endCagePostState, endCageAfterLiveState] using
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
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_cage_false (endCagePostState evm)
          hvatNoCode)))

theorem endX_cage_to_auth {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5433⟩
      [⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  exact ⟨_, _, endRuntimeBlocks.endRuntime_block_798 (R := [sel]) (by simp)
    (by jump_dest) rdEntry⟩

theorem endX_cage_auth_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : solcSlotWord σ I (endAuthSlot I) ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_cage_to_auth (g := g) hreach
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
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_5433_fallthrough
    (R := [⟨562⟩, sel]) (by simp) hcondAuth rdAuth
  exact endRuntimeBlocks.endRuntime_block_5457 (R := [⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_cage_live_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_cage_to_auth (g := g) hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_5433_taken
    (R := [⟨562⟩, sel]) (by simp) hcondAuth (by jump_dest) rdAuth
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 8)) =
        (UInt256.ofNat 0) := by
    have hlive' : solcSlotWord σ I (UInt256.ofNat 8) ≠ ⟨1⟩ := by
      simpa using hlive
    rw [storageRead_eq]
    change UInt256.eq (UInt256.ofNat 1) (solcSlotWord σ I (UInt256.ofNat 8)) =
      (UInt256.ofNat 0)
    exact uInt256_eq_zero_of_ne (by
      intro heq
      exact hlive' (uInt256_eq_one_eq heq).symm)
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_5522_fallthrough
    (R := [⟨562⟩, sel]) (by simp) hcondLive rdLive
  exact endRuntimeBlocks.endRuntime_block_5533 (R := [⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_cage_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hnocode : extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_cage_to_auth (g := g) hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_5433_taken
    (R := [⟨562⟩, sel]) (by simp) hcondAuth (by jump_dest) rdAuth
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠
        (UInt256.ofNat 0) := by
    have hlive' : solcSlotWord σ I (UInt256.ofNat 8) = ⟨1⟩ := by
      simpa using hlive
    rw [storageRead_eq]
    change UInt256.eq (UInt256.ofNat 1) (solcSlotWord σ I (UInt256.ofNat 8)) ≠
      (UInt256.ofNat 0)
    rw [hlive']
    decide
  obtain ⟨_, _, rdStoreEntry⟩ := endRuntimeBlocks.endRuntime_block_5522_taken
    (R := [⟨562⟩, sel]) (by simp) hcondLive (by jump_dest) rdLive
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondNoCode :
      UInt256.isZero (UInt256.isZero
        (extCodeSizeWord
          (storageWrite I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
            (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
          (UInt256.land
            (storageRead I.codeOwner
              (storageWrite I.codeOwner
                (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
                (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
              (UInt256.ofNat 1))
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1))))) = (UInt256.ofNat 0) := by
    rw [hmask]
    change UInt256.isZero (UInt256.isZero
      (extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I))) =
        (UInt256.ofNat 0)
    rw [hnocode]
    decide
  obtain ⟨_, _, rdNoCodeEntry⟩ := endRuntimeBlocks.endRuntime_block_5592_fallthrough
    (R := [⟨562⟩, sel]) (by simp) hperm hcondNoCode rdStoreEntry
  exact endRuntimeBlocks.endRuntime_block_5663
    (R := endRuntimeBlocks.endRuntime_block_5592_fallthrough_stack
      (ee := I)
      (mem := endRuntimeBlocks.endRuntime_block_5433_taken_memory (ee := I) (mem := solcFreePtrMem))
      (σ := σ)
      (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_5592_fallthrough_stack])
    rdNoCodeEntry

theorem endX_cage_to_vat_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvatCode : extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5669⟩
      [endCageVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨0⟩,
        ⟨132⟩, ⟨1763987465⟩, endCageVatTarget σ I, ⟨562⟩, sel]
      (endCageCallMem (endCageAuthMem I)) aw ByteArray.empty
      (cA, endCagePostAccountMap σ I) k C := by
  obtain ⟨_, _, rdAuth⟩ := endX_cage_to_auth (g := g) hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_5433_taken
    (R := [⟨562⟩, sel]) (by simp) hcondAuth (by jump_dest) rdAuth
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠
        (UInt256.ofNat 0) := by
    have hlive' : solcSlotWord σ I (UInt256.ofNat 8) = ⟨1⟩ := by
      simpa using hlive
    rw [storageRead_eq]
    change UInt256.eq (UInt256.ofNat 1) (solcSlotWord σ I (UInt256.ofNat 8)) ≠
      (UInt256.ofNat 0)
    rw [hlive']
    decide
  obtain ⟨_, _, rdStoreEntry⟩ := endRuntimeBlocks.endRuntime_block_5522_taken
    (R := [⟨562⟩, sel]) (by simp) hcondLive (by jump_dest) rdLive
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero (UInt256.isZero
        (extCodeSizeWord
          (storageWrite I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
            (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
          (UInt256.land
            (storageRead I.codeOwner
              (storageWrite I.codeOwner
                (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
                (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
              (UInt256.ofNat 1))
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0) := by
    rw [hmask]
    change UInt256.isZero (UInt256.isZero
      (extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I))) ≠ ⟨0⟩
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw5667, k5667, C5667, rd5667⟩ :=
    endRuntimeBlocks.endRuntime_block_5592_taken_packed
      (R := [⟨562⟩, sel]) (by simp) hperm hcondCode (by jump_dest) rdStoreEntry
  have hcallMemLoad :
      memLoad (UInt256.ofNat 64) (endCageCallMem (endCageAuthMem I)) = ⟨128⟩ :=
    endCageCallMem_mload64 (by rw [endCageAuthMem_size I])
      (endCageAuthMem_read64 I) (endCageAuthMem_mload64 I)
  have hauthLoadRaw :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_5433_taken_memory (ee := I) (mem := solcFreePtrMem)) =
          ⟨128⟩ := by
    simpa [endCageAuthMem] using endCageAuthMem_mload64 I
  have hcallMemLoadRaw :
      memLoad (UInt256.ofNat 64)
        (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
          (endRuntimeBlocks.endRuntime_block_5433_taken_memory (ee := I) (mem := solcFreePtrMem))
          (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
    simpa [endCageCallMem, endCageAuthMem, endCageSelectorWord,
      endCageAuthMem_mload64 I] using hcallMemLoad
  have hcallLen :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) + UInt256.ofNat 4 = ⟨4⟩ := by
    native_decide
  have hcallEnd : (⟨128⟩ : UInt256) + UInt256.ofNat 4 = ⟨132⟩ := by
    native_decide
  have hreadVatPostRaw :
      storageRead I.codeOwner
          (storageWrite I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
            (UInt256.ofNat 9) (UInt256.ofNat I.header.timestamp))
          (UInt256.ofNat 1) =
        storageRead I.codeOwner σ (UInt256.ofNat 1) := by
    rw [storageRead_storageWrite_ne I.codeOwner
      (storageWrite I.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0))
      (by native_decide)]
    rw [storageRead_storageWrite_ne I.codeOwner σ (by native_decide)]
  have hrd5667' :
      ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5667⟩
        (UInt256.isZero (extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I)) ::
          [endCageVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨0⟩,
            ⟨132⟩, ⟨1763987465⟩, endCageVatTarget σ I, ⟨562⟩, sel])
        (endCageCallMem (endCageAuthMem I)) aw ByteArray.empty
        (cA, endCagePostAccountMap σ I) k C := by
    refine ⟨aw5667, k5667, C5667, ?_⟩
    dsimp [endRuntimeBlocks.endRuntime_block_5592_taken_stack,
      endRuntimeBlocks.endRuntime_block_5592_taken_memory] at rd5667
    rw [hreadVatPostRaw, hauthLoadRaw, hcallMemLoadRaw, hcallLen, hcallEnd] at rd5667
    simpa [endCagePostAccountMap, endCageVatTarget, endCageCallMem, endCageAuthMem,
      endCageSelectorWord, hmask, endCageAuthMem_mload64 I] using rd5667
  obtain ⟨aw', k', C', rd5667'⟩ := hrd5667'
  have rd5669 := endRuntimeBlocks.endRuntime_block_5667
    (x0 := UInt256.isZero (extCodeSizeWord (endCagePostAccountMap σ I) (endCageVatTarget σ I)))
    (R := [endCageVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨0⟩,
      ⟨132⟩, ⟨1763987465⟩, endCageVatTarget σ I, ⟨562⟩, sel])
    (by simp) rd5667'
  exact ⟨aw', _, _, by simpa [endRuntimeBlocks.endRuntime_block_5667_stack] using rd5669⟩

theorem endCageVatExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageVatCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := (∅ : Store) } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "cage" (.intLit 0) [] "_vatCage" ]
      (sequenceExit ⟨5687⟩
        (fun cur frame e =>
          frame = endCageAfterVatFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5671_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageVatCallRest σ I sel) ∧
          cur.mem = endCageCallMem (endCageAuthMem I) ∧
          cur.aw = endCageNoOutCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5669⟩ = some (.GAS, .none); decide)
    (by simp) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageVatTarget σ I).toNat) (argVals := [])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5670⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp) (hRevert := trivial)
    (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [endEvalVatAddress_cage]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endCageVatTarget σ I).toNat))
    rw [hload]
    rw [endCagePostAccountMap_read_vat]
    rw [show (UInt256.ofNat 1) = (⟨1⟩ : UInt256) from by native_decide]
    rw [endCageVatTarget_eq_pre]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endCageVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector =
      some ((endCageCallMem (endCageAuthMem I)).readWithPadding 128 4)
    rw [endCageCallMem_readSelector (endCageAuthMem_mload64 I)]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd5687 := endRuntimeBlocks.endRuntime_block_5671_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageVatCallRest σ I sel)
      (by simp) (by native_decide) (by jump_dest)
      (by simpa [gasCursor, callCursor, endCageCallCopyZero, endCageVatCallStack] using rd)
    let frame' : Frame :=
      { contract := contract, locals := (∅ : Store).insert "_vatCage" (collapseReturns []) }
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterVatStatusCursor σ I sel aw out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by simpa [endCageAfterVatStatusCursor, endCageNoOutCallAw] using rd5687⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5678 := endRuntimeBlocks.endRuntime_block_5671_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageVatCallRest σ I sel)
      (by simp) (by native_decide)
      (by simpa [gasCursor, callCursor, endCageCallCopyZero, endCageVatCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_5678
      (R := endRuntimeBlocks.endRuntime_block_5671_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageVatCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5671_fallthrough_stack, endCageVatCallRest])
      rd5678

theorem endCageCatExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨5773⟩ world I (UInt256.ofNat 2) sel aw rdata mem)
      k C endCageAfterVatFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage catRef) "cage" (.intLit 0) [] "_catCage" ]
      (sequenceExit ⟨5791⟩
        (fun cur frame e =>
          frame = endCageAfterCatFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5775_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 2) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5773⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallCursor, endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 2)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5774⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 2)
    have hcat :
        evalExpr? config endCageAfterVatFrame evm (.storage catRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterVatFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterVatFrame.locals) (evm := evm)
          (slot := catRef) (er := { base := "cat", steps := [] })
          (wordSlot := UInt256.ofNat 2)
          (by simp [endCageAfterVatFrame, catRef])
          (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 2) = (⟨2⟩ : UInt256) from by native_decide]
            exact endConfig_storage_cat))
    rw [hcat]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 2)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 2)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 2)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd5791 := endRuntimeBlocks.endRuntime_block_5775_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 2) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterCatFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterCatStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterCatStatusCursor] using rd5791⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5782 := endRuntimeBlocks.endRuntime_block_5775_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 2) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_5782
      (R := endRuntimeBlocks.endRuntime_block_5775_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 2) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5775_fallthrough_stack,
        endCageSlotCallRest])
      rd5782

theorem endCageCatCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterVatStatusCursor σ I sel aw rdata world)
      k C endCageAfterVatFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      (checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage")
      (sequenceExit ⟨5791⟩
        (fun cur frame e =>
          frame = endCageAfterCatFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5775_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 2) sel) ∧
          cur.mem = endCageCallMem (endCageCallMem (endCageAuthMem I)))
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  let mem0 := endCageCallMem (endCageAuthMem I)
  have hmem0Load : memLoad (UInt256.ofNat 64) mem0 = ⟨128⟩ := by
    exact endCageCallMem_mload64 (by rw [endCageAuthMem_size I])
      (endCageAuthMem_read64 I) (endCageAuthMem_mload64 I)
  have hmem0Read : mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    exact endCageCallMem_read64 (by rw [endCageAuthMem_size I])
      (endCageAuthMem_read64 I) (endCageAuthMem_mload64 I)
  have hmem0Size : 96 ≤ mem0.size := by
    dsimp [mem0]
    exact endCageCallMem_size_ge96 (endCageAuthMem_mload64 I)
  have hmem1Load : memLoad (UInt256.ofNat 64) (endCageCallMem mem0) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmem0Size hmem0Read hmem0Load
  have hcatReceiver :
      evalExpr? config endCageAfterVatFrame evm (.storage catRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 2)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 2)
    have hcat :
        evalExpr? config endCageAfterVatFrame evm (.storage catRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterVatFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterVatFrame.locals) (evm := evm)
          (slot := catRef) (er := { base := "cat", steps := [] })
          (wordSlot := UInt256.ofNat 2)
          (by simp [endCageAfterVatFrame, catRef])
          (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 2) = (⟨2⟩ : UInt256) from by native_decide]
            exact endConfig_storage_cat))
    rw [hcat]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 2)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 2)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 2)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage catRef) hcatReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterVatFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)),
            Stmt.externalCall (.storage catRef) "cage" (.intLit 0) [] "_catCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 2))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) =
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd5767⟩ := endRuntimeBlocks.endRuntime_block_5687_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256)) (x3 := endCageVatTarget σ I)
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterVatStatusCursor, endRuntimeBlocks.endRuntime_block_5671_taken_stack,
          endCageVatCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_5767
      (R := endRuntimeBlocks.endRuntime_block_5687_fallthrough_stack
        (ee := I) (mem := mem0) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_5687_fallthrough_stack])
      rd5767
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 2)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage catRef) hcatReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterVatFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)))
          (.ok endCageAfterVatFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 2))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) ≠
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k5771, C5771, rd5771⟩ := endRuntimeBlocks.endRuntime_block_5687_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256)) (x3 := endCageVatTarget σ I)
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterVatStatusCursor, endRuntimeBlocks.endRuntime_block_5671_taken_stack,
          endCageVatCallRest] using rd)
    have hselector :
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295)
            (UInt256.ofNat 1763987465)) (UInt256.ofNat 224) = endCageSelectorWord := by
      native_decide
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem0 = ⟨132⟩ := by
      rw [hmem0Load]
      native_decide
    have hcallLen :
        UInt256.sub (UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem0)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem0)) = ⟨4⟩ := by
      rw [hmem0Load, hmem1Load]
      native_decide
    have hmem0LoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [mem0, endCageCallMem, endCageSelectorWord, endCageAuthMem_mload64 I]
        using hmem0Load
    have hmem1LoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32)
            (memLoad (UInt256.ofNat 64)
              (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
                (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32)).toNat 32) = ⟨128⟩ := by
      simpa [mem0, endCageCallMem, endCageSelectorWord, endCageAuthMem_mload64 I,
        hmem0LoadRaw] using hmem1Load
    have hmem1LoadRaw128 :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32)
            (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [hmem0LoadRaw] using hmem1LoadRaw
    have hcallEndRaw :
        UInt256.ofNat 4 +
          memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32) = ⟨132⟩ := by
      rw [hmem0LoadRaw]
      native_decide
    have hcallLenRaw :
        UInt256.sub
          (UInt256.ofNat 4 +
            memLoad (UInt256.ofNat 64)
              (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
                (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32))
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
                (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32)
              (memLoad (UInt256.ofNat 64)
                (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
                  (endCageAuthMem I) (⟨128⟩ : UInt256).toNat 32)).toNat 32)) = ⟨4⟩ := by
      rw [hmem0LoadRaw, hmem1LoadRaw128]
      native_decide
    have rd5771' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5771⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 2))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 2) sel)
          (endCageCallMem mem0)
          (M (M (M (endCageNoOutCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k5771 C5771 := by
      simpa [endRuntimeBlocks.endRuntime_block_5687_taken_stack,
        endRuntimeBlocks.endRuntime_block_5687_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, mem0, endCageCallMem, endCageSelectorWord,
        endCagePackedSlotTarget_eq, hselector, endCageAuthMem_mload64 I,
        hmem0Load, hmem1Load, hmem0LoadRaw, hmem1LoadRaw, hmem1LoadRaw128,
        hcallEnd, hcallLen, hcallEndRaw, hcallLenRaw]
        using rd5771
    have rd5773 := endRuntimeBlocks.endRuntime_block_5771
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 2))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 2) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd5771'
    have htail := endCageCatExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M (endCageNoOutCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k5771 + 2) (C := C5771 + 3) (evm := evm)
      (mem := mem0) (world := world) hperm hmem0Load
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_5771_stack] using rd5773)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCageDogExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨5877⟩ world I (UInt256.ofNat 3) sel aw rdata mem)
      k C endCageAfterCatFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ]
      (sequenceExit ⟨5895⟩
        (fun cur frame e =>
          frame = endCageAfterDogFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5879_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 3) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5877⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 3)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5878⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 3)
    have hdog :
        evalExpr? config endCageAfterCatFrame evm (.storage dogRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterCatFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterCatFrame.locals) (evm := evm)
          (slot := dogRef) (er := { base := "dog", steps := [] })
          (wordSlot := UInt256.ofNat 3)
          (by simp [endCageAfterCatFrame, dogRef])
          (by simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 3) = (⟨3⟩ : UInt256) from by native_decide]
            exact endConfig_storage_dog))
    rw [hdog]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 3)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 3)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 3)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd5895 := endRuntimeBlocks.endRuntime_block_5879_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 3) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterDogFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterDogStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterDogStatusCursor] using rd5895⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5886 := endRuntimeBlocks.endRuntime_block_5879_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 3) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_5886
      (R := endRuntimeBlocks.endRuntime_block_5879_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 3) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5879_fallthrough_stack,
        endCageSlotCallRest])
      rd5886

theorem endCageDogCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
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
      (checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage")
      (sequenceExit ⟨5895⟩
        (fun cur frame e =>
          frame = endCageAfterDogFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5879_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 3) sel) ∧
          cur.mem = endCageCallMem mem
        )
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  have hnextMemLoad : memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hdogReceiver :
      evalExpr? config endCageAfterCatFrame evm (.storage dogRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 3)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 3)
    have hdog :
        evalExpr? config endCageAfterCatFrame evm (.storage dogRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterCatFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterCatFrame.locals) (evm := evm)
          (slot := dogRef) (er := { base := "dog", steps := [] })
          (wordSlot := UInt256.ofNat 3)
          (by simp [dogRef])
          (by simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 3) = (⟨3⟩ : UInt256) from by native_decide]
            exact endConfig_storage_dog))
    rw [hdog]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 3)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 3)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 3)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage dogRef) hdogReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterCatFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)),
            Stmt.externalCall (.storage dogRef) "cage" (.intLit 0) [] "_dogCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 3))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) =
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd5871⟩ := endRuntimeBlocks.endRuntime_block_5791_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 2))
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterCatCheckedCursor, endRuntimeBlocks.endRuntime_block_5775_taken_stack,
          endCageSlotCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_5871
      (R := endRuntimeBlocks.endRuntime_block_5791_fallthrough_stack
        (ee := I) (mem := mem) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_5791_fallthrough_stack])
      rd5871
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 3)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage dogRef) hdogReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterCatFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)))
          (.ok endCageAfterCatFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 3))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) ≠
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k5875, C5875, rd5875⟩ := endRuntimeBlocks.endRuntime_block_5791_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 2))
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterCatCheckedCursor, endRuntimeBlocks.endRuntime_block_5775_taken_stack,
          endCageSlotCallRest] using rd)
    have hselector :
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295)
            (UInt256.ofNat 1763987465)) (UInt256.ofNat 224) = endCageSelectorWord := by
      native_decide
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem = ⟨132⟩ := by
      rw [hmemLoad]
      native_decide
    have hcallLen :
        UInt256.sub (UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem)) = ⟨4⟩ := by
      rw [hmemLoad, hnextMemLoad]
      native_decide
    have hnextMemLoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            mem (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [endCageCallMem, endCageSelectorWord, hmemLoad] using hnextMemLoad
    have hcallLenRaw :
        (UInt256.ofNat 4 + (⟨128⟩ : UInt256)).sub
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              mem (⟨128⟩ : UInt256).toNat 32)) = ⟨4⟩ := by
      rw [hnextMemLoadRaw]
      native_decide
    have rd5875' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5875⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 3))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 3) sel)
          (endCageCallMem mem)
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k5875 C5875 := by
      simpa [endRuntimeBlocks.endRuntime_block_5791_taken_stack,
        endRuntimeBlocks.endRuntime_block_5791_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, endCageCallMem, endCageSelectorWord,
        endCagePackedSlotTarget_eq, hselector, hmemLoad, hnextMemLoad,
        hnextMemLoadRaw, hcallEnd, hcallLen, hcallLenRaw]
        using rd5875
    have rd5877 := endRuntimeBlocks.endRuntime_block_5875
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 3))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 3) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd5875'
    have htail := endCageDogExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k5875 + 2) (C := C5875 + 3) (evm := evm)
      (mem := mem) (world := world) hperm hmemLoad
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_5875_stack] using rd5877)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCageVowExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨5968⟩ world I (UInt256.ofNat 4) sel aw rdata mem)
      k C endCageAfterDogFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ]
      (sequenceExit ⟨5986⟩
        (fun cur frame e =>
          frame = endCageAfterVowFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5970_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 4) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5968⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 4)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5969⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    have hvow :
        evalExpr? config endCageAfterDogFrame evm (.storage vowRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterDogFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterDogFrame.locals) (evm := evm)
          (slot := vowRef) (er := { base := "vow", steps := [] })
          (wordSlot := UInt256.ofNat 4)
          (by simp [vowRef])
          (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 4) = (⟨4⟩ : UInt256) from by native_decide]
            exact endConfig_storage_vow))
    rw [hvow]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 4)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 4)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 4)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd5986 := endRuntimeBlocks.endRuntime_block_5970_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 4) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterVowFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterVowStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterVowStatusCursor] using rd5986⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5977 := endRuntimeBlocks.endRuntime_block_5970_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 4) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_5977
      (R := endRuntimeBlocks.endRuntime_block_5970_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 4) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5970_fallthrough_stack,
        endCageSlotCallRest])
      rd5977

theorem endCageVowCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
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
      (checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage")
      (sequenceExit ⟨5986⟩
        (fun cur frame e =>
          frame = endCageAfterVowFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_5970_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 4) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  have hnextMemLoad : memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hvowReceiver :
      evalExpr? config endCageAfterDogFrame evm (.storage vowRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 4)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 4)
    have hvow :
        evalExpr? config endCageAfterDogFrame evm (.storage vowRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterDogFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterDogFrame.locals) (evm := evm)
          (slot := vowRef) (er := { base := "vow", steps := [] })
          (wordSlot := UInt256.ofNat 4)
          (by simp [vowRef])
          (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 4) = (⟨4⟩ : UInt256) from by native_decide]
            exact endConfig_storage_vow))
    rw [hvow]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 4)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 4)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 4)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage vowRef) hvowReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterDogFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage vowRef)) (.intLit 0)),
            Stmt.externalCall (.storage vowRef) "cage" (.intLit 0) [] "_vowCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 4))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))))) = (UInt256.ofNat 0) := by
      rw [endCageSimpleSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd5962⟩ := endRuntimeBlocks.endRuntime_block_5895_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 3))
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterDogCheckedCursor, endRuntimeBlocks.endRuntime_block_5879_taken_stack,
          endCageSlotCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_5962
      (R := endRuntimeBlocks.endRuntime_block_5895_fallthrough_stack
        (ee := I) (mem := mem) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_5895_fallthrough_stack])
      rd5962
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 4)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage vowRef) hvowReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterDogFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage vowRef)) (.intLit 0)))
          (.ok endCageAfterDogFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 4))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))))) ≠ (UInt256.ofNat 0) := by
      rw [endCageSimpleSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k5966, C5966, rd5966⟩ := endRuntimeBlocks.endRuntime_block_5895_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 3))
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterDogCheckedCursor, endRuntimeBlocks.endRuntime_block_5879_taken_stack,
          endCageSlotCallRest] using rd)
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem = ⟨132⟩ := by
      rw [hmemLoad]
      native_decide
    have hcallLen :
        UInt256.sub (memLoad (UInt256.ofNat 64) mem)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem)) + UInt256.ofNat 4 = ⟨4⟩ := by
      rw [hmemLoad, hnextMemLoad]
      native_decide
    have hnextMemLoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            mem (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [endCageCallMem, endCageSelectorWord, hmemLoad] using hnextMemLoad
    have hcallLenRaw :
        ((UInt256.sub (⟨128⟩ : UInt256)
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              mem (⟨128⟩ : UInt256).toNat 32))) + UInt256.ofNat 4) = ⟨4⟩ := by
      rw [hnextMemLoadRaw]
      native_decide
    have rd5966' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5966⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 4))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 4) sel)
          (endCageCallMem mem)
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k5966 C5966 := by
      simpa [endRuntimeBlocks.endRuntime_block_5895_taken_stack,
        endRuntimeBlocks.endRuntime_block_5895_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, endCageCallMem, endCageSelectorWord,
        endCageSimpleSlotTarget_eq, hmemLoad, hnextMemLoad,
        hnextMemLoadRaw, hcallEnd, hcallLen, hcallLenRaw]
        using rd5966
    have rd5968 := endRuntimeBlocks.endRuntime_block_5966
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 4))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 4) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd5966'
    have htail := endCageVowExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k5966 + 2) (C := C5966 + 3) (evm := evm)
      (mem := mem) (world := world) hperm hmemLoad
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_5966_stack] using rd5968)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCageSpotExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨6072⟩ world I (UInt256.ofNat 6) sel aw rdata mem)
      k C endCageAfterVowFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ]
      (sequenceExit ⟨6090⟩
        (fun cur frame e =>
          frame = endCageAfterSpotFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6074_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 6) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨6072⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 6)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨6073⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 6)
    have hspot :
        evalExpr? config endCageAfterVowFrame evm (.storage spotRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterVowFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterVowFrame.locals) (evm := evm)
          (slot := spotRef) (er := { base := "spot", steps := [] })
          (wordSlot := UInt256.ofNat 6)
          (by simp [spotRef])
          (by simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 6) = (⟨6⟩ : UInt256) from by native_decide]
            exact endConfig_storage_spot))
    rw [hspot]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 6)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 6)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 6)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd6090 := endRuntimeBlocks.endRuntime_block_6074_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 6) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterSpotFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterSpotStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterSpotStatusCursor] using rd6090⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd6081 := endRuntimeBlocks.endRuntime_block_6074_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 6) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_6081
      (R := endRuntimeBlocks.endRuntime_block_6074_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 6) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_6074_fallthrough_stack,
        endCageSlotCallRest])
      rd6081

theorem endCageSpotCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
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
      (checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage")
      (sequenceExit ⟨6090⟩
        (fun cur frame e =>
          frame = endCageAfterSpotFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6074_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 6) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  have hnextMemLoad : memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hspotReceiver :
      evalExpr? config endCageAfterVowFrame evm (.storage spotRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 6)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 6)
    have hspot :
        evalExpr? config endCageAfterVowFrame evm (.storage spotRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterVowFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterVowFrame.locals) (evm := evm)
          (slot := spotRef) (er := { base := "spot", steps := [] })
          (wordSlot := UInt256.ofNat 6)
          (by simp [spotRef])
          (by simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 6) = (⟨6⟩ : UInt256) from by native_decide]
            exact endConfig_storage_spot))
    rw [hspot]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 6)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 6)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 6)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage spotRef) hspotReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterVowFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)),
            Stmt.externalCall (.storage spotRef) "cage" (.intLit 0) [] "_spotCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 6))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) =
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd6066⟩ := endRuntimeBlocks.endRuntime_block_5986_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 4))
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterVowCheckedCursor, endRuntimeBlocks.endRuntime_block_5970_taken_stack,
          endCageSlotCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_6066
      (R := endRuntimeBlocks.endRuntime_block_5986_fallthrough_stack
        (ee := I) (mem := mem) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_5986_fallthrough_stack])
      rd6066
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 6)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage spotRef) hspotReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterVowFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)))
          (.ok endCageAfterVowFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 6))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) ≠
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k6070, C6070, rd6070⟩ := endRuntimeBlocks.endRuntime_block_5986_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 4))
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterVowCheckedCursor, endRuntimeBlocks.endRuntime_block_5970_taken_stack,
          endCageSlotCallRest] using rd)
    have hselector :
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295)
            (UInt256.ofNat 1763987465)) (UInt256.ofNat 224) = endCageSelectorWord := by
      native_decide
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem = ⟨132⟩ := by
      rw [hmemLoad]
      native_decide
    have hcallLen :
        UInt256.sub (UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem)) = ⟨4⟩ := by
      rw [hmemLoad, hnextMemLoad]
      native_decide
    have hnextMemLoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            mem (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [endCageCallMem, endCageSelectorWord, hmemLoad] using hnextMemLoad
    have hcallLenRaw :
        UInt256.sub (UInt256.ofNat 4 + (⟨128⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              mem (⟨128⟩ : UInt256).toNat 32)) = ⟨4⟩ := by
      rw [hnextMemLoadRaw]
      native_decide
    have rd6070' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6070⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 6))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 6) sel)
          (endCageCallMem mem)
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k6070 C6070 := by
      simpa [endRuntimeBlocks.endRuntime_block_5986_taken_stack,
        endRuntimeBlocks.endRuntime_block_5986_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, endCageCallMem, endCageSelectorWord,
        endCagePackedSlotTarget_eq, hselector, hmemLoad, hnextMemLoad,
        hnextMemLoadRaw, hcallEnd, hcallLen, hcallLenRaw]
        using rd6070
    have rd6072 := endRuntimeBlocks.endRuntime_block_6070
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 6))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 6) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd6070'
    have htail := endCageSpotExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k6070 + 2) (C := C6070 + 3) (evm := evm)
      (mem := mem) (world := world) hperm hmemLoad
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_6070_stack] using rd6072)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCagePotExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨6176⟩ world I (UInt256.ofNat 5) sel aw rdata mem)
      k C endCageAfterSpotFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage potRef) "cage" (.intLit 0) [] "_potCage" ]
      (sequenceExit ⟨6194⟩
        (fun cur frame e =>
          frame = endCageAfterPotFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6178_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 5) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨6176⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 5)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨6177⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 5)
    have hpot :
        evalExpr? config endCageAfterSpotFrame evm (.storage potRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterSpotFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterSpotFrame.locals) (evm := evm)
          (slot := potRef) (er := { base := "pot", steps := [] })
          (wordSlot := UInt256.ofNat 5)
          (by simp [potRef])
          (by simp [evalStorageRef, evalStorageRefSteps, potRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 5) = (⟨5⟩ : UInt256) from by native_decide]
            exact endConfig_storage_pot))
    rw [hpot]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 5)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 5)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 5)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd6194 := endRuntimeBlocks.endRuntime_block_6178_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 5) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterPotFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterPotStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterPotStatusCursor] using rd6194⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd6185 := endRuntimeBlocks.endRuntime_block_6178_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 5) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_6185
      (R := endRuntimeBlocks.endRuntime_block_6178_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 5) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_6178_fallthrough_stack,
        endCageSlotCallRest])
      rd6185

theorem endCagePotCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
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
      (checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage")
      (sequenceExit ⟨6194⟩
        (fun cur frame e =>
          frame = endCageAfterPotFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6178_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 5) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  have hnextMemLoad : memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hpotReceiver :
      evalExpr? config endCageAfterSpotFrame evm (.storage potRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 5)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 5)
    have hpot :
        evalExpr? config endCageAfterSpotFrame evm (.storage potRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterSpotFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterSpotFrame.locals) (evm := evm)
          (slot := potRef) (er := { base := "pot", steps := [] })
          (wordSlot := UInt256.ofNat 5)
          (by simp [potRef])
          (by simp [evalStorageRef, evalStorageRefSteps, potRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 5) = (⟨5⟩ : UInt256) from by native_decide]
            exact endConfig_storage_pot))
    rw [hpot]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 5)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 5)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 5)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage potRef) hpotReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterSpotFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage potRef)) (.intLit 0)),
            Stmt.externalCall (.storage potRef) "cage" (.intLit 0) [] "_potCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 5))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) =
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd6170⟩ := endRuntimeBlocks.endRuntime_block_6090_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 6))
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterSpotCheckedCursor, endRuntimeBlocks.endRuntime_block_6074_taken_stack,
          endCageSlotCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_6170
      (R := endRuntimeBlocks.endRuntime_block_6090_fallthrough_stack
        (ee := I) (mem := mem) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_6090_fallthrough_stack])
      rd6170
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 5)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage potRef) hpotReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterSpotFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage potRef)) (.intLit 0)))
          (.ok endCageAfterSpotFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 5))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) ≠
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k6174, C6174, rd6174⟩ := endRuntimeBlocks.endRuntime_block_6090_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 6))
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterSpotCheckedCursor, endRuntimeBlocks.endRuntime_block_6074_taken_stack,
          endCageSlotCallRest] using rd)
    have hselector :
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295)
            (UInt256.ofNat 1763987465)) (UInt256.ofNat 224) = endCageSelectorWord := by
      native_decide
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem = ⟨132⟩ := by
      rw [hmemLoad]
      native_decide
    have hcallLen :
        UInt256.sub (UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem)) = ⟨4⟩ := by
      rw [hmemLoad, hnextMemLoad]
      native_decide
    have hnextMemLoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            mem (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [endCageCallMem, endCageSelectorWord, hmemLoad] using hnextMemLoad
    have hcallLenRaw :
        UInt256.sub (UInt256.ofNat 4 + (⟨128⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              mem (⟨128⟩ : UInt256).toNat 32)) = ⟨4⟩ := by
      rw [hnextMemLoadRaw]
      native_decide
    have rd6174' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6174⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 5))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 5) sel)
          (endCageCallMem mem)
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k6174 C6174 := by
      simpa [endRuntimeBlocks.endRuntime_block_6090_taken_stack,
        endRuntimeBlocks.endRuntime_block_6090_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, endCageCallMem, endCageSelectorWord,
        endCagePackedSlotTarget_eq, hselector, hmemLoad, hnextMemLoad,
        hnextMemLoadRaw, hcallEnd, hcallLen, hcallLenRaw]
        using rd6174
    have rd6176 := endRuntimeBlocks.endRuntime_block_6174
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 5))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 5) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd6174'
    have htail := endCagePotExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k6174 + 2) (C := C6174 + 3) (evm := evm)
      (mem := mem) (world := world) hperm hmemLoad
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_6174_stack] using rd6176)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCageCureExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hmemLoad : memLoad (UInt256.ofNat 64) mem = ⟨128⟩) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageSlotCallCursor ⟨6280⟩ world I (UInt256.ofNat 7) sel aw rdata mem)
      k C endCageAfterPotFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage cureRef) "cage" (.intLit 0) [] "_cureCage" ]
      (sequenceExit ⟨6298⟩
        (fun cur frame e =>
          frame = endCageAfterCureFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6282_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 7) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨6280⟩ = some (.GAS, .none); decide)
    (by simp [endCageSlotCallStack]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 7)).toNat)
    (argVals := []) (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨6281⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageSlotCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endCageSlotLoad_eq_of_callRel h (UInt256.ofNat 7)
    have hcure :
        evalExpr? config endCageAfterPotFrame evm (.storage cureRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterPotFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterPotFrame.locals) (evm := evm)
          (slot := cureRef) (er := { base := "cure", steps := [] })
          (wordSlot := UInt256.ofNat 7)
          (by simp [cureRef])
          (by simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 7) = (⟨7⟩ : UInt256) from by native_decide]
            exact endConfig_storage_cure))
    rw [hcure]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 7)).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rfl
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endCageSlotTarget world.2 I (UInt256.ofNat 7)).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endCageSlotTarget world.2 I (UInt256.ofNat 7)).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_cage]
    change some cageSelector = some ((endCageCallMem mem).readWithPadding 128 4)
    rw [endCageCallMem_readSelector hmemLoad]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_cage out]
    intro rd hrel
    have rd6298 := endRuntimeBlocks.endRuntime_block_6282_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 7) sel)
      (by simp [endCageSlotCallRest]) (by native_decide) (by jump_dest)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    let frame' : Frame :=
      endCageAfterCureFrame
    refine ⟨.ok frame' evm',
      Endpoint.reached (endCageAfterCureStatusCursor world I sel aw out mem world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endCageAfterCureStatusCursor] using rd6298⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd6289 := endRuntimeBlocks.endRuntime_block_6282_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endCageSlotCallRest world.2 I (UInt256.ofNat 7) sel)
      (by simp [endCageSlotCallRest]) (by native_decide)
      (by
        simpa [gasCursor, callCursor, endCageCallCopyZero, endCageSlotCallCursor,
          endCageSlotCallStack] using rd)
    exact endRuntimeBlocks.endRuntime_block_6289
      (R := endRuntimeBlocks.endRuntime_block_6282_fallthrough_stack (x0 := (⟨0⟩ : UInt256))
        (R := endCageSlotCallRest world.2 I (UInt256.ofNat 7) sel))
      (by simp [endRuntimeBlocks.endRuntime_block_6282_fallthrough_stack,
        endCageSlotCallRest])
      rd6289

theorem endCageCureCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
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
      (sequenceExit ⟨6298⟩
        (fun cur frame e =>
          frame = endCageAfterCureFrame ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6282_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCageSlotCallRest world.2 I (UInt256.ofNat 7) sel) ∧
          cur.mem = endCageCallMem mem)
        (runtimeExit (.abi []))) := by
  intro rd hrel
  unfold checkedExternalCallStmts
  have hnextMemLoad : memLoad (UInt256.ofNat 64) (endCageCallMem mem) = ⟨128⟩ := by
    exact endCageCallMem_mload64 hmemSize hmemRead hmemLoad
  have hcureReceiver :
      evalExpr? config endCageAfterPotFrame evm (.storage cureRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageSlotTarget world.2 I (UInt256.ofNat 7)).toNat)) := by
    have hload := endCageSlotLoad_eq_of_callRel hrel (UInt256.ofNat 7)
    have hcure :
        evalExpr? config endCageAfterPotFrame evm (.storage cureRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
            solcAddrMask).toNat)) := by
      simpa [endCageAfterPotFrame] using
        (endEvalAddressSlot_cage
          (locals := endCageAfterPotFrame.locals) (evm := evm)
          (slot := cureRef) (er := { base := "cure", steps := [] })
          (wordSlot := UInt256.ofNat 7)
          (by simp [cureRef])
          (by simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind])
          (by decide)
          (by
            rw [show (UInt256.ofNat 7) = (⟨7⟩ : UInt256) from by native_decide]
            exact endConfig_storage_cure))
    rw [hcure]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageSlotTarget world.2 I (UInt256.ofNat 7)).toNat))
    rw [hload]
  by_cases hcodeZero :
      extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 7)) = ⟨0⟩
  · have hsourceCodeZero :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 7)) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hcodeZero
    have hguard :=
      endEvalCodeSizeGuard_cage_false (receiver := .storage cureRef) hcureReceiver hsourceCodeZero
    have hsource :
        ExecBlock config endCageAfterPotFrame evm
          [Stmt.require (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)),
            Stmt.externalCall (.storage cureRef) "cage" (.intLit 0) [] "_cureCage"] .reverted :=
      ExecBlock.consRevert (ExecStmt.requireFalse hguard)
    have hcondNoCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 7))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) =
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq, hcodeZero]
      native_decide
    obtain ⟨_, _, rd6274⟩ := endRuntimeBlocks.endRuntime_block_6194_fallthrough
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 5))
      (R := [⟨562⟩, sel]) (by simp) hcondNoCode
      (by
        simpa [endCageAfterPotCheckedCursor, endRuntimeBlocks.endRuntime_block_6178_taken_stack,
          endCageSlotCallRest] using rd)
    have rdrev := endRuntimeBlocks.endRuntime_block_6274
      (R := endRuntimeBlocks.endRuntime_block_6194_fallthrough_stack
        (ee := I) (mem := mem) (σ := world.2) (R := [⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_6194_fallthrough_stack])
      rd6274
    exact ⟨.reverted, .reverted, hsource, rdrev,
      by simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsourceCode :
        extCodeSizeWord evm.accountMap (endCageSlotTarget world.2 I (UInt256.ofNat 7)) ≠ ⟨0⟩ := by
      intro hz
      exact hcodeZero (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cage_true (receiver := .storage cureRef) hcureReceiver hsourceCode
    have hsourceStmt :
        ExecStmt config endCageAfterPotFrame evm
          (Stmt.require (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)))
          (.ok endCageAfterPotFrame evm) :=
      ExecStmt.requireTrue hguard
    have hcondCode :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (UInt256.div (storageRead I.codeOwner world.2 (UInt256.ofNat 7))
                  (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) ≠
          (UInt256.ofNat 0) := by
      rw [endCagePackedSlotTarget_eq]
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeZero]
      native_decide
    obtain ⟨k6278, C6278, rd6278⟩ := endRuntimeBlocks.endRuntime_block_6194_taken
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
      (x2 := (⟨1763987465⟩ : UInt256))
      (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 5))
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest)
      (by
        simpa [endCageAfterPotCheckedCursor, endRuntimeBlocks.endRuntime_block_6178_taken_stack,
          endCageSlotCallRest] using rd)
    have hselector :
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295)
            (UInt256.ofNat 1763987465)) (UInt256.ofNat 224) = endCageSelectorWord := by
      native_decide
    have hcallEnd : UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem = ⟨132⟩ := by
      rw [hmemLoad]
      native_decide
    have hcallLen :
        UInt256.sub (UInt256.ofNat 4 + memLoad (UInt256.ofNat 64) mem)
          (memLoad (UInt256.ofNat 64) (endCageCallMem mem)) = ⟨4⟩ := by
      rw [hmemLoad, hnextMemLoad]
      native_decide
    have hnextMemLoadRaw :
        memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
            mem (⟨128⟩ : UInt256).toNat 32) = ⟨128⟩ := by
      simpa [endCageCallMem, endCageSelectorWord, hmemLoad] using hnextMemLoad
    have hcallLenRaw :
        UInt256.sub (UInt256.ofNat 4 + (⟨128⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            (((UInt256.ofNat 1763987465).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              mem (⟨128⟩ : UInt256).toNat 32)) = ⟨4⟩ := by
      rw [hnextMemLoadRaw]
      native_decide
    have rd6278' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6278⟩
          (UInt256.isZero
            (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 7))) ::
            endCageSlotCallStack world.2 I (UInt256.ofNat 7) sel)
          (endCageCallMem mem)
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
            (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
            (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          rdata world k6278 C6278 := by
      simpa [endRuntimeBlocks.endRuntime_block_6194_taken_stack,
        endRuntimeBlocks.endRuntime_block_6194_taken_memory, endCageSlotCallStack,
        endCageSlotCallRest, endCageCallMem, endCageSelectorWord,
        endCagePackedSlotTarget_eq, hselector, hmemLoad, hnextMemLoad,
        hnextMemLoadRaw, hcallEnd, hcallLen, hcallLenRaw]
        using rd6278
    have rd6280 := endRuntimeBlocks.endRuntime_block_6278
      (x0 := UInt256.isZero
        (extCodeSizeWord world.2 (endCageSlotTarget world.2 I (UInt256.ofNat 7))))
      (R := endCageSlotCallStack world.2 I (UInt256.ofNat 7) sel)
      (by simp [endCageSlotCallStack, endCageSlotCallRest]) rd6278'
    have htail := endCageCureExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel)
      (aw := (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (⟨128⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256)))
      (rdata := rdata) (k := k6278 + 2) (C := C6278 + 3) (evm := evm)
      (mem := mem) (world := world) hperm hmemLoad
    exact BlockProgress.cons hsourceStmt
      (htail
        (by simpa [endRuntimeBlocks.endRuntime_block_6278_stack] using rd6280)
        (by simpa [endCageSlotCallCursor] using hrel))

theorem endCageFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm mem}
    {preWorld world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageAfterCureStatusCursor preWorld I sel aw rdata mem world)
      k C endCageAfterCureFrame evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [] (runtimeExit (.abi [])) := by
  intro rd hrel
  have rd562 := endRuntimeBlocks.endRuntime_block_6298
    (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨132⟩ : UInt256))
    (x2 := (⟨1763987465⟩ : UInt256))
    (x3 := endCageSlotTarget preWorld.2 I (UInt256.ofNat 7))
    (x4 := (⟨562⟩ : UInt256)) (R := [sel])
    (by simp) hperm (by jump_dest)
    (by
      simpa [endCageAfterCureStatusCursor, endRuntimeBlocks.endRuntime_block_6282_taken_stack,
        endCageSlotCallRest] using rd)
  have rdret := endRuntimeBlocks.endRuntime_block_562
    (R := [sel]) (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_6298_stack] using rd562)
  exact BlockProgress.ofRDret ExecBlock.nil rdret
    (by simpa [endCageAfterCureStatusCursor] using hrel.created.symm)
    (by simpa [endCageAfterCureStatusCursor] using hrel.accounts)
    abiVoidFallthrough

end Benchmarks.Dss.End
