import Benchmarks.Dss.Flapper.Tick
import Benchmarks.Dss.Flapper.RuntimeBlocks_003
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

def flapperYankIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperYankLocals (id : UInt256) : Store :=
  (∅ : Store).insert "id" (.int (Int.ofNat id.toNat))

def flapperYankBaseSlot (id : UInt256) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 1) id

theorem flapperKeyValueToWord_uint256_natCast (id : UInt256) :
    keyValueToWord (KeyValue.int ↑id.toNat) = id := by
  simpa using keyValueToWord_uint256 id

theorem flapperYankBidsBase_eq (id : UInt256) :
    bidsBase (.int (Int.ofNat id.toNat)) = flapperYankBaseSlot id := by
  unfold bidsBase mapSlot
  rw [keyValueToWord_uint256]
  change solcMappingSlot (⟨1⟩ : UInt256) id = flapperYankBaseSlot id
  unfold flapperYankBaseSlot
  rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 by decide]

def flapperYankBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperYankBaseSlot (flapperYankIdWord I))

def flapperYankBidWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flapperYankBaseSlot id)

def flapperYankPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperYankBaseSlot (flapperYankIdWord I) + UInt256.ofNat 2)

def flapperYankPackedWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (flapperYankBaseSlot id + UInt256.ofNat 2)

def flapperYankGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperYankPackedWord σ I) flapperAddressMask

def flapperYankGuyWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.land (flapperYankPackedWordOfState evm id) flapperAddressMask

def flapperYankGemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 3)) solcAddrMask

def flapperYankGemWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
    solcAddrMask

def flapperYankLiveWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7)

abbrev flapperYankMoveSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)

def flapperYankHashMem (id : UInt256) : ByteArray :=
  flapperRuntimeBlocks.flapperRuntime_block_964_taken_memory
    (mem := solcFreePtrMem) (x0 := id)

def flapperYankCallBaseMem (id : UInt256) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0
    (id.toByteArray.write 0 (flapperYankHashMem id) (UInt256.ofNat 0).toNat 32)
    (UInt256.ofNat 32).toNat 32

def flapperYankCallMemSelector (id : UInt256) : ByteArray :=
  flapperYankMoveSelectorWord.toByteArray.write 0 (flapperYankCallBaseMem id) 128 32

def flapperYankCallMemThis (I : ExecutionEnv) (id : UInt256) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (flapperYankCallMemSelector id) 132 32

def flapperYankCallMemGuy (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperYankGuyWord σ I).toByteArray.write 0
    (flapperYankCallMemThis I (flapperYankIdWord I)) 164 32

def flapperYankMoveCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperYankBidWord σ I).toByteArray.write 0
    (flapperYankCallMemGuy σ I) 196 32

def flapperYankCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [UInt256.ofNat 228, UInt256.ofNat 3140843579, flapperYankGemWord σ I,
    flapperYankIdWord I, UInt256.ofNat 360, sel]

def flapperYankDeletedAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let base := flapperYankBaseSlot (flapperYankIdWord I)
  storageWrite I.codeOwner
    (storageWrite I.codeOwner
      (storageWrite I.codeOwner σ base (UInt256.ofNat 0))
      (base + UInt256.ofNat 1) (UInt256.ofNat 0))
    (UInt256.ofNat 2 + base) (UInt256.ofNat 0)

def flapperYankPackedSlot (id : UInt256) : UInt256 :=
  flapperYankBaseSlot id + UInt256.ofNat 2

def flapperYankDeleteBidLotState (evm : EVM.State) (id : UInt256) : EVM.State :=
  let base := flapperYankBaseSlot id
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner base (UInt256.ofNat 0))
    evm.executionEnv.codeOwner (base + UInt256.ofNat 1) (UInt256.ofNat 0)

def flapperYankDeleteGuyState (evm : EVM.State) (id : UInt256) : EVM.State :=
  let evm' := flapperYankDeleteBidLotState evm id
  let packed := flapperYankPackedSlot id
  Solm.EVM.storageStore evm' evm.executionEnv.codeOwner packed
    (UInt256.land
      (Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner packed)
      (UInt256.lnot solcAddrMask))

def flapperUint48Offset20ClearWord (old : UInt256) : UInt256 :=
  UInt256.ofNat (old.toNat % 2 ^ 160 + (old.toNat / 2 ^ 208) * 2 ^ 208)

def flapperYankDeleteTicState (evm : EVM.State) (id : UInt256) : EVM.State :=
  let evm' := flapperYankDeleteGuyState evm id
  let packed := flapperYankPackedSlot id
  Solm.EVM.storageStore evm' evm.executionEnv.codeOwner packed
    (flapperUint48Offset20ClearWord
      (Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner packed))

def flapperYankDeleteState (evm : EVM.State) (id : UInt256) : EVM.State :=
  let evm' := flapperYankDeleteTicState evm id
  let packed := flapperYankPackedSlot id
  Solm.EVM.storageStore evm' evm.executionEnv.codeOwner packed
    (UInt256.land
      (Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner packed)
      (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))

theorem flapperStorageLocStore_of_valueToWord_eq
    (evm : EVM.State) (loc : StorageLoc) (v₁ v₂ : Value)
    (h : valueToWord v₁ = valueToWord v₂) :
    storageLocStore evm loc v₁ = storageLocStore evm loc v₂ := by
  unfold storageLocStore
  rw [h]

theorem flapperAddrLoc_eq_addressOffset0Loc (slot : UInt256) :
    addrLoc slot = addressOffset0Loc slot := by
  unfold addrLoc addressOffset0Loc
  congr

theorem flapperStorageLocStore_word_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (wordLoc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat 0)) := by
  simpa [wordLoc, uint256Loc] using
    storageLocStore_uint256 evm slot (UInt256.ofNat 0)

theorem flapperStorageLocStore_address_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addrLoc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot solcAddrMask))) := by
  rw [flapperAddrLoc_eq_addressOffset0Loc]
  trans storageLocStore evm (addressOffset0Loc slot) (.address (AccountAddress.ofNat 0))
  · apply flapperStorageLocStore_of_valueToWord_eq
    simp only [valueToWord]
    rw [wordOfInt_zero]
    decide
  · have h := storageLocStore_address_offset0 evm slot (UInt256.ofNat 0) (by decide)
    simpa [addrLoc, setAddressOffset0Word,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by decide,
      show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = (⟨0⟩ : UInt256) by decide,
      u256_lor_zero] using h

theorem flapperLow160Mask_mod_eq_land (w : UInt256) :
    w.toNat % 2 ^ 160 =
      (UInt256.land w (UInt256.ofNat (2 ^ 160 - 1))).toNat := by
  rw [uland_toNat]
  have hmask : (UInt256.ofNat (2 ^ 160 - 1)).toNat = 2 ^ 160 - 1 := by
    native_decide
  rw [hmask]
  exact (nat_land_mask_eq_mod w.toNat 160).symm

theorem flapperUint48Offset20ClearWord_toNat (old : UInt256) :
    (flapperUint48Offset20ClearWord old).toNat =
      old.toNat % 2 ^ 160 + (old.toNat / 2 ^ 208) * 2 ^ 208 := by
  unfold flapperUint48Offset20ClearWord
  have hsumLt :
      old.toNat % 2 ^ 160 + (old.toNat / 2 ^ 208) * 2 ^ 208 <
        UInt256.size := by
    have hlowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 160))
    have hq : old.toNat / 2 ^ 208 < 2 ^ 48 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by
        rw [← Nat.pow_add]]
      exact old.val.isLt
    have hqle : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hq
    have hqterm :
        old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  exact ulit_toNat' _ hsumLt

theorem flapperStorageLocStore_uint48_offset20_zero
    (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (flapperUint48Offset20ClearWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_zero, bind, Option.bind, pure]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  have htakeOldLen :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have htakeZeroLen :
      ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2]
    norm_num
  congr 2
  apply u256_inj
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20 ++
        (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 6 ++
        (EVM.Word.toBytesLEWithSizeProof old).1.drop 26) =
      (flapperUint48Offset20ClearWord old).toNat
  rw [fromBytes'_append, fromBytes'_append,
    fromBytes'_take_wordLE_land_mask old 20 (by decide),
    fromBytes'_take_wordLE_land_mask (⟨0⟩ : UInt256) 6 (by decide),
    fromBytes'_drop_wordLE, List.length_append, htakeOldLen, htakeZeroLen]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num,
    show 2 ^ (8 * (20 + 6)) = 2 ^ 208 by norm_num,
    show 256 ^ 26 = 2 ^ 208 by norm_num]
  rw [← flapperLow160Mask_mod_eq_land old,
    show (UInt256.land (⟨0⟩ : UInt256) (UInt256.ofNat (2 ^ (8 * 6) - 1))).toNat = 0 by
      native_decide,
    flapperUint48Offset20ClearWord_toNat]
  ring

theorem flapperStorageLocStore_uint48_offset20_zero_any
    (evm : EVM.State) (slot : UInt256)
    {hbound : (20 : Fin 32).val + 6 - 1 < 32} :
    storageLocStore evm (uint48Loc slot (20 : Fin 32) hbound) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (flapperUint48Offset20ClearWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  have hloc :
      uint48Loc slot (20 : Fin 32) hbound =
        uint48Loc slot ⟨20, by decide⟩ (by decide) := by
    unfold uint48Loc
    congr
  rw [hloc]
  exact flapperStorageLocStore_uint48_offset20_zero evm slot

theorem flapperStorageLocStore_uint48_offset26_zero
    (evm : EVM.State) (slot : UInt256)
    {hbound : (26 : Fin 32).val + 6 - 1 < 32} :
    storageLocStore evm (uint48Loc slot (26 : Fin 32) hbound) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))) := by
  have hloc :
      uint48Loc slot (26 : Fin 32) hbound =
        uint48Loc slot ⟨26, by decide⟩ (by decide) := by
    unfold uint48Loc
    congr
  rw [hloc]
  have hstore := flapperStorageLocStore_uint48_offset26 evm slot (UInt256.ofNat 0)
  rw [show UInt256.land (UInt256.ofNat 0) flapperUint48Mask = (⟨0⟩ : UInt256) by
      native_decide] at hstore
  rw [show UInt256.mul flapperUint48Shift208 (⟨0⟩ : UInt256) = (⟨0⟩ : UInt256) by
      native_decide] at hstore
  rw [u256_lor_zero] at hstore
  simpa using hstore

theorem flapperYankDeleteStorage (evm : EVM.State) (id : UInt256) :
    deleteStorage? config
      { contract := contract, locals := flapperYankLocals id } evm
      (bidRef (.var "id")) =
      .ok (flapperYankDeleteState evm id) := by
  let locals := flapperYankLocals id
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat))] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperYankLocals]
  have her : evalStorageRef config solm evm (bidRef (.var "id")) = .ok er := by
    simp [solm, er, bidRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, locals, flapperYankLocals]
  have hty : storageTypeAt? contract.storage er = some BidStructTy := by
    simp [er, contract, storageDecls, storageTypeAt?, storageTypeStep?, BidStructTy,
      uint256St, addrSt, uint48St]
  change deleteStorage? config solm evm (bidRef (.var "id")) =
    .ok (flapperYankDeleteState evm id)
  rw [deleteStorage?]
  simp only [resolveStorageRef?_ok (cfg := config) (solm := solm) (evm := evm)
    (slot := bidRef (.var "id")) (er := er) (ty := BidStructTy) hbase her hty,
    bind, EvalResult.bind]
  simp [solm, locals, er, clearStorage?, clearFields?, config, storageLayout,
    solidityStorageLayout, storageLayoutRaw, contract, storageDecls, BidStructTy,
    uint256St, addrSt, uint48St, flapperYankDeleteState,
    flapperYankDeleteTicState, flapperYankDeleteGuyState,
    flapperYankDeleteBidLotState, flapperYankPackedSlot, flapperYankBaseSlot,
    flapperStorageLocStore_word_zero, flapperStorageLocStore_address_zero, EvalResult.ofOption,
    flapperStorageLocStore_uint48_offset20_zero_any,
    flapperStorageLocStore_uint48_offset26_zero, storageStore_executionEnv]
  simpa [bidsBase, mapSlot, flapperKeyValueToWord_uint256_natCast, solcMappingSlot,
    show ({ val := 1 } : UInt256) = UInt256.ofNat 1 by decide,
    show ({ val := 2 } : UInt256) = UInt256.ofNat 2 by decide]

theorem flapperYankDeleteStorage_afterMoveRet (evm : EVM.State) (id : UInt256) :
    deleteStorage? config
      { contract := contract,
        locals := (flapperYankLocals id).insert "_moveRet" (collapseReturns []) } evm
      (bidRef (.var "id")) =
      .ok (flapperYankDeleteState evm id) := by
  let locals := (flapperYankLocals id).insert "_moveRet" (collapseReturns [])
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat))] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperYankLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    change ((flapperYankLocals id).insert "_moveRet" (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat id.toNat))
    rw [store_get_ne (flapperYankLocals id) (k := "_moveRet") (a := "id")
      (collapseReturns []) (by decide)]
    exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have her : evalStorageRef config solm evm (bidRef (.var "id")) = .ok er := by
    simp [solm, er, bidRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, hbase, hgetIdElem]
  have hty : storageTypeAt? contract.storage er = some BidStructTy := by
    simp [er, contract, storageDecls, storageTypeAt?, storageTypeStep?, BidStructTy,
      uint256St, addrSt, uint48St]
  change deleteStorage? config solm evm (bidRef (.var "id")) =
    .ok (flapperYankDeleteState evm id)
  rw [deleteStorage?]
  simp only [resolveStorageRef?_ok (cfg := config) (solm := solm) (evm := evm)
    (slot := bidRef (.var "id")) (er := er) (ty := BidStructTy) hbase her hty,
    bind, EvalResult.bind]
  simp [solm, locals, er, clearStorage?, clearFields?, config, storageLayout,
    solidityStorageLayout, storageLayoutRaw, contract, storageDecls, BidStructTy,
    uint256St, addrSt, uint48St, flapperYankDeleteState,
    flapperYankDeleteTicState, flapperYankDeleteGuyState,
    flapperYankDeleteBidLotState, flapperYankPackedSlot, flapperYankBaseSlot,
    flapperStorageLocStore_word_zero, flapperStorageLocStore_address_zero, EvalResult.ofOption,
    flapperStorageLocStore_uint48_offset20_zero_any,
    flapperStorageLocStore_uint48_offset26_zero, storageStore_executionEnv]
  simpa [bidsBase, mapSlot, flapperKeyValueToWord_uint256_natCast, solcMappingSlot,
    show ({ val := 1 } : UInt256) = UInt256.ofNat 1 by decide,
    show ({ val := 2 } : UInt256) = UInt256.ofNat 2 by decide]

theorem flapperX_yank_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 890)
      (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd331⟩ := hreach
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
  have rd353 := flapperRuntimeBlocks.flapperRuntime_block_331_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd331
  have rd890raw := flapperRuntimeBlocks.flapperRuntime_block_353
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd353
  exact ⟨_, _, by simpa [flapperYankIdWord, calldataWord] using rd890raw⟩

theorem flapperX_yank_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd331⟩ := hreach
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
  have rd349 := flapperRuntimeBlocks.flapperRuntime_block_331_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd331
  exact flapperRuntimeBlocks.flapperRuntime_block_349
    (R := flapperRuntimeBlocks.flapperRuntime_block_331_fallthrough_stack
      (ee := I) (R := [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_331_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd349

theorem flapperDispatch_yank {cd : ByteArray}
    (hsel : ((⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some yankTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition,
      kickTransition, kicksTransition, lidTransition, liveTransition,
      relyTransition, tauTransition, tendTransition, tickTransition,
      ttlTransition, vatTransition, wardsTransition])
    (post := [])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [flapperWardsSelectorBytes, hcd]; decide
  · rw [flapperYankSelectorBytes]
    exact hsel

theorem flapperSelectorDispatch_yank {cd : ByteArray}
    (hsel : ((⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some yankTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList]
  rw [show contract.transitions =
      [begTransition, bidsTransition, cageTransition, dealTransition,
        denyTransition, fileTransition, fillTransition, gemTransition,
        kickTransition, kicksTransition, lidTransition, liveTransition,
        relyTransition, tauTransition, tendTransition, tickTransition,
        ttlTransition, vatTransition, wardsTransition] ++ yankTransition :: [] by rfl]
  refine dispatchList_eq_some_of_split ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [flapperWardsSelectorBytes, hcd]; decide
  · rw [flapperYankSelectorBytes]
    exact hsel

theorem flapperDecode_yank_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata =
      some (flapperYankLocals (flapperYankIdWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata =
    some (flapperYankLocals (flapperYankIdWord I))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      flapperYankIdWord I := by
    simpa [flapperYankIdWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["id"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (start := 0) htake4]
  change decodeCalldata.insertValues ["id"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)]
      ∅ =
    some (flapperYankLocals (flapperYankIdWord I))
  rw [hword4]
  simp [decodeCalldata.insertValues, flapperYankLocals]

theorem flapperDecode_yank_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (yankTransition.params.map Param.name)
      (transitionSignature yankTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["id"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short
    (mode := DecodeMode.legacySolc05) (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperYankLive_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.storage liveRef) =
      .ok (.int (Int.ofNat (flapperYankLiveWordOfState evm).toNat)) := by
  let locals := flapperYankLocals id
  let er : EvaledStorageRef := { base := "live", steps := [] }
  have hbase : locals.get? "live" = none := by
    simp [locals, flapperYankLocals]
  have her : evalStorageRef config { contract := contract, locals := locals } evm liveRef =
      .ok er := by
    simp [locals, er, evalStorageRef, evalStorageRefSteps, liveRef,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er =
      fun _ => some (wordLoc (⟨7⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [locals, flapperYankLiveWordOfState,
    show (⟨7⟩ : UInt256) = UInt256.ofNat 7 by decide]

theorem flapperYankBid_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (flapperYankBidWordOfState evm id).toNat)) := by
  let locals := flapperYankLocals id
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperYankLocals]
  have herBid :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "bid") = .ok erBid := by
    simp [locals, erBid, flapperYankLocals, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, bidsF, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperYankBaseSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperYankBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herBid) (hty := htyBid) (hloc := hlocBid),
    flapperStorageLocLoad_uint256]
  simp [locals, flapperYankBidWordOfState]

theorem flapperYankGuy_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat
        (flapperYankGuyWordOfState evm id).toNat)) := by
  let locals := flapperYankLocals id
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperYankLocals]
  have herGuy :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [locals, erGuy, flapperYankLocals, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, bidsF, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have htyGuy : storageTypeAt? contract.storage erGuy =
      some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperYankPackedSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperYankPackedSlot, flapperYankBaseSlot]
    rw [hkey]
    change addrLoc
        (uInt256OfByteArray (ffi.KEC
          (id.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2) =
      addrLoc (solcMappingSlot (UInt256.ofNat 1) id + UInt256.ofNat 2)
    rfl
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := herGuy) (hty := htyGuy) (hloc := hlocGuy),
    flapperStorageLocLoad_address]
  simp [locals, flapperYankGuyWordOfState, flapperYankPackedWordOfState,
    flapperYankPackedSlot]

theorem flapperYankGem_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat
        (flapperYankGemWordOfState evm).toNat)) := by
  let locals := flapperYankLocals id
  let er : EvaledStorageRef := { base := "gem", steps := [] }
  have hbase : locals.get? "gem" = none := by
    simp [locals, flapperYankLocals]
  have her : evalStorageRef config { contract := contract, locals := locals } evm gemRef =
      .ok er := by
    simp [locals, er, evalStorageRef, evalStorageRefSteps, gemRef,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    decide
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨3⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_address]
  simp [locals, flapperYankGemWordOfState,
    show (⟨3⟩ : UInt256) = UInt256.ofNat 3 by decide]

theorem flapperYankZeroAddr_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, evalExpr?, addrSt, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem flapperYankLiveGuard_eval_true (evm : EVM.State) (id : UInt256)
    (hlive : flapperYankLiveWordOfState evm = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool true) := by
  have hLiveEval := flapperYankLive_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLiveEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLiveEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_true (flapperYankLiveWordOfState evm) hlive]

theorem flapperYankLiveGuard_eval_false (evm : EVM.State) (id : UInt256)
    (hlive : flapperYankLiveWordOfState evm ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool false) := by
  have hLiveEval := flapperYankLive_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLiveEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLiveEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_false (flapperYankLiveWordOfState evm) hlive]

theorem flapperAccountAddress_ofNat_ne_zero_of_canonical {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hzero : w ≠ UInt256.ofNat 0) :
    AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  apply hzero
  have hval := congrArg Fin.val haddr
  have hmod : w.toNat % AccountAddress.size = 0 := by
    simpa [AccountAddress.ofNat, Fin.ofNat] using hval
  have hltAddr : w.toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hnat : w.toNat = 0 := by
    simpa [Nat.mod_eq_of_lt hltAddr] using hmod
  apply u256_inj
  rw [hnat]
  rfl

theorem flapperYankGuyGuard_eval_true (evm : EVM.State) (id : UInt256)
    (hguy : flapperYankGuyWordOfState evm id ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
      .ok (.bool true) := by
  let guy := flapperYankGuyWordOfState evm id
  have hGuyEval := flapperYankGuy_eval evm id
  have hZeroEval := flapperYankZeroAddr_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval
  have hcanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flapperYankGuyWordOfState, flapperYankPackedWordOfState] using
      solcAddrMask_result_canonical
        (flapperYankPackedWordOfState evm id)
  have haddrNe : AccountAddress.ofNat guy.toNat ≠ AccountAddress.ofNat 0 :=
    flapperAccountAddress_ofNat_ne_zero_of_canonical hcanon (by simpa [guy] using hguy)
  have hvalNe :
      (Value.address (AccountAddress.ofNat guy.toNat)) ≠
        Value.address (AccountAddress.ofNat 0) := by
    intro h
    injection h with haddr
    exact haddrNe haddr
  have hbeq :
      ((Value.address (AccountAddress.ofNat guy.toNat)) ==
          Value.address (AccountAddress.ofNat 0)) = false := by
    cases h :
        ((Value.address (AccountAddress.ofNat guy.toNat)) ==
          Value.address (AccountAddress.ofNat 0))
    · rfl
    · exact False.elim (hvalNe (beq_iff_eq.mp h))
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuyEval, hZeroEval]
  simp [guy, hbeq]

theorem flapperYankGuyGuard_eval_false (evm : EVM.State) (id : UInt256)
    (hguy : flapperYankGuyWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
      .ok (.bool false) := by
  have hGuyEval := flapperYankGuy_eval evm id
  have hZeroEval := flapperYankZeroAddr_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuyEval, hZeroEval]
  have haddr :
      AccountAddress.ofNat (flapperYankGuyWordOfState evm id).toNat =
        AccountAddress.ofNat 0 := by
    rw [hguy]
    rfl
  simpa [flapperYankGuyWordOfState, flapperYankPackedWordOfState] using haddr

theorem flapperYankArgs_eval (evm : EVM.State) (id : UInt256) :
    evalExprs? config { contract := contract, locals := flapperYankLocals id } evm
        [thisAddr, .storage (bidsF (.var "id") "guy"), .storage (bidsF (.var "id") "bid")] =
      .ok [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (flapperYankGuyWordOfState evm id).toNat),
        .int (Int.ofNat (flapperYankBidWordOfState evm id).toNat)] := by
  have hGuyEval := flapperYankGuy_eval evm id
  have hBidEval := flapperYankBid_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval hBidEval
  simp only [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind, bind, pure]
  rw [hGuyEval, hBidEval]

theorem flapperYankExtCodeSizeWord_eval (evm : EVM.State) (targetWord : UInt256) :
    EVM.Word.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
          (fun acc => acc.code.size)) =
      extCodeSizeWord evm.accountMap targetWord := by
  unfold extCodeSizeWord State.lookupAccount
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find? (AccountAddress.ofNat targetWord.toNat) <;> rfl

theorem flapperYankExtGuard_true (evm : EVM.State) (id : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperYankGemWordOfState evm) ≠
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let targetWord := flapperYankGemWordOfState evm
  have hreceiver := flapperYankGem_eval evm id
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperYankExtCodeSizeWord_eval evm targetWord
  have hpos :
      0 <
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hcodeSize
    simpa [targetWord, hword] using
      (uint256_toNat_eq_zero (a := extCodeSizeWord evm.accountMap targetWord) (by
        rw [← hword]
        exact hzero))
  simp only [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hgt :
      decide (Int.ofNat
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat > 0) = true := by
    have hposInt :
        (0 : Int) <
          Int.ofNat
            (EVM.Word.ofNat
              ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
                (fun acc => acc.code.size))).toNat := by
      norm_num
      exact hpos
    exact decide_eq_true hposInt
  simpa [targetWord, hgt]

theorem flapperYankExtGuard_false (evm : EVM.State) (id : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperYankGemWordOfState evm) =
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperYankLocals id } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let targetWord := flapperYankGemWordOfState evm
  have hreceiver := flapperYankGem_eval evm id
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperYankExtCodeSizeWord_eval evm targetWord
  have hzero :
      (EVM.Word.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hword, hcodeSize]
    rfl
  simp only [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hgt :
      decide (Int.ofNat
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat > 0) = false := by
    exact decide_eq_false (by
      intro hpos
      rw [hzero] at hpos
      norm_num at hpos)
  simpa [targetWord, hgt]

theorem flapperYankPrefixOk (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperYankLiveWordOfState evm = UInt256.ofNat 0)
    (hguy : flapperYankGuyWordOfState evm id ≠ UInt256.ofNat 0) :
    ExecBlock config
      { contract := contract, locals := flapperYankLocals id } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ])
      (.ok { contract := contract, locals := flapperYankLocals id } evm) := by
  let solm : Frame := { contract := contract, locals := flapperYankLocals id }
  have hLiveGuard := flapperYankLiveGuard_eval_true evm id hlive
  have hGuyGuard := flapperYankGuyGuard_eval_true evm id hguy
  simpa [nonpayable, solm] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuyGuard) ExecBlock.nil :
      ExecBlock config solm evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ]
        (.ok solm evm))

theorem flapperYankBodyRevertsLive (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperYankLiveWordOfState evm ≠ UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperYankLocals id)
      yankTransition.body .reverted := by
  let locals := flapperYankLocals id
  let solm : Frame := { contract := contract, locals := locals }
  have hguard := flapperYankLiveGuard_eval_false evm id hlive
  exact ExecFuncBody.execBlockRevert <| by
    simpa [yankTransition, nonpayable, checkedExternalCallStmts, locals, solm] using
      nonpayableSecondRequireReverts (cfg := config) (solm := solm) (evm := evm)
        (guard := .binary .eq (.storage liveRef) (.intLit 0))
        (rest :=
          [ .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr),
            .require (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)),
            .externalCall (.storage gemRef) "move" (.intLit 0)
              [thisAddr, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_moveRet",
            .delete (bidRef (.var "id")) ])
        hwv hguard

theorem flapperYankBodyRevertsGuy (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperYankLiveWordOfState evm = UInt256.ofNat 0)
    (hguy : flapperYankGuyWordOfState evm id = UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperYankLocals id)
      yankTransition.body .reverted := by
  let locals := flapperYankLocals id
  let solm : Frame := { contract := contract, locals := locals }
  have hLiveGuard := flapperYankLiveGuard_eval_true evm id hlive
  have hGuyGuard := flapperYankGuyGuard_eval_false evm id hguy
  exact ExecFuncBody.execBlockRevert <| by
    simpa [yankTransition, nonpayable, checkedExternalCallStmts, locals, solm] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hGuyGuard) :
        ExecBlock config solm evm
          (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
            .require (.binary .eq (.storage liveRef) (.intLit 0)) ::
            .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ::
            checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [thisAddr, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_moveRet" ++
            [ .delete (bidRef (.var "id")) ])
          .reverted)

theorem flapperYankBodyRevertsNoCode (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperYankLiveWordOfState evm = UInt256.ofNat 0)
    (hguy : flapperYankGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperYankGemWordOfState evm) =
        UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperYankLocals id)
      yankTransition.body .reverted := by
  let locals := flapperYankLocals id
  let solm : Frame := { contract := contract, locals := locals }
  have hpref :
      ExecBlock config solm evm
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
            .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ])
        (.ok solm evm) := by
    simpa [solm, locals] using flapperYankPrefixOk evm id hwv hlive hguy
  have hguard := flapperYankExtGuard_false evm id hcodeSize
  have htail :
      ExecBlock config solm evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet")
        .reverted := by
    simpa [checkedExternalCallStmts, solm, locals] using
      checkedExternalCallNoCode (cfg := config) (C := contract)
        (evm := evm) (locals := locals) (receiver := .storage gemRef)
        (name := "move") (sendVal := 0)
        (args := [thisAddr, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        (retVar := "_moveRet") hguard
  have htailDelete :
      ExecBlock config solm evm
        (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
          [thisAddr, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_moveRet" ++
          [ .delete (bidRef (.var "id")) ])
        .reverted := by
    exact execBlock_append_term htail (by intro f e h; cases h)
  exact ExecFuncBody.execBlockRevert <| by
    simpa [yankTransition, nonpayable, checkedExternalCallStmts, solm, locals] using
      execBlock_append hpref htailDelete

theorem flapperStorageLoad_storageStore_same_zero_preserving
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256)
    (hzero : Solm.EVM.storageLoad evm addr slot = UInt256.ofNat 0 → val = UInt256.ofNat 0) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm addr slot val) addr slot = val := by
  cases hacc : evm.accountMap.find? addr with
  | none =>
    have hload0 : Solm.EVM.storageLoad evm addr slot = UInt256.ofNat 0 := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hacc, Option.option]
      apply u256_inj
      rfl
    have hval := hzero hload0
    rw [hval]
    simp [Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, hacc,
      Option.option]
    apply u256_inj
    rfl
  | some acc =>
    exact storageLoad_storageStore_same_present evm addr hacc slot val

theorem flapperYankDeleteGuyState_load_packed (evm : EVM.State) (id : UInt256) :
    Solm.EVM.storageLoad (flapperYankDeleteGuyState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id) =
      UInt256.land
        (Solm.EVM.storageLoad (flapperYankDeleteBidLotState evm id)
          evm.executionEnv.codeOwner (flapperYankPackedSlot id))
        (UInt256.lnot solcAddrMask) := by
  dsimp [flapperYankDeleteGuyState]
  exact flapperStorageLoad_storageStore_same_zero_preserving
    (flapperYankDeleteBidLotState evm id) evm.executionEnv.codeOwner
    (flapperYankPackedSlot id)
    (UInt256.land
      (Solm.EVM.storageLoad (flapperYankDeleteBidLotState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id))
      (UInt256.lnot solcAddrMask))
    (by
      intro hzero
      rw [hzero]
      native_decide)

theorem flapperYankDeleteTicState_load_packed (evm : EVM.State) (id : UInt256) :
    Solm.EVM.storageLoad (flapperYankDeleteTicState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id) =
      flapperUint48Offset20ClearWord
        (Solm.EVM.storageLoad (flapperYankDeleteGuyState evm id)
          evm.executionEnv.codeOwner (flapperYankPackedSlot id)) := by
  dsimp [flapperYankDeleteTicState]
  exact flapperStorageLoad_storageStore_same_zero_preserving
    (flapperYankDeleteGuyState evm id) evm.executionEnv.codeOwner
    (flapperYankPackedSlot id)
    (flapperUint48Offset20ClearWord
      (Solm.EVM.storageLoad (flapperYankDeleteGuyState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id)))
    (by
      intro hzero
      rw [hzero]
      unfold flapperUint48Offset20ClearWord
      native_decide)

theorem flapperYankDeleteTicState_low208_zero (evm : EVM.State) (id : UInt256) :
    (Solm.EVM.storageLoad (flapperYankDeleteTicState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id)).toNat % 2 ^ 208 = 0 := by
  rw [flapperYankDeleteTicState_load_packed, flapperYankDeleteGuyState_load_packed]
  let old :=
    Solm.EVM.storageLoad (flapperYankDeleteBidLotState evm id)
      evm.executionEnv.codeOwner (flapperYankPackedSlot id)
  have hlow160 :
      (UInt256.land old (UInt256.lnot solcAddrMask)).toNat % 2 ^ 160 = 0 := by
    rw [addressOffset0High160Mask_toNat]
    simpa using Nat.mul_mod_right (old.toNat / 2 ^ 160) (2 ^ 160)
  rw [flapperUint48Offset20ClearWord_toNat, hlow160, Nat.zero_add]
  simpa using Nat.mul_mod_right
    ((UInt256.land old (UInt256.lnot solcAddrMask)).toNat / 2 ^ 208) (2 ^ 208)

theorem flapperYankDeleteEndValue_zero (evm : EVM.State) (id : UInt256) :
    UInt256.land
        (Solm.EVM.storageLoad (flapperYankDeleteTicState evm id)
          evm.executionEnv.codeOwner (flapperYankPackedSlot id))
        (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)) =
      UInt256.ofNat 0 := by
  apply u256_inj
  rw [uland_toNat]
  have hmask :
      (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)).toNat = 2 ^ 208 - 1 := by
    native_decide
  rw [hmask]
  change Nat.land
      (Solm.EVM.storageLoad (flapperYankDeleteTicState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id)).toNat
      (2 ^ 208 - 1) = (UInt256.ofNat 0).toNat
  rw [nat_land_mask_eq_mod, flapperYankDeleteTicState_low208_zero]
  rfl

theorem flapperYankDeleteState_accountMap_eq (evm : EVM.State) (id : UInt256) :
    (flapperYankDeleteState evm id).accountMap =
      let base := flapperYankBaseSlot id
      let packed := flapperYankPackedSlot id
      let evmBase := flapperYankDeleteBidLotState evm id
      let w1 :=
        UInt256.land
          (Solm.EVM.storageLoad evmBase evm.executionEnv.codeOwner packed)
          (UInt256.lnot solcAddrMask)
      let w2 :=
        flapperUint48Offset20ClearWord
          (Solm.EVM.storageLoad (flapperYankDeleteGuyState evm id)
            evm.executionEnv.codeOwner packed)
      sstoreAccountMap evm.executionEnv.codeOwner
        (sstoreAccountMap evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner
            (sstoreAccountMap evm.executionEnv.codeOwner
              (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap base
                (UInt256.ofNat 0))
              (base + UInt256.ofNat 1) (UInt256.ofNat 0))
            packed w1)
          packed w2)
        packed (UInt256.ofNat 0) := by
  dsimp [flapperYankDeleteState]
  rw [flapperYankDeleteEndValue_zero]
  simp only [flapperYankDeleteTicState, flapperYankDeleteGuyState,
    flapperYankDeleteBidLotState, storageStore_accountMap, storageStore_executionEnv]

theorem flapperYankDeleteState_createdAccounts (evm : EVM.State) (id : UInt256) :
    (flapperYankDeleteState evm id).createdAccounts = evm.createdAccounts := by
  simp [flapperYankDeleteState, flapperYankDeleteTicState, flapperYankDeleteGuyState,
    flapperYankDeleteBidLotState, storageStore_createdAccounts]

theorem flapperYankDeleteState_accountMapEquiv
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hEnv : evm.executionEnv = I) :
    accountMapEquiv (flapperYankDeletedAccountMap σ I)
      (flapperYankDeleteState evm (flapperYankIdWord I)).accountMap := by
  let id := flapperYankIdWord I
  let owner := I.codeOwner
  let base := flapperYankBaseSlot id
  let packed := UInt256.ofNat 2 + base
  have hPackedEq : flapperYankPackedSlot id = packed := by
    simp [packed, base, flapperYankPackedSlot, u256_add_comm]
  let evmBase := flapperYankDeleteBidLotState evm id
  let w1 :=
    UInt256.land
      (Solm.EVM.storageLoad evmBase evm.executionEnv.codeOwner (flapperYankPackedSlot id))
      (UInt256.lnot solcAddrMask)
  let w2 :=
    flapperUint48Offset20ClearWord
      (Solm.EVM.storageLoad (flapperYankDeleteGuyState evm id)
        evm.executionEnv.codeOwner (flapperYankPackedSlot id))
  have hbyteSolmTriple :
      accountMapEquiv
        (sstoreAccountMap owner
          (sstoreAccountMap owner (sstoreAccountMap owner σ base (UInt256.ofNat 0))
            (base + UInt256.ofNat 1) (UInt256.ofNat 0))
          packed (UInt256.ofNat 0))
        (sstoreAccountMap owner
          (sstoreAccountMap owner
            (sstoreAccountMap owner evm.accountMap base (UInt256.ofNat 0))
            (base + UInt256.ofNat 1) (UInt256.ofNat 0))
          packed (UInt256.ofNat 0)) := by
    exact accountMapEquiv_sstoreAccountMap_three owner owner owner
      base (UInt256.ofNat 0) (base + UInt256.ofNat 1) (UInt256.ofNat 0)
      packed (UInt256.ofNat 0) hAccounts
  have hsourceSameSlot :
      accountMapEquiv
        (sstoreAccountMap owner
          (sstoreAccountMap owner
            (sstoreAccountMap owner evm.accountMap base (UInt256.ofNat 0))
            (base + UInt256.ofNat 1) (UInt256.ofNat 0))
          packed (UInt256.ofNat 0))
        (sstoreAccountMap owner
          (sstoreAccountMap owner
            (sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap base (UInt256.ofNat 0))
                (base + UInt256.ofNat 1) (UInt256.ofNat 0))
              packed w1)
            packed w2)
          packed (UInt256.ofNat 0)) := by
    let σbase :=
      sstoreAccountMap owner
        (sstoreAccountMap owner evm.accountMap base (UInt256.ofNat 0))
        (base + UInt256.ofNat 1) (UInt256.ofNat 0)
    have h1 :
        accountMapEquiv (sstoreAccountMap owner σbase packed (UInt256.ofNat 0))
          (sstoreAccountMap owner
            (sstoreAccountMap owner σbase packed w1) packed (UInt256.ofNat 0)) :=
      accountMapEquiv_sstoreAccountMap_self_update σbase owner packed w1 (UInt256.ofNat 0)
    have h2 :
        accountMapEquiv
          (sstoreAccountMap owner
            (sstoreAccountMap owner σbase packed w1) packed (UInt256.ofNat 0))
          (sstoreAccountMap owner
            (sstoreAccountMap owner
              (sstoreAccountMap owner σbase packed w1) packed w2)
            packed (UInt256.ofNat 0)) :=
      accountMapEquiv_sstoreAccountMap_self_update
        (sstoreAccountMap owner σbase packed w1) owner packed w2 (UInt256.ofNat 0)
    simpa [σbase] using accountMapEquiv.trans h1 h2
  have hsourceActual :
      accountMapEquiv
        (sstoreAccountMap owner
          (sstoreAccountMap owner
            (sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap base (UInt256.ofNat 0))
                (base + UInt256.ofNat 1) (UInt256.ofNat 0))
              packed w1)
            packed w2)
          packed (UInt256.ofNat 0))
        (flapperYankDeleteState evm id).accountMap := by
    rw [flapperYankDeleteState_accountMap_eq evm id]
    simp [hEnv, hPackedEq, id, owner, base, packed, evmBase, w1, w2]
    exact accountMapEquiv_refl _
  have hdelByte :
      flapperYankDeletedAccountMap σ I =
        sstoreAccountMap owner
          (sstoreAccountMap owner (sstoreAccountMap owner σ base (UInt256.ofNat 0))
            (base + UInt256.ofNat 1) (UInt256.ofNat 0))
          packed (UInt256.ofNat 0) := by
    simp [flapperYankDeletedAccountMap, storageWrite_eq, id, owner, base, packed]
  rw [hdelByte]
  exact accountMapEquiv.trans hbyteSolmTriple
    (accountMapEquiv.trans hsourceSameSlot hsourceActual)

theorem flapperYankHashMem_eq (id : UInt256) :
    flapperYankHashMem id = twoWordHashMem id (UInt256.ofNat 1) solcFreePtrMem := by
  simp [flapperYankHashMem,
    flapperRuntimeBlocks.flapperRuntime_block_964_taken_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperYankMappingHashSlot (id : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          (id.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      flapperYankBaseSlot id := by
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 1) mem) = flapperYankBaseSlot id
  simpa [flapperYankBaseSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat id (UInt256.ofNat 1) mem

theorem flapperYankHashSlot (id : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (flapperYankHashMem id) =
      flapperYankBaseSlot id := by
  rw [flapperYankHashMem_eq]
  simpa [flapperYankBaseSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat id (UInt256.ofNat 1) solcFreePtrMem

theorem flapperYankHashMem_size (id : UInt256) :
    (flapperYankHashMem id).size = 96 := by
  rw [flapperYankHashMem_eq]
  exact twoWordHashMem_size_96 id (UInt256.ofNat 1) solcFreePtrMem_size

theorem flapperYankHashMem_read64 (id : UInt256) :
    (flapperYankHashMem id).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  rw [flapperYankHashMem_eq]
  simpa using twoWordHashMem_read64 id (UInt256.ofNat 1)
    solcFreePtrMem_size solcFreePtrMem_read64

@[simp] theorem flapperYankHashMem_mload64 (id : UInt256) :
    memLoad (UInt256.ofNat 64) (flapperYankHashMem id) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperYankHashMem_size id]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperYankHashMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperYankCallBaseMem_size (id : UInt256) :
    (flapperYankCallBaseMem id).size = 96 := by
  unfold flapperYankCallBaseMem
  have h0 :
      (id.toByteArray.write 0 (flapperYankHashMem id) (UInt256.ofNat 0).toNat 32).size =
        96 := by
    exact toByteArray_write32_size_of_le (flapperYankHashMem id) id 0 96 96
      (flapperYankHashMem_size id) (by omega) (by omega)
  exact toByteArray_write32_size_of_le
    (id.toByteArray.write 0 (flapperYankHashMem id) (UInt256.ofNat 0).toNat 32)
    (UInt256.ofNat 1) 32 96 96 h0 (by omega) (by omega)

theorem flapperYankCallBaseMem_read64 (id : UInt256) :
    (flapperYankCallBaseMem id).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperYankCallBaseMem
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have h0 :
      (id.toByteArray.write 0 (flapperYankHashMem id) 0 32).size =
        96 := by
    exact toByteArray_write32_size_of_le (flapperYankHashMem id) id 0 96 96
      (flapperYankHashMem_size id) (by omega) (by omega)
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by
      have h := flapperYankHashMem_size id
      omega)
    (by omega)
    (by
      have h := flapperYankHashMem_size id
      omega)]
  exact flapperYankHashMem_read64 id

@[simp] theorem flapperYankCallBaseMem_mload64 (id : UInt256) :
    memLoad (UInt256.ofNat 64) (flapperYankCallBaseMem id) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperYankCallBaseMem_size id]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperYankCallBaseMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperYankCallBaseMem_expr_mload64 (id : UInt256) :
    memLoad (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          (id.toByteArray.write 0 (flapperYankHashMem id) (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      UInt256.ofNat 128 := by
  change memLoad (UInt256.ofNat 64) (flapperYankCallBaseMem id) = UInt256.ofNat 128
  exact flapperYankCallBaseMem_mload64 id

theorem flapperYankCallBaseHashSlot (id : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (flapperYankCallBaseMem id) =
      flapperYankBaseSlot id := by
  unfold flapperYankCallBaseMem
  exact flapperYankMappingHashSlot id (flapperYankHashMem id)

theorem flapperYankRuntimeCallMem_eq (σ : AccountMap) (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_1062_memory
        (ee := I) (mem := flapperYankHashMem (flapperYankIdWord I))
        (σ := σ) (x0 := flapperYankIdWord I) =
      flapperYankMoveCallMem σ I := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_1062_memory,
    flapperYankMoveCallMem, flapperYankCallMemGuy, flapperYankCallMemThis,
    flapperYankCallMemSelector, flapperYankMoveSelectorWord,
    flapperYankCallBaseMem, flapperYankMappingHashSlot, flapperYankBidWord,
    flapperYankGuyWord, flapperYankCallBaseMem_expr_mload64,
    flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem flapperYankMoveSelectorPrefix :
    flapperYankMoveSelectorWord.toByteArray.extract 0 4 = moveSelector := by
  native_decide

theorem flapperYankCallMemSelector_size_ge_160 (id : UInt256) :
    160 ≤ (flapperYankCallMemSelector id).size := by
  unfold flapperYankCallMemSelector
  exact toByteArray_write_size_ge_off_add32_unbounded flapperYankMoveSelectorWord
    (flapperYankCallBaseMem id) 128

theorem flapperYankCallMemThis_size_ge_164 (I : ExecutionEnv) (id : UInt256) :
    164 ≤ (flapperYankCallMemThis I id).size := by
  unfold flapperYankCallMemThis
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperYankCallMemSelector id) 132

theorem flapperYankCallMemGuy_size_ge_196 (σ : AccountMap) (I : ExecutionEnv) :
    196 ≤ (flapperYankCallMemGuy σ I).size := by
  unfold flapperYankCallMemGuy
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperYankGuyWord σ I)
    (flapperYankCallMemThis I (flapperYankIdWord I)) 164

theorem flapperYankMoveCallMem_size_ge_228 (σ : AccountMap) (I : ExecutionEnv) :
    228 ≤ (flapperYankMoveCallMem σ I).size := by
  unfold flapperYankMoveCallMem
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperYankBidWord σ I)
    (flapperYankCallMemGuy σ I) 196

theorem flapperYankMoveCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperYankMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperYankBidWord σ I) _ 196 64
    (by
      have h := flapperYankCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperYankCallMemGuy
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperYankGuyWord σ I) _ 164 64
    (by
      have h := flapperYankCallMemThis_size_ge_164 I (flapperYankIdWord I)
      omega)
    (by omega)]
  unfold flapperYankCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 132 64
    (by
      have h := flapperYankCallMemSelector_size_ge_160 (flapperYankIdWord I)
      omega)
    (by omega)]
  unfold flapperYankCallMemSelector
  rw [toByteArray_write_read_below_of_gap_unbounded flapperYankMoveSelectorWord _
    128 64
    (by rw [flapperYankCallBaseMem_size])
    (by omega)]
  exact flapperYankCallBaseMem_read64 (flapperYankIdWord I)

@[simp] theorem flapperYankMoveCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperYankMoveCallMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperYankMoveCallMem_size_ge_228 σ I
    omega)]
  rw [flapperYankMoveCallMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperYankMoveCallMem_expr_eq (σ : AccountMap) (I : ExecutionEnv) :
    (storageRead I.codeOwner σ
        (flapperYankBaseSlot (flapperYankIdWord I))).toByteArray.write 0
      ((UInt256.land solcAddrMask
          (storageRead I.codeOwner σ
            (flapperYankBaseSlot (flapperYankIdWord I) + UInt256.ofNat 2))).toByteArray.write 0
        ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
            ((UInt256.ofNat 1).toByteArray.write 0
              ((flapperYankIdWord I).toByteArray.write 0
                (flapperYankHashMem (flapperYankIdWord I))
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)
            128 32)
          132 32)
        164 32)
      196 32 =
      flapperYankMoveCallMem σ I := by
  simp [flapperYankMoveCallMem, flapperYankCallMemGuy, flapperYankCallMemThis,
    flapperYankCallMemSelector, flapperYankMoveSelectorWord, flapperYankCallBaseMem,
    flapperYankBidWord, flapperYankGuyWord, flapperYankPackedWord,
    flapperAddressMask_eq_solcAddrMask, u256_land_comm,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

@[simp] theorem flapperYankMoveCallMem_expr_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
      ((storageRead I.codeOwner σ
          (flapperYankBaseSlot (flapperYankIdWord I))).toByteArray.write 0
        ((UInt256.land solcAddrMask
            (storageRead I.codeOwner σ
              (flapperYankBaseSlot (flapperYankIdWord I) + UInt256.ofNat 2))).toByteArray.write 0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperYankIdWord I).toByteArray.write 0
                  (flapperYankHashMem (flapperYankIdWord I))
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)
              128 32)
            132 32)
          164 32)
        196 32) =
      UInt256.ofNat 128 := by
  rw [flapperYankMoveCallMem_expr_eq]
  exact flapperYankMoveCallMem_mload64 σ I

theorem flapperYankMoveCallMem_read196 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (flapperYankBidWord σ I) := by
  unfold flapperYankMoveCallMem
  exact toByteArray_write_read_back_of_gap_unbounded (flapperYankBidWord σ I) _ 196

theorem flapperYankMoveCallMem_read164 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (flapperYankGuyWord σ I) := by
  unfold flapperYankMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperYankBidWord σ I) _ 196 164
    (by
      have h := flapperYankCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperYankCallMemGuy
  exact toByteArray_write_read_back_of_gap_unbounded (flapperYankGuyWord σ I) _ 164

theorem flapperYankMoveCallMem_read132 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperYankMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperYankBidWord σ I) _ 196 132
    (by
      have h := flapperYankCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperYankCallMemGuy
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperYankGuyWord σ I) _ 164 132
    (by
      have h := flapperYankCallMemThis_size_ge_164 I (flapperYankIdWord I)
      omega)
    (by omega)]
  unfold flapperYankCallMemThis
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 132

theorem flapperYankMoveCallMem_read128_4 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 128 4 = moveSelector := by
  unfold flapperYankMoveCallMem
  rw [toByteArray_write_read_below_len_of_gap (flapperYankBidWord σ I) _ 196 128 4
    (by
      have h := flapperYankCallMemGuy_size_ge_196 σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperYankCallMemGuy_size_ge_196 σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperYankCallMemGuy
  rw [toByteArray_write_read_below_len_of_gap (flapperYankGuyWord σ I) _ 164 128 4
    (by
      have h := flapperYankCallMemThis_size_ge_164 I (flapperYankIdWord I)
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperYankCallMemThis_size_ge_164 I (flapperYankIdWord I)
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperYankCallMemThis
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 132 128 4
    (by
      have h := flapperYankCallMemSelector_size_ge_160 (flapperYankIdWord I)
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperYankCallMemSelector_size_ge_160 (flapperYankIdWord I)
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperYankCallMemSelector
  rw [toByteArray_write_read_window_of_gap_unbounded flapperYankMoveSelectorWord
    (flapperYankCallBaseMem (flapperYankIdWord I)) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperYankMoveSelectorPrefix

theorem flapperYankMoveCallMem_read128_100 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperYankMoveCallMem σ I).readWithPadding 128 100 =
      moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperYankGuyWord σ I) ++
        UInt256.toByteArray (flapperYankBidWord σ I) := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (flapperYankMoveCallMem σ I) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperYankMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperYankMoveCallMem σ I) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperYankMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperYankMoveCallMem σ I) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperYankMoveCallMem_size_ge_228 σ I
      omega)]
  rw [flapperYankMoveCallMem_read128_4, flapperYankMoveCallMem_read132,
    flapperYankMoveCallMem_read164, flapperYankMoveCallMem_read196]
  simp [ByteArray.append_assoc]

theorem flapperYankMoveEncode_eq (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
        [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperYankGuyWord σ I).toNat),
          .int (Int.ofNat (flapperYankBidWord σ I).toNat)] =
      some ((flapperYankMoveCallMem σ I).readWithPadding 128 100) := by
  rw [flapperYankMoveCallMem_read128_100]
  change externalABI.encode? "move"
        [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperYankGuyWord σ I).toNat),
          .int (Int.ofNat (flapperYankBidWord σ I).toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperYankGuyWord σ I) ++
        UInt256.toByteArray (flapperYankBidWord σ I))
  have hencOwner :
      encodeABIValue? addr (.address I.codeOwner) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) := by
    have hword : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by
      apply u256_inj
      unfold EVM.word EVM.uintN UInt256.ofNat UInt256.toNat
      simp only [Fin.ofNat]
      change I.codeOwner.val % EVM.twoPow 256 = I.codeOwner.val % UInt256.size
      simp [EVM.twoPow, UInt256.size]
    simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rw [hword]
  have hcanonGuy : (flapperYankGuyWord σ I).toNat < EVM.addressModulus := by
    simpa [flapperYankGuyWord, flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask] using
      solcAddrMask_result_canonical (flapperYankPackedWord σ I)
  have hencGuy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (flapperYankGuyWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperYankGuyWord σ I)) :=
    flapperEncodeValue_addr (flapperYankGuyWord σ I) hcanonGuy
  have hencBid :
      encodeABIValue? uint256 (.int (Int.ofNat (flapperYankBidWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperYankBidWord σ I)) :=
    flapperEncodeValue_uint256 (flapperYankBidWord σ I)
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.codeOwner,
            .address (AccountAddress.ofNat (flapperYankGuyWord σ I).toNat),
            .int (Int.ofNat (flapperYankBidWord σ I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (flapperYankGuyWord σ I) ++
          EVM.Word.toBytesBE (flapperYankBidWord σ I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencOwner, hencGuy,
      hencBid, hdynAddr, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem flapperYankRuntimeCallStack_eq (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_1062_stack
        (ee := I) (mem := flapperYankHashMem (flapperYankIdWord I))
        (σ := σ) (x0 := flapperYankIdWord I)
        (R := UInt256.ofNat 360 :: [sel]) =
      (UInt256.ofNat 0 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 128 :: flapperYankCallRest σ I sel) := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_1062_stack,
    flapperRuntimeBlocks.flapperRuntime_block_1062_memory,
    flapperYankRuntimeCallMem_eq, flapperYankCallRest, flapperYankCallBaseMem,
    flapperYankMappingHashSlot, flapperYankBidWord, flapperYankGuyWord,
    flapperYankMoveCallMem_expr_mload64,
    flapperYankPackedWord, flapperYankGemWord, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide]

theorem flapperX_yank_live_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) ≠ UInt256.ofNat 0)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 890) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd890⟩ := hdecode
  have hcondLive :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 7)) = UInt256.ofNat 0 :=
    isZero_eq_zero_of_ne hlive
  obtain ⟨_, _, rd899⟩ := flapperRuntimeBlocks.flapperRuntime_block_890_fallthrough
    (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLive rd890
  exact flapperRuntimeBlocks.flapperRuntime_block_899
    (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd899

theorem flapperX_yank_live_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 0)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 890) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 964) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd890⟩ := hdecode
  have hcondLive :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 7)) ≠ UInt256.ofNat 0 := by
    rw [hlive]
    decide
  obtain ⟨aw, k, C, rd964⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_890_taken_packed
      (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLive (by jump_dest) rd890
  exact ⟨aw, k, C, rd964⟩

theorem flapperX_yank_guy_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hguy : flapperYankGuyWord σ I = UInt256.ofNat 0)
    (h964 : ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 964) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd964⟩ := h964
  have hcondGuy :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperYankIdWord I).toByteArray.write 0 solcFreePtrMem
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)))) =
        UInt256.ofNat 0 := by
    rw [flapperYankMappingHashSlot (flapperYankIdWord I) solcFreePtrMem]
    rw [u256_add_comm]
    simpa [flapperYankGuyWord, flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask,
      u256_land_comm] using hguy
  obtain ⟨_, _, _, rd996⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_964_fallthrough_packed
      (x0 := flapperYankIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondGuy rd964
  exact flapperRuntimeBlocks.flapperRuntime_block_996
    (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd996

theorem flapperX_yank_guy_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hguy : flapperYankGuyWord σ I ≠ UInt256.ofNat 0)
    (h964 : ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 964) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 1062) (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperYankHashMem (flapperYankIdWord I)) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd964⟩ := h964
  have hcondGuy :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperYankIdWord I).toByteArray.write 0 solcFreePtrMem
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)))) ≠
        UInt256.ofNat 0 := by
    intro hzero
    apply hguy
    rw [flapperYankMappingHashSlot (flapperYankIdWord I) solcFreePtrMem] at hzero
    rw [u256_add_comm] at hzero
    simpa [flapperYankGuyWord, flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask,
      u256_land_comm] using hzero
  obtain ⟨aw', k, C, rd1062⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_964_taken_packed
      (x0 := flapperYankIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondGuy (by jump_dest) rd964
  exact ⟨aw', k, C, by simpa [flapperYankHashMem] using rd1062⟩

theorem flapperX_yank_call_setup {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (h1062 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1062)
      (flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperYankHashMem (flapperYankIdWord I)) aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1148)
      (UInt256.ofNat 0 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 128 :: flapperYankCallRest σ I sel)
      (flapperYankMoveCallMem σ I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1062⟩ := h1062
  obtain ⟨aw', k, C, rd1148raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1062_packed
      (x0 := flapperYankIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      rd1062
  have rd1148 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1148)
        (UInt256.ofNat 0 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
          UInt256.ofNat 128 :: flapperYankCallRest σ I sel)
        (flapperYankMoveCallMem σ I) aw' ByteArray.empty (cA, σ) k C := by
    simpa [flapperYankRuntimeCallStack_eq σ I sel,
        flapperYankRuntimeCallMem_eq σ I] using rd1148raw
  exact ⟨aw', k, C, rd1148⟩

theorem flapperX_yank_no_code_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcodeSize : extCodeSizeWord σ (flapperYankGemWord σ I) = UInt256.ofNat 0)
    (h1148 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1148)
      (UInt256.ofNat 0 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 128 :: flapperYankCallRest σ I sel)
      (flapperYankMoveCallMem σ I) aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw1148, _, _, rd1148⟩ := h1148
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (storageRead I.codeOwner σ (UInt256.ofNat 3))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) = UInt256.ofNat 0 := by
    simpa [flapperYankGemWord, solcAddrMask] using
      (by rw [hcodeSize]; decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord σ (flapperYankGemWord σ I))) = UInt256.ofNat 0)
  obtain ⟨_, _, _, rd1166⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1148_fallthrough_packed
      (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperYankGemWord σ I)
      (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt
      (by simpa [flapperYankCallRest] using rd1148)
  exact flapperRuntimeBlocks.flapperRuntime_block_1166
    (R := flapperRuntimeBlocks.flapperRuntime_block_1148_fallthrough_stack
      (σ := σ) (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperYankGemWord σ I)
      (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_1148_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd1166

theorem flapperX_yank_call_boundary {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcodeSize : extCodeSizeWord σ (flapperYankGemWord σ I) ≠ UInt256.ofNat 0)
    (h1148 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1148)
      (UInt256.ofNat 0 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 128 :: flapperYankCallRest σ I sel)
      (flapperYankMoveCallMem σ I) aw ByteArray.empty (cA, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1173)
      (gasArg :: flapperYankGemWord σ I :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperYankCallRest σ I sel)
      (flapperYankMoveCallMem σ I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1148⟩ := h1148
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (storageRead I.codeOwner σ (UInt256.ofNat 3))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    simpa [flapperYankGemWord, solcAddrMask] using
      (by
        rw [isZero_eq_zero_of_ne hcodeSize]
        decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord σ (flapperYankGemWord σ I))) ≠ UInt256.ofNat 0)
  obtain ⟨aw1170, k1170, C1170, rd1170raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1148_taken_packed
      (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperYankGemWord σ I)
      (R := flapperYankIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest)
      (by simpa [flapperYankCallRest] using rd1148)
  have rd1170 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1170)
        (UInt256.isZero (extCodeSizeWord σ (flapperYankGemWord σ I)) ::
          flapperYankGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperYankCallRest σ I sel)
        (flapperYankMoveCallMem σ I) aw1170 ByteArray.empty (cA, σ) k1170 C1170 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1148_taken_stack,
      flapperYankCallRest, flapperYankGemWord, solcAddrMask,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
        decide,
      show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide]
      using rd1170raw
  have rd1172 := flapperRuntimeBlocks.flapperRuntime_block_1170
    (x0 := UInt256.isZero (extCodeSizeWord σ (flapperYankGemWord σ I)))
    (R := flapperYankGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperYankCallRest σ I sel)
    (by simp only [flapperYankCallRest, List.length_cons, List.length_nil]; omega)
    rd1170
  have rd1172' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1172)
        (flapperYankGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperYankCallRest σ I sel)
        (flapperYankMoveCallMem σ I) aw1170 ByteArray.empty (cA, σ)
        (k1170 + 2) (C1170 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1170_stack] using rd1172
  obtain ⟨gasArg, rd1173raw⟩ := RD.rawGas rd1172' (by native_decide)
    (by simp only [flapperYankCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw1170, k1170 + 2 + 1, C1170 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_1170_stack,
    show UInt256.ofNat 1172 + ⟨1⟩ = UInt256.ofNat 1173 by native_decide]
    using rd1173raw

theorem flapperX_yank_call_failure {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1174)
      (UInt256.ofNat 0 :: flapperYankCallRest σ I sel) mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1181 := flapperRuntimeBlocks.flapperRuntime_block_1174_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperYankCallRest σ I sel)
    (by simp only [flapperYankCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_1181
    (R := flapperRuntimeBlocks.flapperRuntime_block_1174_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperYankCallRest σ I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_1174_fallthrough_stack,
        flapperYankCallRest, List.length_cons, List.length_nil]
      omega)
    rd1181

theorem flapperX_yank_call_success {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1174)
      (UInt256.ofNat 1 :: flapperYankCallRest σ I sel) mem aw rdata world k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (world.1, flapperYankDeletedAccountMap world.2 I) ByteArray.empty := by
  have rd1190 := flapperRuntimeBlocks.flapperRuntime_block_1174_taken
    (x0 := UInt256.ofNat 1) (R := flapperYankCallRest σ I sel)
    (by simp only [flapperYankCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) h
  have rd1190' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1190)
        (UInt256.ofNat 0 :: flapperYankCallRest σ I sel) mem aw rdata world
        (k + 5) (C + 22) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1174_taken_stack,
      flapperYankCallRest] using rd1190
  cases world with
  | mk cAcur σcur =>
    obtain ⟨aw360, k360, C360, rd360raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_1190_packed
        (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
        (x2 := UInt256.ofNat 3140843579) (x3 := flapperYankGemWord σ I)
        (x4 := flapperYankIdWord I) (x5 := UInt256.ofNat 360) (R := [sel])
        (by simp only [List.length_cons, List.length_nil]; omega)
        hperm (by jump_dest) rd1190'
    have rd360 :
        RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 360)
          [sel] (flapperRuntimeBlocks.flapperRuntime_block_1190_memory
            (mem := mem) (x4 := flapperYankIdWord I))
          aw360 rdata (cAcur, flapperYankDeletedAccountMap σcur I) k360 C360 := by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_1190_stack,
        flapperYankDeletedAccountMap, flapperYankMappingHashSlot, u256_add_comm]
        using rd360raw
    exact flapperRuntimeBlocks.flapperRuntime_block_360
      (R := [sel]) (by simp only [List.length_cons, List.length_nil]; omega) rd360

theorem flapperYankBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 19))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨331⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hselLit :
      ((⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) == I.calldata.extract 0 4) =
        true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 19) (by decide) hsel
  have hd : dispatchMsg contract I.calldata = some yankTransition :=
    flapperDispatch_yank hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_yank_ok (I := I) hsz36
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let id := flapperYankIdWord I
    have hdecode := flapperX_yank_decode_ok
      (g := Sat256.ofUInt256 g) hsize hsz36 hreach
    have hloadLiveEq :
        flapperYankLiveWordOfState evmSolm =
          storageRead I.codeOwner σ_evm (UInt256.ofNat 7) := by
      simpa [flapperYankLiveWordOfState, evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 7)
    by_cases hliveEvm : storageRead I.codeOwner σ_evm (UInt256.ofNat 7) = UInt256.ofNat 0
    · have h964 := flapperX_yank_live_ok
        (g := Sat256.ofUInt256 g) hliveEvm hdecode
      have hliveSolm :
          flapperYankLiveWordOfState evmSolm = UInt256.ofNat 0 := by
        rw [hloadLiveEq, hliveEvm]
      have hStateInit :
          CallStateRel (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            I (cA, σ_evm) evmSolm :=
        CallStateRel.initState hAccounts
      have hPackedLoadEq :
          flapperYankPackedWordOfState evmSolm id =
            storageRead I.codeOwner σ_evm (flapperYankPackedSlot id) := by
        simpa [flapperYankPackedWordOfState, flapperYankPackedSlot, evmSolm,
          initState, id] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperYankPackedSlot id)
      have hGuyWordSolm :
          flapperYankGuyWordOfState evmSolm id = flapperYankGuyWord σ_evm I := by
        simp [flapperYankGuyWordOfState, flapperYankGuyWord, flapperYankPackedWord,
          flapperYankPackedSlot, hPackedLoadEq, id]
      by_cases hguyEvm : flapperYankGuyWord σ_evm I = UInt256.ofNat 0
      · have hguySolm :
            flapperYankGuyWordOfState evmSolm id = UInt256.ofNat 0 := by
          rw [hGuyWordSolm, hguyEvm]
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperYankLocals id)
              yankTransition.body .reverted := by
          simpa [evmSolm, id] using
            flapperYankBodyRevertsGuy evmSolm id
              (by simp only [evmSolm, initState]; exact hwv) hliveSolm hguySolm
        exact (flapperX_yank_guy_revert (g := Sat256.ofUInt256 g) hguyEvm h964)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hguySolmNe :
            flapperYankGuyWordOfState evmSolm id ≠ UInt256.ofNat 0 := by
          intro hzero
          exact hguyEvm (by rw [← hGuyWordSolm]; exact hzero)
        have h1062 := flapperX_yank_guy_ok
          (g := Sat256.ofUInt256 g) hguyEvm h964
        have h1148 := flapperX_yank_call_setup
          (g := Sat256.ofUInt256 g) h1062
        have hGemLoadEq :
            Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (UInt256.ofNat 3) =
              storageRead I.codeOwner σ_evm (UInt256.ofNat 3) := by
          simpa [evmSolm, initState] using
            flapperInitStorageLoad_eq
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hAccounts (UInt256.ofNat 3)
        have hGemWordSolm :
            flapperYankGemWordOfState evmSolm = flapperYankGemWord σ_evm I := by
          simp [flapperYankGemWordOfState, flapperYankGemWord, hGemLoadEq]
        have hBidLoadEq :
            flapperYankBidWordOfState evmSolm id = flapperYankBidWord σ_evm I := by
          simpa [flapperYankBidWordOfState, flapperYankBidWord, evmSolm, initState,
            id] using
            flapperInitStorageLoad_eq
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hAccounts (flapperYankBaseSlot id)
        by_cases hcodeSize :
            extCodeSizeWord σ_evm (flapperYankGemWord σ_evm I) = UInt256.ofNat 0
        · have hcodeSizeSolm :
              extCodeSizeWord evmSolm.accountMap (flapperYankGemWordOfState evmSolm) =
                UInt256.ofNat 0 := by
            have hmapCode := extCodeSizeWord_accountMapEquiv hStateInit.accounts
              (flapperYankGemWord σ_evm I)
            exact (by
              simpa [hGemWordSolm] using hmapCode.symm.trans hcodeSize)
          have hbody :
              ExecTransitionBody config contract evmSolm (flapperYankLocals id)
                yankTransition.body .reverted := by
            simpa [evmSolm, id] using
              flapperYankBodyRevertsNoCode evmSolm id
                (by simp only [evmSolm, initState]; exact hwv)
                hliveSolm hguySolmNe hcodeSizeSolm
          exact (flapperX_yank_no_code_revert
              (g := Sat256.ofUInt256 g) hcodeSize h1148)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hcodeSizeSolmNe :
              extCodeSizeWord evmSolm.accountMap (flapperYankGemWordOfState evmSolm) ≠
                UInt256.ofNat 0 := by
            intro hzero
            apply hcodeSize
            have hmapCode := extCodeSizeWord_accountMapEquiv hStateInit.accounts
              (flapperYankGemWord σ_evm I)
            have hzeroGem :
                extCodeSizeWord evmSolm.accountMap (flapperYankGemWord σ_evm I) =
                  UInt256.ofNat 0 := by
              simpa [hGemWordSolm] using hzero
            exact hmapCode.trans hzeroGem
          let frameLive : Frame := { contract := contract, locals := flapperYankLocals id }
          have hguardTrue :
              evalExpr? config frameLive evmSolm
                (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
                  .ok (.bool true) := by
            simpa [frameLive] using
              flapperYankExtGuard_true evmSolm id hcodeSizeSolmNe
          have hpref :
              ExecBlock config frameLive evmSolm
                (nonpayable ++
                  [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                    .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) ])
                (.ok frameLive evmSolm) := by
            simpa [frameLive, evmSolm, id] using
              flapperYankPrefixOk evmSolm id
                (by simp only [evmSolm, initState]; exact hwv) hliveSolm hguySolmNe
          have htailExternal :
              BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config frameLive evmSolm
                [ .externalCall (.storage gemRef) "move" (.intLit 0)
                    [thisAddr, .storage (bidsF (.var "id") "guy"),
                      .storage (bidsF (.var "id") "bid")] "_moveRet",
                  .delete (bidRef (.var "id")) ]
                (runtimeExit (.abi yankTransition.returnType)) := by
            obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
              flapperX_yank_call_boundary (g := Sat256.ofUInt256 g)
                hcodeSize h1148
            refine BlockProgress.externalCall
              (h := rdCall) (hState := hStateInit)
              (receiver := .storage gemRef) (eth := .intLit 0)
              (args := [thisAddr, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")])
              (argVals := [.address I.codeOwner,
                .address (AccountAddress.ofNat (flapperYankGuyWord σ_evm I).toNat),
                .int (Int.ofNat (flapperYankBidWord σ_evm I).toNat)])
              (tgt := AccountAddress.ofNat (flapperYankGemWord σ_evm I).toNat)
              (name := "move") (retVar := "_moveRet") (value := 0)
              (stmts := [.delete (bidRef (.var "id"))])
              ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
              (by simp only [flapperYankCallRest, List.length_cons, List.length_nil]; omega)
              (by exact True.intro) ?_ ?_
            · have hrecv := flapperYankGem_eval evmSolm id
              simpa [frameLive, hGemWordSolm] using hrecv
            · simp [evalExpr?, pure]
            · have hargs := flapperYankArgs_eval evmSolm id
              rw [hGuyWordSolm, hBidLoadEq] at hargs
              simpa [frameLive, evmSolm, initState] using hargs
            · exact wordOfInt_zero.symm
            · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
              apply Fin.ext
              simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
                AccountAddress.size]
            · simpa [
                show (UInt256.ofNat 128).toNat = 128 by decide,
                show (UInt256.ofNat 100).toNat = 100 by decide] using
                flapperYankMoveEncode_eq σ_evm I
            · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
              have hdecodeOut : config.externalABI.decode? "move" out = some [] := by
                simp [config, externalABI, decodeVoid?]
              rw [hdecodeOut]
              have hdelete :
                  deleteStorage? config
                    { contract := contract,
                      locals := (flapperYankLocals id).insert "_moveRet" (collapseReturns []) }
                    evm' (bidRef (.var "id")) =
                    .ok (flapperYankDeleteState evm' id) :=
                flapperYankDeleteStorage_afterMoveRet evm' id
              have hret : RDret flapperBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (world'.1, flapperYankDeletedAccountMap world'.2 I) ByteArray.empty := by
                exact flapperX_yank_call_success
                  (σ := σ_evm) (sel := flapperSelWord I) hperm (h := by
                    simpa [callCursor,
                      show UInt256.ofNat 1173 + ⟨1⟩ = UInt256.ofNat 1174 by native_decide]
                      using rdSucc)
              exact BlockProgress.ofRDret
                (hsource := by
                  simpa [frameLive] using
                    (ExecBlock.consNormal (ExecStmt.delete hdelete) ExecBlock.nil :
                      ExecBlock config
                        { contract := contract,
                          locals := (flapperYankLocals id).insert "_moveRet"
                            (collapseReturns []) } evm'
                        [ .delete (bidRef (.var "id")) ]
                        (.ok
                          { contract := contract,
                            locals := (flapperYankLocals id).insert "_moveRet"
                              (collapseReturns []) }
                          (flapperYankDeleteState evm' id))))
                hret
                (by
                  rw [flapperYankDeleteState_createdAccounts]
                  exact hState'.created.symm)
                (flapperYankDeleteState_accountMapEquiv
                  (σ := world'.2) (evm := evm') (I := I)
                  hState'.accounts hState'.env)
                (by simpa [yankTransition] using abiVoidFallthrough)
            · intro out world' k' C' cur rdFail
              exact flapperX_yank_call_failure
                (σ := σ_evm) (sel := flapperSelWord I) (h := by
                  simpa [callCursor,
                    show UInt256.ofNat 1173 + ⟨1⟩ = UInt256.ofNat 1174 by native_decide]
                    using rdFail)
          have htail :
              BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config frameLive evmSolm
                (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                  [thisAddr, .storage (bidsF (.var "id") "guy"),
                    .storage (bidsF (.var "id") "bid")] "_moveRet" ++
                  [ .delete (bidRef (.var "id")) ])
                (runtimeExit (.abi yankTransition.returnType)) := by
            simpa [checkedExternalCallStmts] using
              BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
          have hprogress :
              BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config frameLive evmSolm yankTransition.body
                (runtimeExit (.abi yankTransition.returnType)) := by
            have hp := BlockProgress.prepend hpref htail
            simpa [yankTransition, nonpayable, checkedExternalCallStmts, frameLive] using hp
          exact hprogress.toRuntimeEquivalenceFor hcode
            (fun result hfunc => by
              exact solmExec.intro (flapperSelectorDispatch_yank hselLit) rfl hdec
                (by simp [evmSolm, initState, Sat256.ofUInt256, Sat256.toUInt256])
                hfunc)
            (by intro result endpoint h; exact h)
    · have hliveSolmNe :
          flapperYankLiveWordOfState evmSolm ≠ UInt256.ofNat 0 := by
        intro hzero
        exact hliveEvm (by rw [← hloadLiveEq]; exact hzero)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperYankLocals id)
            yankTransition.body .reverted := by
        simpa [evmSolm, id] using
          flapperYankBodyRevertsLive evmSolm id
            (by simp only [evmSolm, initState]; exact hwv) hliveSolmNe
      exact (flapperX_yank_live_revert
          (g := Sat256.ofUInt256 g) hliveEvm hdecode)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_yank_none_short (I := I) hsz4 hshort
    have hrev := flapperX_yank_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
