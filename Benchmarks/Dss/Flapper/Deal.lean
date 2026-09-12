import Benchmarks.Dss.Flapper.Kick
import Benchmarks.Dss.Flapper.Yank
import Benchmarks.Dss.Flapper.Cage
import Reasoning.CallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

abbrev flapperDealIdWord (I : ExecutionEnv) : UInt256 :=
  flapperYankIdWord I

abbrev flapperDealLocals (id : UInt256) : Store :=
  flapperYankLocals id

def flapperDealLocalsLot (id lot : UInt256) : Store :=
  (flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat))

def flapperDealLocalsAfterMove (id lot : UInt256) : Store :=
  (flapperDealLocalsLot id lot).insert "_moveRet" (collapseReturns [])

def flapperDealLocalsAfterBurn (id lot : UInt256) : Store :=
  (flapperDealLocalsAfterMove id lot).insert "_burnRet" (collapseReturns [])

def flapperDealLocalsAfterSub (id lot fillNew : UInt256) : Store :=
  (flapperDealLocalsAfterBurn id lot).insert "fillNew"
    (.int (Int.ofNat fillNew.toNat))

def flapperDealAfterSubFrame (id lot fillNew : UInt256) : Frame :=
  { contract := contract, locals := flapperDealLocalsAfterSub id lot fillNew }

def flapperDealSubLocals (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat))

def flapperDealSubLocalsZ (x y z : UInt256) : Store :=
  (flapperDealSubLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev flapperDealBaseSlot (id : UInt256) : UInt256 :=
  flapperYankBaseSlot id

abbrev flapperDealPackedSlot (id : UInt256) : UInt256 :=
  flapperYankPackedSlot id

abbrev flapperDealBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperYankBidWord σ I

def flapperDealLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperDealBaseSlot (flapperDealIdWord I) + UInt256.ofNat 1)

abbrev flapperDealPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperYankPackedWord σ I

abbrev flapperDealGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperYankGuyWord σ I

abbrev flapperDealGemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperYankGemWord σ I

def flapperDealVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 2)) solcAddrMask

def flapperDealTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperDealPackedWord σ I) flapperUint48Shift160)

def flapperDealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperDealPackedWord σ I) flapperUint48Shift208)

def flapperDealTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev flapperDealLiveWordOfState (evm : EVM.State) : UInt256 :=
  flapperKickLiveWordOfState evm

def flapperDealLotWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (flapperDealBaseSlot id + UInt256.ofNat 1)

abbrev flapperDealBidWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperYankBidWordOfState evm id

abbrev flapperDealPackedWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperYankPackedWordOfState evm id

abbrev flapperDealGuyWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperYankGuyWordOfState evm id

abbrev flapperDealGemWordOfState (evm : EVM.State) : UInt256 :=
  flapperYankGemWordOfState evm

abbrev flapperDealVatWordOfState (evm : EVM.State) : UInt256 :=
  flapperKickVatWordOfState evm

abbrev flapperDealFillWordOfState (evm : EVM.State) : UInt256 :=
  flapperKickFillWordOfState evm

def flapperDealTicWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.div (flapperDealPackedWordOfState evm id) flapperUint48Shift160)
    flapperUint48Mask

def flapperDealEndWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.div (flapperDealPackedWordOfState evm id) flapperUint48Shift208)
    flapperUint48Mask

def flapperDealTimestampWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev flapperDealDeletedAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  flapperYankDeletedAccountMap σ I

def flapperDealDeletedState (evm : EVM.State) (id : UInt256) : EVM.State :=
  flapperYankDeleteState evm id

def flapperDealFillNewWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (storageRead I.codeOwner (flapperDealDeletedAccountMap σ I) (UInt256.ofNat 9))
    (flapperDealLotWord σ I)

def flapperDealFillNewWordFrom (σ : AccountMap) (I : ExecutionEnv)
    (lot : UInt256) : UInt256 :=
  UInt256.sub (storageRead I.codeOwner (flapperDealDeletedAccountMap σ I) (UInt256.ofNat 9))
    lot

def flapperDealFillNewWordOfState (evm : EVM.State) (id lot : UInt256) : UInt256 :=
  UInt256.sub (flapperDealFillWordOfState (flapperDealDeletedState evm id)) lot

def flapperDealAfterFillState (evm : EVM.State) (id lot : UInt256) : EVM.State :=
  Solm.EVM.storageStore (flapperDealDeletedState evm id)
    evm.executionEnv.codeOwner (UInt256.ofNat 9)
    (flapperDealFillNewWordOfState evm id lot)

def flapperDealAfterFillWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (flapperDealDeletedAccountMap σ I) (UInt256.ofNat 9)
    (flapperDealFillNewWord σ I)

def flapperDealAfterFillWorldFrom (σ : AccountMap) (I : ExecutionEnv)
    (lot : UInt256) : AccountMap :=
  storageWrite I.codeOwner (flapperDealDeletedAccountMap σ I) (UInt256.ofNat 9)
    (flapperDealFillNewWordFrom σ I lot)

abbrev flapperDealMoveSelectorWord : UInt256 :=
  flapperYankMoveSelectorWord

abbrev flapperDealBurnSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 661694443) (UInt256.ofNat 226)

abbrev flapperDealHashMem (id : UInt256) : ByteArray :=
  flapperYankHashMem id

def flapperDealScratchMem (id : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0
    (id.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
    (UInt256.ofNat 32).toNat 32

abbrev flapperDealCallBaseMem (id : UInt256) : ByteArray :=
  flapperYankCallBaseMem id

def flapperDealMoveCallMemSelector (id : UInt256) : ByteArray :=
  flapperDealMoveSelectorWord.toByteArray.write 0 (flapperDealCallBaseMem id) 128 32

def flapperDealMoveCallMemThis (I : ExecutionEnv) (id : UInt256) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (flapperDealMoveCallMemSelector id) 132 32

def flapperDealMoveCallMemGuy (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperDealGuyWord σ I).toByteArray.write 0
    (flapperDealMoveCallMemThis I (flapperDealIdWord I)) 164 32

def flapperDealMoveCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperDealLotWord σ I).toByteArray.write 0
    (flapperDealMoveCallMemGuy σ I) 196 32

def flapperDealMoveCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [UInt256.ofNat 228, UInt256.ofNat 3140843579, flapperDealVatWord σ I,
    flapperDealLotWord σ I, flapperDealIdWord I, UInt256.ofNat 360, sel]

def flapperDealBurnCallBaseMem (pre σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0
    ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I)
      (UInt256.ofNat 0).toNat 32)
    (UInt256.ofNat 32).toNat 32

def flapperDealBurnCallMemSelector (pre σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  flapperDealBurnSelectorWord.toByteArray.write 0
    (flapperDealBurnCallBaseMem pre σ I) 128 32

def flapperDealBurnCallMemThis (pre σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (flapperDealBurnCallMemSelector pre σ I) 132 32

def flapperDealBurnCallMem (pre σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperDealBidWord σ I).toByteArray.write 0
    (flapperDealBurnCallMemThis pre σ I) 164 32

def flapperDealBurnCallRest (pre σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [UInt256.ofNat 196, UInt256.ofNat 2646777772, flapperDealGemWord σ I,
    flapperDealLotWord pre I, flapperDealIdWord I, UInt256.ofNat 360, sel]

theorem flapperDealCallBaseMem_size (id : UInt256) :
    (flapperDealCallBaseMem id).size = 96 := by
  simpa [flapperDealCallBaseMem] using flapperYankCallBaseMem_size id

theorem flapperDealHashMem_size_ge_96 (id : UInt256) :
    96 ≤ (flapperDealHashMem id).size := by
  simpa [flapperDealHashMem] using
    (le_of_eq (flapperYankHashMem_size id).symm)

theorem flapperDealHashMem_read64 (id : UInt256) :
    (flapperDealHashMem id).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  simpa [flapperDealHashMem] using flapperYankHashMem_read64 id

theorem flapperDealScratchMem_size_ge_96 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size) :
    96 ≤ (flapperDealScratchMem id mem).size := by
  unfold flapperDealScratchMem
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have h0size :
      (id.toByteArray.write 0 mem 0 32).size = mem.size := by
    exact toByteArray_write32_size_of_le mem id 0 mem.size mem.size rfl
      (by omega) (by omega)
  have h1size :
      ((UInt256.ofNat 1).toByteArray.write 0
        (id.toByteArray.write 0 mem 0 32) 32 32).size =
        mem.size := by
    exact toByteArray_write32_size_of_le
      (id.toByteArray.write 0 mem 0 32) (UInt256.ofNat 1) 32 mem.size
      mem.size h0size (by omega) (by omega)
  rw [h1size]
  exact hmem

theorem flapperDealScratchMem_read64 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperDealScratchMem id mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealScratchMem
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have h0size :
      (id.toByteArray.write 0 mem 0 32).size = mem.size := by
    exact toByteArray_write32_size_of_le mem id 0 mem.size mem.size rfl
      (by omega) (by omega)
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [h0size]; omega) (by omega) (by rw [h0size]; omega)]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]
  exact hread

theorem flapperDealScratchMem_mload64 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    memLoad (UInt256.ofNat 64) (flapperDealScratchMem id mem) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealScratchMem_size_ge_96 id mem hmem
    omega)]
  rw [flapperDealScratchMem_read64 id mem hmem hread]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperDealCallBaseMem_mload64 (id : UInt256) :
    memLoad (UInt256.ofNat 64) (flapperDealCallBaseMem id) =
      UInt256.ofNat 128 := by
  simpa [flapperDealCallBaseMem] using flapperYankCallBaseMem_mload64 id

@[simp] theorem flapperDealCallBaseMem_expr_mload64 (id : UInt256) :
    memLoad (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          (id.toByteArray.write 0 (flapperDealHashMem id) (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      UInt256.ofNat 128 := by
  simpa [flapperDealHashMem] using flapperYankCallBaseMem_expr_mload64 id

theorem flapperDealRuntimeMoveCallMem_eq (σ : AccountMap) (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_3601_memory
        (ee := I) (mem := flapperDealHashMem (flapperDealIdWord I))
        (σ := σ) (x0 := flapperDealIdWord I) =
      flapperDealMoveCallMem σ I := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3601_memory,
    flapperDealMoveCallMem, flapperDealMoveCallMemGuy, flapperDealMoveCallMemThis,
    flapperDealMoveCallMemSelector, flapperDealMoveSelectorWord, flapperDealCallBaseMem,
    flapperYankMoveSelectorWord, flapperYankCallBaseMem, flapperDealHashMem,
    flapperYankMappingHashSlot, flapperDealLotWord, flapperDealGuyWord,
    flapperYankGuyWord, flapperDealPackedWord, flapperYankPackedWord,
    flapperAddressMask_eq_solcAddrMask,
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

theorem flapperDealMoveSelectorPrefix :
    flapperDealMoveSelectorWord.toByteArray.extract 0 4 = moveSelector := by
  simpa [flapperDealMoveSelectorWord] using flapperYankMoveSelectorPrefix

theorem flapperDealMoveCallMemSelector_size_ge_160 (id : UInt256) :
    160 ≤ (flapperDealMoveCallMemSelector id).size := by
  unfold flapperDealMoveCallMemSelector
  exact toByteArray_write_size_ge_off_add32_unbounded flapperDealMoveSelectorWord
    (flapperDealCallBaseMem id) 128

theorem flapperDealMoveCallMemThis_size_ge_164 (I : ExecutionEnv) (id : UInt256) :
    164 ≤ (flapperDealMoveCallMemThis I id).size := by
  unfold flapperDealMoveCallMemThis
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperDealMoveCallMemSelector id) 132

theorem flapperDealMoveCallMemGuy_size_ge_196 (σ : AccountMap) (I : ExecutionEnv) :
    196 ≤ (flapperDealMoveCallMemGuy σ I).size := by
  unfold flapperDealMoveCallMemGuy
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealGuyWord σ I)
    (flapperDealMoveCallMemThis I (flapperDealIdWord I)) 164

theorem flapperDealMoveCallMem_size_ge_228 (σ : AccountMap) (I : ExecutionEnv) :
    228 ≤ (flapperDealMoveCallMem σ I).size := by
  unfold flapperDealMoveCallMem
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealLotWord σ I)
    (flapperDealMoveCallMemGuy σ I) 196

theorem flapperDealMoveCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 64
    (by
      have h := flapperDealMoveCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemGuy
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealGuyWord σ I) _ 164 64
    (by
      have h := flapperDealMoveCallMemThis_size_ge_164 I (flapperDealIdWord I)
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _
    132 64
    (by
      have h := flapperDealMoveCallMemSelector_size_ge_160 (flapperDealIdWord I)
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemSelector
  rw [toByteArray_write_read_below_of_gap_unbounded flapperDealMoveSelectorWord _
    128 64
    (by rw [flapperDealCallBaseMem_size])
    (by omega)]
  simpa [flapperDealCallBaseMem] using
    flapperYankCallBaseMem_read64 (flapperDealIdWord I)

@[simp] theorem flapperDealMoveCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperDealMoveCallMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealMoveCallMem_size_ge_228 σ I
    omega)]
  rw [flapperDealMoveCallMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperDealRuntimeMoveCallMem_mload64 (σ : AccountMap)
    (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3601_memory
          (ee := I) (mem := flapperDealHashMem (flapperDealIdWord I))
          (σ := σ) (x0 := flapperDealIdWord I)) =
      UInt256.ofNat 128 := by
  rw [flapperDealRuntimeMoveCallMem_eq σ I]
  exact flapperDealMoveCallMem_mload64 σ I

@[simp] theorem flapperDealRuntimeMoveCallMem_raw_mload64 (σ : AccountMap)
    (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
      ((storageRead I.codeOwner σ
            (flapperYankBaseSlot (flapperDealIdWord I) + UInt256.ofNat 1)).toByteArray.write 0
        ((UInt256.land solcAddrMask
              (storageRead I.codeOwner σ
                (flapperYankBaseSlot (flapperDealIdWord I) + UInt256.ofNat 2))).toByteArray.write
          0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            (((UInt256.ofNat 3140843579).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperDealIdWord I).toByteArray.write 0
                  (flapperYankHashMem (flapperDealIdWord I))
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)
              128 32)
            132 32)
          164 32)
        196 32) =
      UInt256.ofNat 128 := by
  simpa [flapperDealMoveCallMem, flapperDealMoveCallMemGuy,
    flapperDealMoveCallMemThis, flapperDealMoveCallMemSelector,
    flapperDealMoveSelectorWord, flapperYankMoveSelectorWord, flapperDealCallBaseMem,
    flapperYankCallBaseMem, flapperDealHashMem, flapperYankMappingHashSlot,
    flapperDealLotWord, flapperDealGuyWord, flapperYankGuyWord, flapperDealPackedWord,
    flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask, u256_land_comm,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]
    using flapperDealMoveCallMem_mload64 σ I

@[simp] theorem flapperDealMoveCallMem_expr_eq (σ : AccountMap) (I : ExecutionEnv) :
    ((flapperDealLotWord σ I).toByteArray.write 0
      ((flapperDealGuyWord σ I).toByteArray.write 0
        ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
            (flapperDealCallBaseMem (flapperDealIdWord I))
            (UInt256.ofNat 128).toNat 32)
          ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat 32)
        ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat 32)
      ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat 32) =
      flapperDealMoveCallMem σ I := by
  simp [flapperDealMoveCallMem, flapperDealMoveCallMemGuy,
    flapperDealMoveCallMemThis, flapperDealMoveCallMemSelector,
    flapperDealMoveSelectorWord,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

@[simp] theorem flapperDealMoveCallMem_expr_mload64 (σ : AccountMap)
    (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
      ((flapperDealLotWord σ I).toByteArray.write 0
        ((flapperDealGuyWord σ I).toByteArray.write 0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
              (flapperDealCallBaseMem (flapperDealIdWord I))
              (UInt256.ofNat 128).toNat 32)
            ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat 32)
          ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat 32)
        ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat 32) =
      UInt256.ofNat 128 := by
  rw [flapperDealMoveCallMem_expr_eq]
  exact flapperDealMoveCallMem_mload64 σ I

theorem flapperDealMoveCallMem_read196 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (flapperDealLotWord σ I) := by
  unfold flapperDealMoveCallMem
  exact toByteArray_write_read_back_of_gap_unbounded (flapperDealLotWord σ I) _ 196

theorem flapperDealMoveCallMem_read164 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (flapperDealGuyWord σ I) := by
  unfold flapperDealMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 164
    (by
      have h := flapperDealMoveCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemGuy
  exact toByteArray_write_read_back_of_gap_unbounded
    (flapperDealGuyWord σ I) (flapperDealMoveCallMemThis I (flapperDealIdWord I)) 164

theorem flapperDealMoveCallMem_read132 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperDealMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 132
    (by
      have h := flapperDealMoveCallMemGuy_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemGuy
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealGuyWord σ I) _ 164 132
    (by
      have h := flapperDealMoveCallMemThis_size_ge_164 I (flapperDealIdWord I)
      omega)
    (by omega)]
  unfold flapperDealMoveCallMemThis
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.codeOwner.val) (flapperDealMoveCallMemSelector (flapperDealIdWord I)) 132

theorem flapperDealMoveCallMem_read128_4 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 128 4 = moveSelector := by
  unfold flapperDealMoveCallMem
  rw [toByteArray_write_read_below_len_of_gap (flapperDealLotWord σ I) _ 196 128 4
    (by
      have h := flapperDealMoveCallMemGuy_size_ge_196 σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemGuy_size_ge_196 σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperDealMoveCallMemGuy
  rw [toByteArray_write_read_below_len_of_gap (flapperDealGuyWord σ I) _ 164 128 4
    (by
      have h := flapperDealMoveCallMemThis_size_ge_164 I (flapperDealIdWord I)
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemThis_size_ge_164 I (flapperDealIdWord I)
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperDealMoveCallMemThis
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 132 128 4
    (by
      have h := flapperDealMoveCallMemSelector_size_ge_160 (flapperDealIdWord I)
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemSelector_size_ge_160 (flapperDealIdWord I)
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperDealMoveCallMemSelector
  rw [toByteArray_write_read_window_of_gap_unbounded flapperDealMoveSelectorWord
    (flapperDealCallBaseMem (flapperDealIdWord I)) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperDealMoveSelectorPrefix

theorem flapperDealMoveCallMem_read128_100 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealMoveCallMem σ I).readWithPadding 128 100 =
      moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealGuyWord σ I) ++
        UInt256.toByteArray (flapperDealLotWord σ I) := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMem σ I) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMem σ I) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMem σ I) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMem_size_ge_228 σ I
      omega)]
  rw [flapperDealMoveCallMem_read128_4, flapperDealMoveCallMem_read132,
    flapperDealMoveCallMem_read164, flapperDealMoveCallMem_read196]
  simp [ByteArray.append_assoc]

theorem flapperDealMoveEncode_eq (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
        [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperDealGuyWord σ I).toNat),
          .int (Int.ofNat (flapperDealLotWord σ I).toNat)] =
      some ((flapperDealMoveCallMem σ I).readWithPadding 128 100) := by
  rw [flapperDealMoveCallMem_read128_100]
  change externalABI.encode? "move"
        [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperDealGuyWord σ I).toNat),
          .int (Int.ofNat (flapperDealLotWord σ I).toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealGuyWord σ I) ++
        UInt256.toByteArray (flapperDealLotWord σ I))
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
  have hcanonGuy : (flapperDealGuyWord σ I).toNat < EVM.addressModulus := by
    simpa [flapperDealGuyWord, flapperYankGuyWord, flapperYankPackedWord,
      flapperAddressMask_eq_solcAddrMask] using
      solcAddrMask_result_canonical (flapperYankPackedWord σ I)
  have hencGuy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (flapperDealGuyWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperDealGuyWord σ I)) :=
    flapperEncodeValue_addr (flapperDealGuyWord σ I) hcanonGuy
  have hencLot :
      encodeABIValue? uint256 (.int (Int.ofNat (flapperDealLotWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperDealLotWord σ I)) :=
    flapperEncodeValue_uint256 (flapperDealLotWord σ I)
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.codeOwner,
            .address (AccountAddress.ofNat (flapperDealGuyWord σ I).toNat),
            .int (Int.ofNat (flapperDealLotWord σ I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (flapperDealGuyWord σ I) ++
          EVM.Word.toBytesBE (flapperDealLotWord σ I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencOwner, hencGuy,
      hencLot, hdynAddr, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

def flapperDealMoveCallMemFrom (σ : AccountMap) (I : ExecutionEnv)
    (base : ByteArray) : ByteArray :=
  (flapperDealLotWord σ I).toByteArray.write 0
    ((flapperDealGuyWord σ I).toByteArray.write 0
      ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32)
    196 32

theorem flapperDealMoveCallMemFromSelector_size_ge_160
    (base : ByteArray) :
    160 ≤ (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded flapperDealMoveSelectorWord
    base 128

theorem flapperDealMoveCallMemFromThis_size_ge_164
    (I : ExecutionEnv) (base : ByteArray) :
    164 ≤ ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
      132 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.ofNat I.codeOwner.val)
    (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32) 132

theorem flapperDealMoveCallMemFromGuy_size_ge_196
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    196 ≤ ((flapperDealGuyWord σ I).toByteArray.write 0
      ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealGuyWord σ I)
    ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
      132 32) 164

theorem flapperDealMoveCallMemFrom_size_ge_228
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    228 ≤ (flapperDealMoveCallMemFrom σ I base).size := by
  unfold flapperDealMoveCallMemFrom
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealLotWord σ I)
    ((flapperDealGuyWord σ I).toByteArray.write 0
      ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32) 196

theorem flapperDealMoveCallMemFrom_read64
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 64
    (by
      have h := flapperDealMoveCallMemFromGuy_size_ge_196 σ I base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealGuyWord σ I) _ 164 64
    (by
      have h := flapperDealMoveCallMemFromThis_size_ge_164 I base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _
    132 64
    (by
      have h := flapperDealMoveCallMemFromSelector_size_ge_160 base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded flapperDealMoveSelectorWord _
    128 64
    (by omega)
    (by omega)]
  exact hread

theorem flapperDealMoveCallMemFrom_mload64
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    memLoad (UInt256.ofNat 64) (flapperDealMoveCallMemFrom σ I base) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealMoveCallMemFrom_size_ge_228 σ I base
    omega)]
  rw [flapperDealMoveCallMemFrom_read64 σ I base hbase hread]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperDealMoveCallMemFrom_read196
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 196 32 =
      UInt256.toByteArray (flapperDealLotWord σ I) := by
  unfold flapperDealMoveCallMemFrom
  exact toByteArray_write_read_back_of_gap_unbounded (flapperDealLotWord σ I) _ 196

theorem flapperDealMoveCallMemFrom_read164
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 164 32 =
      UInt256.toByteArray (flapperDealGuyWord σ I) := by
  unfold flapperDealMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 164
    (by
      have h := flapperDealMoveCallMemFromGuy_size_ge_196 σ I base
      omega)
    (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded (flapperDealGuyWord σ I) _ 164

theorem flapperDealMoveCallMemFrom_read132
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperDealMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealLotWord σ I) _ 196 132
    (by
      have h := flapperDealMoveCallMemFromGuy_size_ge_196 σ I base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealGuyWord σ I) _ 164 132
    (by
      have h := flapperDealMoveCallMemFromThis_size_ge_164 I base
      omega)
    (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 132

theorem flapperDealMoveCallMemFrom_read128_4
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 128 4 =
      moveSelector := by
  unfold flapperDealMoveCallMemFrom
  rw [toByteArray_write_read_below_len_of_gap (flapperDealLotWord σ I) _ 196 128 4
    (by
      have h := flapperDealMoveCallMemFromGuy_size_ge_196 σ I base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 196 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_below_len_of_gap (flapperDealGuyWord σ I) _ 164 128 4
    (by
      have h := flapperDealMoveCallMemFromThis_size_ge_164 I base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 164 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _
    132 128 4
    (by
      have h := flapperDealMoveCallMemFromSelector_size_ge_160 base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 132 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_window_of_gap_unbounded flapperDealMoveSelectorWord
    base 128 0 4 (by norm_num) (by norm_num) (by norm_num)]
  exact flapperDealMoveSelectorPrefix

theorem flapperDealMoveCallMemFrom_read128_100
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealMoveCallMemFrom σ I base).readWithPadding 128 100 =
      moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealGuyWord σ I) ++
        UInt256.toByteArray (flapperDealLotWord σ I) := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMemFrom σ I base) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemFrom_size_ge_228 σ I base
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMemFrom σ I base) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemFrom_size_ge_228 σ I base
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealMoveCallMemFrom σ I base) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealMoveCallMemFrom_size_ge_228 σ I base
      omega)]
  rw [flapperDealMoveCallMemFrom_read128_4, flapperDealMoveCallMemFrom_read132,
    flapperDealMoveCallMemFrom_read164, flapperDealMoveCallMemFrom_read196]
  simp [ByteArray.append_assoc]

theorem flapperDealMoveEncodeFrom_eq
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    config.externalABI.encode? "move"
        [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperDealGuyWord σ I).toNat),
          .int (Int.ofNat (flapperDealLotWord σ I).toNat)] =
      some ((flapperDealMoveCallMemFrom σ I base).readWithPadding 128 100) := by
  rw [flapperDealMoveCallMemFrom_read128_100]
  simpa [flapperDealMoveCallMem_read128_100] using flapperDealMoveEncode_eq σ I

theorem flapperDealRuntimeMoveCallMem_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (hbase : memLoad (UInt256.ofNat 64)
      (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128) :
    flapperRuntimeBlocks.flapperRuntime_block_3601_memory
        (ee := I) (mem := mem) (σ := σ) (x0 := flapperDealIdWord I) =
      flapperDealMoveCallMemFrom σ I
        (flapperDealScratchMem (flapperDealIdWord I) mem) := by
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperDealBaseSlot (flapperDealIdWord I) := by
    simpa [flapperDealBaseSlot, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  simp [flapperRuntimeBlocks.flapperRuntime_block_3601_memory,
    flapperDealMoveCallMemFrom, flapperDealScratchMem, hbaseRaw, hhashRaw,
    flapperYankMappingHashSlot, flapperDealLotWord, flapperDealGuyWord,
    flapperYankGuyWord, flapperDealPackedWord, flapperYankPackedWord,
    flapperDealVatWord, flapperAddressMask_eq_solcAddrMask, u256_land_comm,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem flapperDealRuntimeMoveCallStack_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) (mem : ByteArray)
    (hscratch : 96 ≤ (flapperDealScratchMem (flapperDealIdWord I) mem).size)
    (hread : (flapperDealScratchMem (flapperDealIdWord I) mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    flapperRuntimeBlocks.flapperRuntime_block_3601_stack
        (ee := I) (mem := mem) (σ := σ) (x0 := flapperDealIdWord I)
        (R := UInt256.ofNat 360 :: [sel]) =
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 3140843579 :: flapperDealVatWord σ I ::
        flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel]) := by
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128 := by
    unfold memLoad
    rw [show (UInt256.ofNat 64).toNat = 64 by decide]
    rw [if_neg (by omega)]
    rw [hread, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperDealBaseSlot (flapperDealIdWord I) := by
    simpa [flapperDealBaseSlot, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  have hcallMem :
      flapperRuntimeBlocks.flapperRuntime_block_3601_memory
          (ee := I) (mem := mem) (σ := σ) (x0 := flapperDealIdWord I) =
        flapperDealMoveCallMemFrom σ I
          (flapperDealScratchMem (flapperDealIdWord I) mem) :=
    flapperDealRuntimeMoveCallMem_eq_from σ I mem hbase
  have hcallFrom :
      memLoad (UInt256.ofNat 64)
        (flapperDealMoveCallMemFrom σ I
          (flapperDealScratchMem (flapperDealIdWord I) mem)) =
        UInt256.ofNat 128 :=
    flapperDealMoveCallMemFrom_mload64 σ I
      (flapperDealScratchMem (flapperDealIdWord I) mem) hscratch hread
  have hcallFromRaw :
      memLoad (UInt256.ofNat 64)
        ((storageRead I.codeOwner σ
            (flapperDealBaseSlot (flapperDealIdWord I) + UInt256.ofNat 1)).toByteArray.write
          0
          ((solcAddrMask.land
              (storageRead I.codeOwner σ
                (flapperDealBaseSlot (flapperDealIdWord I) + UInt256.ofNat 2))).toByteArray.write
            0
            ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
              (((UInt256.ofNat 3140843579).shiftLeft (UInt256.ofNat 224)).toByteArray.write 0
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32)
                (UInt256.ofNat 128).toNat
                32)
              (UInt256.ofNat 128 + UInt256.ofNat 4).toNat
              32)
            (UInt256.ofNat 128 + UInt256.ofNat 36).toNat
            32)
          (UInt256.ofNat 128 + UInt256.ofNat 68).toNat
          32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealMoveCallMemFrom, flapperDealScratchMem, hbaseRaw,
      hhashRaw, flapperDealLotWord, flapperDealGuyWord, flapperYankGuyWord,
      flapperDealPackedWord, flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask,
      u256_land_comm,
      show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) = solcAddrMask by decide,
      show (UInt256.sub
          (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
          (UInt256.ofNat 1)) = solcAddrMask by decide,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide,
      show (UInt256.ofNat 128).toNat = 128 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]
      using hcallFrom
  have hlotRaw :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) +
            UInt256.ofNat 1) =
        flapperDealLotWord σ I := by
    rw [hhashRaw]
    rfl
  simp [flapperRuntimeBlocks.flapperRuntime_block_3601_stack,
    flapperRuntimeBlocks.flapperRuntime_block_3601_memory,
    flapperDealMoveCallMemFrom, hbaseRaw, hcallMem, hcallFromRaw, hhashRaw, hlotRaw,
    flapperYankMappingHashSlot, flapperDealLotWord,
    flapperDealGuyWord, flapperYankGuyWord, flapperDealPackedWord,
    flapperYankPackedWord, flapperDealVatWord, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide]

theorem flapperDealRuntimeMoveCallStack_eq (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_3601_stack
        (ee := I) (mem := flapperDealHashMem (flapperDealIdWord I))
        (σ := σ) (x0 := flapperDealIdWord I)
        (R := UInt256.ofNat 360 :: [sel]) =
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 3140843579 :: flapperDealVatWord σ I ::
        flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel]) := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3601_stack,
    flapperRuntimeBlocks.flapperRuntime_block_3601_memory,
    flapperDealRuntimeMoveCallMem_eq, flapperDealMoveCallRest, flapperDealCallBaseMem,
    flapperYankMoveSelectorWord, flapperYankCallBaseMem, flapperDealHashMem,
    flapperYankMappingHashSlot, flapperDealLotWord, flapperDealGuyWord,
    flapperYankGuyWord, flapperDealMoveCallMem_expr_mload64,
    flapperDealPackedWord, flapperYankPackedWord, flapperDealVatWord,
    flapperAddressMask_eq_solcAddrMask,
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

theorem flapperDealBurnSelectorPrefix :
    flapperDealBurnSelectorWord.toByteArray.extract 0 4 = burnSelector := by
  native_decide

theorem flapperDealBurnCallBaseMem_read64 (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallBaseMem pre σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealBurnCallBaseMem
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have hmove96 : 96 ≤ (flapperDealMoveCallMem pre I).size := by
    have h := flapperDealMoveCallMem_size_ge_228 pre I
    omega
  have h0size :
      ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I) 0 32).size =
        (flapperDealMoveCallMem pre I).size := by
    exact toByteArray_write32_size_of_le (flapperDealMoveCallMem pre I)
      (flapperDealIdWord I) 0 (flapperDealMoveCallMem pre I).size
      (flapperDealMoveCallMem pre I).size rfl (by omega) (by omega)
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [h0size]; omega) (by omega) (by rw [h0size]; omega)]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]
  exact flapperDealMoveCallMem_read64 pre I

theorem flapperDealBurnCallBaseMem_size_ge_96 (pre σ : AccountMap)
    (I : ExecutionEnv) :
    96 ≤ (flapperDealBurnCallBaseMem pre σ I).size := by
  unfold flapperDealBurnCallBaseMem
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have hmove96 : 96 ≤ (flapperDealMoveCallMem pre I).size := by
    have h := flapperDealMoveCallMem_size_ge_228 pre I
    omega
  have h0size :
      ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I) 0 32).size =
        (flapperDealMoveCallMem pre I).size := by
    exact toByteArray_write32_size_of_le (flapperDealMoveCallMem pre I)
      (flapperDealIdWord I) 0 (flapperDealMoveCallMem pre I).size
      (flapperDealMoveCallMem pre I).size rfl (by omega) (by omega)
  have h1size :
      ((UInt256.ofNat 1).toByteArray.write 0
          ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I) 0 32)
          32 32).size =
        (flapperDealMoveCallMem pre I).size := by
    exact toByteArray_write32_size_of_le
      ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I) 0 32)
      (UInt256.ofNat 1) 32 (flapperDealMoveCallMem pre I).size
      (flapperDealMoveCallMem pre I).size h0size (by omega) (by omega)
  rw [h1size]
  exact hmove96

@[simp] theorem flapperDealBurnCallBaseMem_mload64 (pre σ : AccountMap)
    (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperDealBurnCallBaseMem pre σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealBurnCallBaseMem_size_ge_96 pre σ I
    omega)]
  rw [flapperDealBurnCallBaseMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperDealBurnCallMemSelector_size_ge_160
    (pre σ : AccountMap) (I : ExecutionEnv) :
    160 ≤ (flapperDealBurnCallMemSelector pre σ I).size := by
  unfold flapperDealBurnCallMemSelector
  exact toByteArray_write_size_ge_off_add32_unbounded flapperDealBurnSelectorWord
    (flapperDealBurnCallBaseMem pre σ I) 128

theorem flapperDealBurnCallMemThis_size_ge_164
    (pre σ : AccountMap) (I : ExecutionEnv) :
    164 ≤ (flapperDealBurnCallMemThis pre σ I).size := by
  unfold flapperDealBurnCallMemThis
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperDealBurnCallMemSelector pre σ I) 132

theorem flapperDealBurnCallMem_size_ge_196
    (pre σ : AccountMap) (I : ExecutionEnv) :
    196 ≤ (flapperDealBurnCallMem pre σ I).size := by
  unfold flapperDealBurnCallMem
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealBidWord σ I)
    (flapperDealBurnCallMemThis pre σ I) 164

theorem flapperDealBurnCallMem_read64 (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallMem pre σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealBurnCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealBidWord σ I) _ 164 64
    (by
      have h := flapperDealBurnCallMemThis_size_ge_164 pre σ I
      omega)
    (by omega)]
  unfold flapperDealBurnCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _
    132 64
    (by
      have h := flapperDealBurnCallMemSelector_size_ge_160 pre σ I
      omega)
    (by omega)]
  unfold flapperDealBurnCallMemSelector
  rw [toByteArray_write_read_below_of_gap_unbounded flapperDealBurnSelectorWord _
    128 64
    (by
      have h := flapperDealBurnCallBaseMem_size_ge_96 pre σ I
      omega)
    (by omega)]
  exact flapperDealBurnCallBaseMem_read64 pre σ I

@[simp] theorem flapperDealBurnCallMem_mload64
    (pre σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperDealBurnCallMem pre σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealBurnCallMem_size_ge_196 pre σ I
    omega)]
  rw [flapperDealBurnCallMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperDealRuntimeBurnCallMem_eq (pre σ : AccountMap) (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_3731_memory
        (ee := I) (mem := flapperDealMoveCallMem pre I)
        (σ := σ) (x5 := flapperDealIdWord I) =
      flapperDealBurnCallMem pre σ I := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3731_memory,
    flapperDealBurnCallMem, flapperDealBurnCallMemThis,
    flapperDealBurnCallMemSelector, flapperDealBurnCallBaseMem,
    flapperDealBurnSelectorWord, flapperDealMoveCallMem_mload64,
    flapperYankMappingHashSlot, flapperDealBidWord, flapperYankBidWord,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]
  have hbase :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealBurnCallBaseMem] using
      flapperDealBurnCallBaseMem_mload64 pre σ I
  rw [hbase]
  simp [show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]

@[simp] theorem flapperDealRuntimeBurnCallMem_mload64
    (pre σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3731_memory
          (ee := I) (mem := flapperDealMoveCallMem pre I)
          (σ := σ) (x5 := flapperDealIdWord I)) =
      UInt256.ofNat 128 := by
  rw [flapperDealRuntimeBurnCallMem_eq pre σ I]
  exact flapperDealBurnCallMem_mload64 pre σ I

theorem flapperDealBurnCallMem_read164
    (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallMem pre σ I).readWithPadding 164 32 =
      UInt256.toByteArray (flapperDealBidWord σ I) := by
  unfold flapperDealBurnCallMem
  exact toByteArray_write_read_back_of_gap_unbounded (flapperDealBidWord σ I) _ 164

theorem flapperDealBurnCallMem_read132
    (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallMem pre σ I).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperDealBurnCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealBidWord σ I) _ 164 132
    (by
      have h := flapperDealBurnCallMemThis_size_ge_164 pre σ I
      omega)
    (by omega)]
  unfold flapperDealBurnCallMemThis
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.codeOwner.val) (flapperDealBurnCallMemSelector pre σ I) 132

theorem flapperDealBurnCallMem_read128_4
    (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallMem pre σ I).readWithPadding 128 4 = burnSelector := by
  unfold flapperDealBurnCallMem
  rw [toByteArray_write_read_below_len_of_gap (flapperDealBidWord σ I) _ 164 128 4
    (by
      have h := flapperDealBurnCallMemThis_size_ge_164 pre σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMemThis_size_ge_164 pre σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperDealBurnCallMemThis
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 132 128 4
    (by
      have h := flapperDealBurnCallMemSelector_size_ge_160 pre σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMemSelector_size_ge_160 pre σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperDealBurnCallMemSelector
  rw [toByteArray_write_read_window_of_gap_unbounded flapperDealBurnSelectorWord
    (flapperDealBurnCallBaseMem pre σ I) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperDealBurnSelectorPrefix

theorem flapperDealBurnCallMem_read128_68
    (pre σ : AccountMap) (I : ExecutionEnv) :
    (flapperDealBurnCallMem pre σ I).readWithPadding 128 68 =
      burnSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealBidWord σ I) := by
  rw [show 68 = 4 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealBurnCallMem pre σ I) 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMem_size_ge_196 pre σ I
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealBurnCallMem pre σ I) 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMem_size_ge_196 pre σ I
      omega)]
  rw [flapperDealBurnCallMem_read128_4, flapperDealBurnCallMem_read132,
    flapperDealBurnCallMem_read164]
  simp [ByteArray.append_assoc]

theorem flapperDealBurnEncode_eq (pre σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "burn"
        [.address I.codeOwner, .int (Int.ofNat (flapperDealBidWord σ I).toNat)] =
      some ((flapperDealBurnCallMem pre σ I).readWithPadding 128 68) := by
  rw [flapperDealBurnCallMem_read128_68]
  change externalABI.encode? "burn"
        [.address I.codeOwner, .int (Int.ofNat (flapperDealBidWord σ I).toNat)] =
      some (burnSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealBidWord σ I))
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
  have hencBid :
      encodeABIValue? uint256 (.int (Int.ofNat (flapperDealBidWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperDealBidWord σ I)) :=
    flapperEncodeValue_uint256 (flapperDealBidWord σ I)
  have hhead : abiTupleHeadSize? [addr, uint256] = some 64 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, uint256]
          [.address I.codeOwner, .int (Int.ofNat (flapperDealBidWord σ I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (flapperDealBidWord σ I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencOwner,
      hencBid, hdynAddr, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

def flapperDealBurnCallMemFrom (σ : AccountMap) (I : ExecutionEnv)
    (base : ByteArray) : ByteArray :=
  (flapperDealBidWord σ I).toByteArray.write 0
    ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (flapperDealBurnSelectorWord.toByteArray.write 0
        (flapperDealScratchMem (flapperDealIdWord I) base) 128 32)
      132 32)
    164 32

theorem flapperDealBurnCallMemFromSelector_size_ge_160
    (I : ExecutionEnv) (base : ByteArray) :
    160 ≤ (flapperDealBurnSelectorWord.toByteArray.write 0
        (flapperDealScratchMem (flapperDealIdWord I) base) 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded flapperDealBurnSelectorWord
    (flapperDealScratchMem (flapperDealIdWord I) base) 128

theorem flapperDealBurnCallMemFromThis_size_ge_164
    (I : ExecutionEnv) (base : ByteArray) :
    164 ≤ ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
        (flapperDealBurnSelectorWord.toByteArray.write 0
          (flapperDealScratchMem (flapperDealIdWord I) base) 128 32)
        132 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperDealBurnSelectorWord.toByteArray.write 0
      (flapperDealScratchMem (flapperDealIdWord I) base) 128 32)
    132

theorem flapperDealBurnCallMemFrom_size_ge_196
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    196 ≤ (flapperDealBurnCallMemFrom σ I base).size := by
  unfold flapperDealBurnCallMemFrom
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperDealBidWord σ I)
    ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (flapperDealBurnSelectorWord.toByteArray.write 0
        (flapperDealScratchMem (flapperDealIdWord I) base) 128 32)
      132 32)
    164

theorem flapperDealBurnCallMemFrom_read64
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperDealBurnCallMemFrom σ I base).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperDealBurnCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealBidWord σ I) _ 164 64
    (by
      have h := flapperDealBurnCallMemFromThis_size_ge_164 I base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _
    132 64
    (by
      have h := flapperDealBurnCallMemFromSelector_size_ge_160 I base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded flapperDealBurnSelectorWord _
    128 64
    (by
      have h := flapperDealScratchMem_size_ge_96 (flapperDealIdWord I) base hbase
      omega)
    (by omega)]
  exact flapperDealScratchMem_read64 (flapperDealIdWord I) base hbase hread

theorem flapperDealBurnCallMemFrom_mload64
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    memLoad (UInt256.ofNat 64) (flapperDealBurnCallMemFrom σ I base) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperDealBurnCallMemFrom_size_ge_196 σ I base
    omega)]
  rw [flapperDealBurnCallMemFrom_read64 σ I base hbase hread]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperDealBurnCallMemFrom_read164
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealBurnCallMemFrom σ I base).readWithPadding 164 32 =
      UInt256.toByteArray (flapperDealBidWord σ I) := by
  unfold flapperDealBurnCallMemFrom
  exact toByteArray_write_read_back_of_gap_unbounded (flapperDealBidWord σ I) _ 164

theorem flapperDealBurnCallMemFrom_read132
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealBurnCallMemFrom σ I base).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperDealBurnCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperDealBidWord σ I) _ 164 132
    (by
      have h := flapperDealBurnCallMemFromThis_size_ge_164 I base
      omega)
    (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.codeOwner.val)
    (flapperDealBurnSelectorWord.toByteArray.write 0
      (flapperDealScratchMem (flapperDealIdWord I) base) 128 32)
    132

theorem flapperDealBurnCallMemFrom_read128_4
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealBurnCallMemFrom σ I base).readWithPadding 128 4 = burnSelector := by
  unfold flapperDealBurnCallMemFrom
  rw [toByteArray_write_read_below_len_of_gap (flapperDealBidWord σ I) _ 164 128 4
    (by
      have h := flapperDealBurnCallMemFromThis_size_ge_164 I base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 164 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 132 128 4
    (by
      have h := flapperDealBurnCallMemFromSelector_size_ge_160 I base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 132 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_window_of_gap_unbounded flapperDealBurnSelectorWord
    (flapperDealScratchMem (flapperDealIdWord I) base) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperDealBurnSelectorPrefix

theorem flapperDealBurnCallMemFrom_read128_68
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    (flapperDealBurnCallMemFrom σ I base).readWithPadding 128 68 =
      burnSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperDealBidWord σ I) := by
  rw [show 68 = 4 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealBurnCallMemFrom σ I base) 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMemFrom_size_ge_196 σ I base
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperDealBurnCallMemFrom σ I base) 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperDealBurnCallMemFrom_size_ge_196 σ I base
      omega)]
  rw [flapperDealBurnCallMemFrom_read128_4, flapperDealBurnCallMemFrom_read132,
    flapperDealBurnCallMemFrom_read164]
  simp [ByteArray.append_assoc]

theorem flapperDealBurnEncodeFrom_eq
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    config.externalABI.encode? "burn"
        [.address I.codeOwner, .int (Int.ofNat (flapperDealBidWord σ I).toNat)] =
      some ((flapperDealBurnCallMemFrom σ I base).readWithPadding 128 68) := by
  rw [flapperDealBurnCallMemFrom_read128_68]
  simpa [flapperDealBurnCallMem_read128_68] using flapperDealBurnEncode_eq σ σ I

theorem flapperDealRuntimeBurnCallMem_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (hbase : memLoad (UInt256.ofNat 64)
      (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128) :
    flapperRuntimeBlocks.flapperRuntime_block_3731_memory
        (ee := I) (mem := mem) (σ := σ) (x5 := flapperDealIdWord I) =
      flapperDealBurnCallMemFrom σ I mem := by
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperDealBaseSlot (flapperDealIdWord I) := by
    simpa [flapperDealBaseSlot, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  simp [flapperRuntimeBlocks.flapperRuntime_block_3731_memory,
    flapperDealBurnCallMemFrom, flapperDealScratchMem, hbaseRaw, hhashRaw,
    flapperDealBidWord, flapperYankBidWord, flapperDealBurnSelectorWord,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]

theorem flapperDealRuntimeBurnCallStack_eq_from
    (pre σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    flapperRuntimeBlocks.flapperRuntime_block_3731_stack
        (ee := I) (mem := mem) (σ := σ)
        (x4 := flapperDealLotWord pre I) (x5 := flapperDealIdWord I)
        (R := UInt256.ofNat 360 :: [sel]) =
      (flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperDealBurnCallRest pre σ I sel) := by
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128 :=
    flapperDealScratchMem_mload64 (flapperDealIdWord I) mem hmem hread
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperDealBaseSlot (flapperDealIdWord I) := by
    simpa [flapperDealBaseSlot, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  have hburn :
      memLoad (UInt256.ofNat 64) (flapperDealBurnCallMemFrom σ I mem) =
        UInt256.ofNat 128 :=
    flapperDealBurnCallMemFrom_mload64 σ I mem hmem hread
  have hburnRaw :
      memLoad (UInt256.ofNat 64)
        ((storageRead I.codeOwner σ
            (flapperDealBaseSlot (flapperDealIdWord I))).toByteArray.write
          0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            (((UInt256.ofNat 661694443).shiftLeft (UInt256.ofNat 226)).toByteArray.write 0
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32)
              128 32)
            132 32)
          164 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealBurnCallMemFrom, flapperDealScratchMem, hbaseRaw,
      hhashRaw, flapperDealBidWord, flapperYankBidWord, flapperDealBurnSelectorWord,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide,
      show (UInt256.ofNat 128).toNat = 128 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]
      using hburn
  simp [flapperRuntimeBlocks.flapperRuntime_block_3731_stack,
    flapperRuntimeBlocks.flapperRuntime_block_3731_memory, hbaseRaw, hhashRaw,
    hburnRaw, flapperDealBurnCallRest, flapperDealGemWord, flapperYankGemWord,
    flapperDealBidWord, flapperYankBidWord, flapperDealBurnSelectorWord,
    flapperAddressMask_eq_solcAddrMask, u256_land_comm,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 0 + UInt256.ofNat 68 = UInt256.ofNat 68 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 68 = UInt256.ofNat 196 by decide]

theorem flapperDealRuntimeBurnCallStack_eq
    (pre σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_3731_stack
        (ee := I) (mem := flapperDealMoveCallMem pre I)
        (σ := σ) (x4 := flapperDealLotWord pre I)
    (x5 := flapperDealIdWord I)
    (R := UInt256.ofNat 360 :: [sel]) =
      (flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperDealBurnCallRest pre σ I sel) := by
  have hbase :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealBurnCallBaseMem] using
      flapperDealBurnCallBaseMem_mload64 pre σ I
  simp [flapperRuntimeBlocks.flapperRuntime_block_3731_stack,
    flapperRuntimeBlocks.flapperRuntime_block_3731_memory,
    flapperDealRuntimeBurnCallMem_eq, flapperDealBurnCallRest,
    flapperDealBurnCallMem_mload64, flapperDealBurnCallBaseMem,
    flapperDealMoveCallMem_mload64, hbase, flapperYankMappingHashSlot,
    flapperDealBidWord, flapperYankBidWord, flapperDealGemWord, flapperYankGemWord,
    flapperDealBurnSelectorWord, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 0 + UInt256.ofNat 68 = UInt256.ofNat 68 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 68 = UInt256.ofNat 196 by decide]
  have hburn :
      memLoad (UInt256.ofNat 64)
          ((storageRead I.codeOwner σ
                (flapperYankBaseSlot (flapperDealIdWord I))).toByteArray.write 0
            ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
              (((UInt256.ofNat 661694443).shiftLeft (UInt256.ofNat 226)).toByteArray.write 0
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperDealIdWord I).toByteArray.write 0 (flapperDealMoveCallMem pre I)
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)
                128 32)
              132 32)
            164 32) =
        UInt256.ofNat 128 := by
    simpa [flapperDealBurnCallMem, flapperDealBurnCallMemThis,
      flapperDealBurnCallMemSelector, flapperDealBurnCallBaseMem,
      flapperDealBurnSelectorWord, flapperDealBidWord, flapperYankBidWord, hbase,
      show (UInt256.ofNat 128).toNat = 128 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]
      using flapperDealBurnCallMem_mload64 pre σ I
  simp [hburn,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 0 + UInt256.ofNat 68 = UInt256.ofNat 68 by decide]

theorem flapperDispatch_deal {cd : ByteArray}
    (hsel : ((⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some dealTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition])
    (post := [denyTransition, fileTransition, fillTransition, gemTransition,
      kickTransition, kicksTransition, lidTransition, liveTransition,
      relyTransition, tauTransition, tendTransition, tickTransition,
      ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
  · rw [flapperDealSelectorBytes]
    exact hsel

theorem flapperSelectorDispatch_deal {cd : ByteArray}
    (hsel : ((⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some dealTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList]
  rw [show contract.transitions =
      [begTransition, bidsTransition, cageTransition] ++ dealTransition ::
      [denyTransition, fileTransition, fillTransition, gemTransition,
        kickTransition, kicksTransition, lidTransition, liveTransition,
        relyTransition, tauTransition, tendTransition, tickTransition,
        ttlTransition, vatTransition, wardsTransition, yankTransition] by rfl]
  refine dispatchList_eq_some_of_split ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
  · rw [flapperDealSelectorBytes]
    exact hsel

theorem flapperDecode_deal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata =
      some (flapperDealLocals (flapperDealIdWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata =
    some (flapperDealLocals (flapperDealIdWord I))
  simpa [flapperDealLocals, flapperDealIdWord] using
    flapperDecode_yank_ok (I := I) hsz36

theorem flapperDecode_deal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata = none
  exact flapperDecode_yank_none_short (I := I) hsz4 hshort

theorem flapperDealLot_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (flapperDealLotWordOfState evm id).toNat)) := by
  let locals := flapperDealLocals id
  let erLot : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "lot"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperDealLocals, flapperYankLocals]
  have herLot :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "lot") = .ok erLot := by
    simp [locals, erLot, flapperDealLocals, flapperYankLocals, evalStorageRef,
      evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
      EvalResult.ofOption, EvalResult.bind, pure, bind]
  have htyLot : storageTypeAt? contract.storage erLot =
      some (.elem (.int uint256Int)) := by
    simp [erLot, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocLot : config.storage.layout erLot =
      fun _ => some (wordLoc (flapperDealBaseSlot id + UInt256.ofNat 1)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erLot,
      bidsBase, mapSlot, solcMappingSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herLot) (hty := htyLot) (hloc := hlocLot),
    flapperStorageLocLoad_uint256]
  simp [locals, flapperDealLotWordOfState]

theorem flapperDealVarLot_eval (evm : EVM.State) (id lot : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
        (.var "lot") =
      .ok (.int (Int.ofNat lot.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperDealLocalsLot
  exact store_get_self (flapperDealLocals id) "lot"
    (Solm.Value.int (Int.ofNat lot.toNat))

theorem flapperDealVarFillNew_eval (evm : EVM.State) (id lot fillNew : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsAfterSub id lot fillNew }
        evm (.var "fillNew") =
      .ok (.int (Int.ofNat fillNew.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperDealLocalsAfterSub
  exact store_get_self (flapperDealLocalsAfterBurn id lot) "fillNew"
    (Solm.Value.int (Int.ofNat fillNew.toNat))

theorem flapperDealLiveGuard_eval_true (evm : EVM.State) (id : UInt256)
    (hlive : flapperDealLiveWordOfState evm = UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  exact flapperKickLiveGuard_eval_true evm (flapperDealLocals id)
    (by simp [flapperDealLocals, flapperYankLocals]) hlive

theorem flapperDealLiveGuard_eval_false (evm : EVM.State) (id : UInt256)
    (hlive : flapperDealLiveWordOfState evm ≠ UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  exact flapperKickLiveGuard_eval_false evm (flapperDealLocals id)
    (by simp [flapperDealLocals, flapperYankLocals]) hlive

theorem flapperDealTic_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (flapperDealTicWordOfState evm id).toNat)) := by
  simpa [flapperDealLocals, flapperYankLocals, flapperTickLocals,
    flapperDealTicWordOfState, flapperDealPackedWordOfState,
    flapperTickTicWordOfState, flapperTickPackedWordOfState,
    flapperDealPackedSlot, flapperTickPackedSlot, flapperDealBaseSlot,
    flapperTickBaseSlot] using flapperTickTic_eval evm id

theorem flapperDealEnd_eval (evm : EVM.State) (id : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (flapperDealEndWordOfState evm id).toNat)) := by
  simpa [flapperDealLocals, flapperYankLocals, flapperTickLocals,
    flapperDealEndWordOfState, flapperDealPackedWordOfState,
    flapperTickEndWordOfState, flapperTickPackedWordOfState,
    flapperDealPackedSlot, flapperTickPackedSlot, flapperDealBaseSlot,
    flapperTickBaseSlot] using flapperTickEnd_eval evm id

theorem flapperDealTicNeZero_eval_true (evm : EVM.State) (id : UInt256)
    (htic : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool true) := by
  have hTicEval := flapperDealTic_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  have hbeq := flapperTickIntZeroBeq_false (flapperDealTicWordOfState evm id) htic
  have htoNatNe : ¬ (flapperDealTicWordOfState evm id).toNat = 0 := by
    intro hz
    exact htic (uint256_toNat_eq_zero hz)
  simpa [evalBinaryOp?, hbeq, htoNatNe]

theorem flapperDealTicNeZero_eval_false (evm : EVM.State) (id : UInt256)
    (htic : flapperDealTicWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool false) := by
  have hTicEval := flapperDealTic_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  have hbeq := flapperTickIntZeroBeq_true (flapperDealTicWordOfState evm id) htic
  have htoNat : (flapperDealTicWordOfState evm id).toNat = 0 := by
    rw [htic]
    rfl
  simpa [evalBinaryOp?, hbeq, htoNat]

theorem flapperDealTicLt_eval_true (evm : EVM.State) (id : UInt256)
    (htic :
      (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
      .ok (.bool true) := by
  have hTicEval := flapperDealTic_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  have hprop :
      (flapperDealTicWordOfState evm id).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperDealTimestampWordOfState] using htic
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp [envValue, hprop]

theorem flapperDealTicLt_eval_false (evm : EVM.State) (id : UInt256)
    (htic :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
      .ok (.bool false) := by
  have hTicEval := flapperDealTic_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  have hprop :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperDealTimestampWordOfState] using htic
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp [envValue, hprop]

theorem flapperDealEndLt_eval_true (evm : EVM.State) (id : UInt256)
    (hend :
      (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool true) := by
  have hEndEval := flapperDealEnd_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      (flapperDealEndWordOfState evm id).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperDealTimestampWordOfState] using hend
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperDealEndLt_eval_false (evm : EVM.State) (id : UInt256)
    (hend :
      ¬ (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool false) := by
  have hEndEval := flapperDealEnd_eval evm id
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      ¬ (flapperDealEndWordOfState evm id).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperDealTimestampWordOfState] using hend
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperDealTimingGuard_eval_true_tic (evm : EVM.State) (id : UInt256)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .and
          (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
          (.binary .or
            (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
            (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool true) := by
  have hNe := flapperDealTicNeZero_eval_true evm id hticNe
  have hLt := flapperDealTicLt_eval_true evm id hticLt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hNe hLt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hNe, hLt]

theorem flapperDealTimingGuard_eval_true_end (evm : EVM.State) (id : UInt256)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hendLt :
      (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .and
          (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
          (.binary .or
            (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
            (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool true) := by
  have hNe := flapperDealTicNeZero_eval_true evm id hticNe
  have hTic := flapperDealTicLt_eval_false evm id hticLt
  have hEnd := flapperDealEndLt_eval_true evm id hendLt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hNe hTic hEnd
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hNe, hTic, hEnd]

theorem flapperDealTimingGuard_eval_false_tic_zero (evm : EVM.State) (id : UInt256)
    (htic : flapperDealTicWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .and
          (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
          (.binary .or
            (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
            (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool false) := by
  have hNe := flapperDealTicNeZero_eval_false evm id htic
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hNe
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hNe]

theorem flapperDealTimingGuard_eval_false_time (evm : EVM.State) (id : UInt256)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hendLt :
      ¬ (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperDealLocals id } evm
        (.binary .and
          (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
          (.binary .or
            (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
            (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))) =
      .ok (.bool false) := by
  have hNe := flapperDealTicNeZero_eval_true evm id hticNe
  have hTic := flapperDealTicLt_eval_false evm id hticLt
  have hEnd := flapperDealEndLt_eval_false evm id hendLt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hNe hTic hEnd
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hNe, hTic, hEnd]

theorem flapperDealPrefixOk_tic (evm : EVM.State) (id lot : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperDealLiveWordOfState evm = UInt256.ofNat 1)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hlot : lot = flapperDealLotWordOfState evm id) :
    ExecBlock config { contract := contract, locals := flapperDealLocals id } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require
            (.binary .and
              (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (.binary .or
                (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))),
          .letDecl "lot" (some uint256) (.storage (bidsF (.var "id") "lot")) ])
      (.ok { contract := contract, locals := flapperDealLocalsLot id lot } evm) := by
  subst lot
  let frame : Frame := { contract := contract, locals := flapperDealLocals id }
  have hLive := flapperDealLiveGuard_eval_true evm id hlive
  have hTiming := flapperDealTimingGuard_eval_true_tic evm id hticNe hticLt
  have hLot := flapperDealLot_eval evm id
  simpa [nonpayable, frame, flapperDealLocalsLot] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hTiming) <|
      ExecBlock.consNormal (ExecStmt.letDecl hLot) ExecBlock.nil)

theorem flapperDealPrefixOk_end (evm : EVM.State) (id lot : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperDealLiveWordOfState evm = UInt256.ofNat 1)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hendLt :
      (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hlot : lot = flapperDealLotWordOfState evm id) :
    ExecBlock config { contract := contract, locals := flapperDealLocals id } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require
            (.binary .and
              (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
              (.binary .or
                (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))),
          .letDecl "lot" (some uint256) (.storage (bidsF (.var "id") "lot")) ])
      (.ok { contract := contract, locals := flapperDealLocalsLot id lot } evm) := by
  subst lot
  let frame : Frame := { contract := contract, locals := flapperDealLocals id }
  have hLive := flapperDealLiveGuard_eval_true evm id hlive
  have hTiming := flapperDealTimingGuard_eval_true_end evm id hticNe hticLt hendLt
  have hLot := flapperDealLot_eval evm id
  simpa [nonpayable, frame, flapperDealLocalsLot] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hTiming) <|
      ExecBlock.consNormal (ExecStmt.letDecl hLot) ExecBlock.nil)

theorem flapperDealBodyRevertsLive (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperDealLiveWordOfState evm ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperDealLocals id)
      dealTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperDealLocals id }
  have hguard := flapperDealLiveGuard_eval_false evm id hlive
  exact ExecFuncBody.execBlockRevert <| by
    simpa [dealTransition, nonpayable, checkedExternalCallStmts, frame,
      flapperDealLocals] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hguard))

theorem flapperDealBodyRevertsTimingTicZero (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperDealLiveWordOfState evm = UInt256.ofNat 1)
    (htic : flapperDealTicWordOfState evm id = UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperDealLocals id)
      dealTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperDealLocals id }
  have hLive := flapperDealLiveGuard_eval_true evm id hlive
  have hTiming := flapperDealTimingGuard_eval_false_tic_zero evm id htic
  exact ExecFuncBody.execBlockRevert <| by
    simpa [dealTransition, nonpayable, checkedExternalCallStmts, frame,
      flapperDealLocals] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hTiming))

theorem flapperDealBodyRevertsTimingTime (evm : EVM.State) (id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperDealLiveWordOfState evm = UInt256.ofNat 1)
    (hticNe : flapperDealTicWordOfState evm id ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat)
    (hendLt :
      ¬ (flapperDealEndWordOfState evm id).toNat <
        (flapperDealTimestampWordOfState evm).toNat) :
    ExecTransitionBody config contract evm (flapperDealLocals id)
      dealTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperDealLocals id }
  have hLive := flapperDealLiveGuard_eval_true evm id hlive
  have hTiming := flapperDealTimingGuard_eval_false_time evm id hticNe hticLt hendLt
  exact ExecFuncBody.execBlockRevert <| by
    simpa [dealTransition, nonpayable, checkedExternalCallStmts, frame,
      flapperDealLocals] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hTiming))

theorem flapperDealVat_eval_lot (evm : EVM.State) (id lot : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat (flapperDealVatWordOfState evm).toNat)) := by
  simpa [flapperDealVatWordOfState] using
    flapperKickVat_eval evm (flapperDealLocalsLot id lot)
      (by simp [flapperDealLocalsLot, flapperDealLocals, flapperYankLocals])

theorem flapperDealGuy_eval_lot (evm : EVM.State) (id lot : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat
        (flapperDealGuyWordOfState evm id).toNat)) := by
  let locals := flapperDealLocalsLot id lot
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperDealLocalsLot, flapperDealLocals, flapperYankLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    change ((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat))).get? "id" =
      some (.int (Int.ofNat id.toNat))
    rw [store_get_ne (flapperDealLocals id) (k := "lot") (a := "id")
      (.int (Int.ofNat lot.toNat)) (by decide)]
    simp [flapperDealLocals, flapperYankLocals]
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herGuy :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hbase, hgetIdElem]
  have htyGuy : storageTypeAt? contract.storage erGuy =
      some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperDealPackedSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := herGuy) (hty := htyGuy) (hloc := hlocGuy),
    flapperStorageLocLoad_address]
  simp [locals, flapperDealGuyWordOfState, flapperYankGuyWordOfState,
    flapperDealPackedWordOfState, flapperYankPackedWordOfState, flapperDealPackedSlot,
    flapperYankPackedSlot, flapperAddressMask_eq_solcAddrMask]

theorem flapperDealMoveArgs_eval (evm : EVM.State) (id lot : UInt256) :
    evalExprs? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
        [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] =
      .ok [.address evm.executionEnv.codeOwner,
        .address (AccountAddress.ofNat (flapperDealGuyWordOfState evm id).toNat),
        .int (Int.ofNat lot.toNat)] := by
  have hGuyEval := flapperDealGuy_eval_lot evm id lot
  have hLotEval := flapperDealVarLot_eval evm id lot
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval hLotEval
  simp only [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind, bind, pure]
  rw [hGuyEval, hLotEval]

theorem flapperDealVatExtGuard_true (evm : EVM.State) (id lot : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperDealVatWordOfState evm) ≠
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  exact flapperKickExtGuard_true evm (flapperDealLocalsLot id lot)
    (by simp [flapperDealLocalsLot, flapperDealLocals, flapperYankLocals])
    (by simpa [flapperDealVatWordOfState] using hcodeSize)

theorem flapperDealVatExtGuard_false (evm : EVM.State) (id lot : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperDealVatWordOfState evm) =
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsLot id lot } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  exact flapperKickExtGuard_false evm (flapperDealLocalsLot id lot)
    (by simp [flapperDealLocalsLot, flapperDealLocals, flapperYankLocals])
    (by simpa [flapperDealVatWordOfState] using hcodeSize)

theorem flapperDealGem_eval_of_base (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "gem" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat
        (flapperDealGemWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "gem", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm gemRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, gemRef,
      EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    decide
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨3⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_address]
  simp [flapperDealGemWordOfState, flapperYankGemWordOfState,
    show (⟨3⟩ : UInt256) = UInt256.ofNat 3 by decide]

theorem flapperDealGem_eval_afterMove (evm : EVM.State) (id lot : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsAfterMove id lot } evm
        (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat
        (flapperDealGemWordOfState evm).toNat)) := by
  exact flapperDealGem_eval_of_base evm (flapperDealLocalsAfterMove id lot)
    (by simp [flapperDealLocalsAfterMove, flapperDealLocalsLot, flapperDealLocals,
      flapperYankLocals])

theorem flapperDealBid_eval_afterMove (evm : EVM.State) (id lot : UInt256) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsAfterMove id lot } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (flapperDealBidWordOfState evm id).toNat)) := by
  let locals := flapperDealLocalsAfterMove id lot
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperDealLocalsAfterMove, flapperDealLocalsLot, flapperDealLocals,
      flapperYankLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    change (((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat)))
      |>.insert "_moveRet" (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat id.toNat))
    rw [store_get_ne ((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat)))
      (k := "_moveRet") (a := "id") (collapseReturns []) (by decide)]
    rw [store_get_ne (flapperDealLocals id) (k := "lot") (a := "id")
      (.int (Int.ofNat lot.toNat)) (by decide)]
    simp [flapperDealLocals, flapperYankLocals]
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herBid :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "bid") = .ok erBid := by
    simp [erBid, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, bidsF, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind, hbase, hgetIdElem]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperDealBaseSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herBid) (hty := htyBid) (hloc := hlocBid),
    flapperStorageLocLoad_uint256]
  simp [locals, flapperDealBidWordOfState, flapperYankBidWordOfState,
    flapperDealBaseSlot]

theorem flapperDealBurnArgs_eval (evm : EVM.State) (id lot : UInt256) :
    evalExprs? config { contract := contract, locals := flapperDealLocalsAfterMove id lot } evm
        [thisAddr, .storage (bidsF (.var "id") "bid")] =
      .ok [.address evm.executionEnv.codeOwner,
        .int (Int.ofNat (flapperDealBidWordOfState evm id).toNat)] := by
  have hBidEval := flapperDealBid_eval_afterMove evm id lot
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hBidEval
  simp only [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind, bind, pure]
  rw [hBidEval]

theorem flapperDealGemExtGuard_true (evm : EVM.State) (id lot : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperDealGemWordOfState evm) ≠
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsAfterMove id lot } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let targetWord := flapperDealGemWordOfState evm
  have hreceiver := flapperDealGem_eval_afterMove evm id lot
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

theorem flapperDealGemExtGuard_false (evm : EVM.State) (id lot : UInt256)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperDealGemWordOfState evm) =
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperDealLocalsAfterMove id lot } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let targetWord := flapperDealGemWordOfState evm
  have hreceiver := flapperDealGem_eval_afterMove evm id lot
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

theorem flapperDealDeleteStorage_afterBurnRet (evm : EVM.State) (id lot : UInt256) :
    deleteStorage? config
      { contract := contract, locals := flapperDealLocalsAfterBurn id lot } evm
      (bidRef (.var "id")) =
      .ok (flapperDealDeletedState evm id) := by
  let locals := flapperDealLocalsAfterBurn id lot
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat))] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperDealLocalsAfterBurn, flapperDealLocalsAfterMove,
      flapperDealLocalsLot, flapperDealLocals, flapperYankLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    change ((((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat)))
      |>.insert "_moveRet" (collapseReturns []))
      |>.insert "_burnRet" (collapseReturns [])).get? "id" =
      some (.int (Int.ofNat id.toNat))
    rw [store_get_ne (((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat)))
      |>.insert "_moveRet" (collapseReturns [])) (k := "_burnRet") (a := "id")
      (collapseReturns []) (by decide)]
    rw [store_get_ne ((flapperDealLocals id).insert "lot" (.int (Int.ofNat lot.toNat)))
      (k := "_moveRet") (a := "id") (collapseReturns []) (by decide)]
    rw [store_get_ne (flapperDealLocals id) (k := "lot") (a := "id")
      (.int (Int.ofNat lot.toNat)) (by decide)]
    simp [flapperDealLocals, flapperYankLocals]
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
    .ok (flapperDealDeletedState evm id)
  rw [deleteStorage?]
  simp only [resolveStorageRef?_ok (cfg := config) (solm := solm) (evm := evm)
    (slot := bidRef (.var "id")) (er := er) (ty := BidStructTy) hbase her hty,
    bind, EvalResult.bind]
  simp [solm, locals, er, clearStorage?, clearFields?, config, storageLayout,
    solidityStorageLayout, storageLayoutRaw, contract, storageDecls, BidStructTy,
    uint256St, addrSt, uint48St, flapperDealDeletedState, flapperYankDeleteState,
    flapperYankDeleteTicState, flapperYankDeleteGuyState,
    flapperYankDeleteBidLotState, flapperYankPackedSlot, flapperYankBaseSlot,
    flapperDealPackedSlot, flapperDealBaseSlot,
    flapperStorageLocStore_word_zero, flapperStorageLocStore_address_zero, EvalResult.ofOption,
    flapperStorageLocStore_uint48_offset20_zero_any,
    flapperStorageLocStore_uint48_offset26_zero, storageStore_executionEnv]
  simpa [bidsBase, mapSlot, flapperKeyValueToWord_uint256_natCast, solcMappingSlot,
    show ({ val := 1 } : UInt256) = UInt256.ofNat 1 by decide,
    show ({ val := 2 } : UInt256) = UInt256.ofNat 2 by decide]

theorem flapperDealSubArgs_eval (evm : EVM.State) (id lot : UInt256) :
    evalExprs? config { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
        evm [.storage fillRef, .var "lot"] =
      .ok [.int (Int.ofNat (flapperDealFillWordOfState evm).toNat),
        .int (Int.ofNat lot.toNat)] := by
  have hFill := flapperKickFill_eval evm (flapperDealLocalsAfterBurn id lot)
    (by simp [flapperDealLocalsAfterBurn, flapperDealLocalsAfterMove,
      flapperDealLocalsLot, flapperDealLocals, flapperYankLocals])
  have hLot :
      evalExpr? config
        { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
        evm (.var "lot") = .ok (.int (Int.ofNat lot.toNat)) := by
    apply flapperKickVarInt_eval
    unfold flapperDealLocalsAfterBurn flapperDealLocalsAfterMove flapperDealLocalsLot
    rw [store_get_ne ((flapperDealLocals id).insert "lot"
      (.int (Int.ofNat lot.toNat)) |>.insert "_moveRet" (collapseReturns []))
      (k := "_burnRet") (a := "lot") (collapseReturns []) (by decide)]
    rw [store_get_ne ((flapperDealLocals id).insert "lot"
      (.int (Int.ofNat lot.toNat))) (k := "_moveRet") (a := "lot")
      (collapseReturns []) (by decide)]
    exact store_get_self (flapperDealLocals id) "lot" (.int (Int.ofNat lot.toNat))
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hFill hLot
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [hFill, hLot]

theorem flapperDealSub_eval_ok (evm : EVM.State) (x y : UInt256)
    (hok : y.toNat ≤ x.toNat) :
    evalExpr? config
        { contract := contract, locals := flapperDealSubLocals x y }
        evm (sub256 (.var "x") (.var "y")) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
  have hsub :
      Int.ofNat x.toNat - Int.ofNat y.toNat =
        Int.ofNat (x.toNat - y.toNat) := by
    exact (Int.ofNat_sub hok).symm
  have hnotHigh :
      ¬ Int.ofNat x.toNat - Int.ofNat y.toNat ≥ (2 : Int) ^ 256 := by
    have hx : x.toNat < UInt256.size := x.val.isLt
    have hlt : x.toNat - y.toNat < UInt256.size := by omega
    have hltInt : Int.ofNat (x.toNat - y.toNat) < (2 : Int) ^ 256 := by
      have hpow : UInt256.size = (2 : Nat) ^ 256 := by
        rfl
      exact Int.ofNat_lt.mpr (by simpa [hpow] using hlt)
    intro hge
    rw [hsub] at hge
    exact (not_le_of_gt hltInt) hge
  have hgetX : (flapperDealSubLocals x y).get? "x" =
      some (.int (Int.ofNat x.toNat)) := by
    simp [flapperDealSubLocals]
  have hgetY : (flapperDealSubLocals x y).get? "y" =
      some (.int (Int.ofNat y.toNat)) := by
    change (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
      (.int (Int.ofNat x.toNat))).get? "y" = some (.int (Int.ofNat y.toNat))
    rw [store_get_ne ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat)))
      (k := "x") (a := "y") (.int (Int.ofNat x.toNat)) (by decide)]
    exact store_get_self (∅ : Store) "y" (.int (Int.ofNat y.toNat))
  simp only [sub256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    EvalResult.ofOption, hgetX, hgetY, evalBinaryOp?]
  rw [hsub]
  have hleft : decide (Int.ofNat (x.toNat - y.toNat) < 0) = false := by
    exact decide_eq_false (by
      intro hlt
      exact (not_lt_of_ge (Int.ofNat_nonneg _)) hlt)
  have hright :
      decide (Int.ofNat (x.toNat - y.toNat) ≥ (2 : Int) ^ 256) = false := by
    rw [← hsub]
    exact decide_eq_false hnotHigh
  rw [hleft, hright]
  simpa [usub_toNat (a := x) (b := y) hok]

theorem flapperDealSub_eval_revert (evm : EVM.State) (x y : UInt256)
    (hbad : x.toNat < y.toNat) :
    evalExpr? config
        { contract := contract, locals := flapperDealSubLocals x y }
        evm (sub256 (.var "x") (.var "y")) =
      .revert := by
  have hneg : Int.ofNat x.toNat - Int.ofNat y.toNat < 0 := by
    have hltInt : (Int.ofNat x.toNat : Int) < Int.ofNat y.toNat :=
      Int.ofNat_lt.mpr hbad
    omega
  have hgetX : (flapperDealSubLocals x y).get? "x" =
      some (.int (Int.ofNat x.toNat)) := by
    simp [flapperDealSubLocals]
  have hgetY : (flapperDealSubLocals x y).get? "y" =
      some (.int (Int.ofNat y.toNat)) := by
    change (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
      (.int (Int.ofNat x.toNat))).get? "y" = some (.int (Int.ofNat y.toNat))
    rw [store_get_ne ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat)))
      (k := "x") (a := "y") (.int (Int.ofNat x.toNat)) (by decide)]
    exact store_get_self (∅ : Store) "y" (.int (Int.ofNat y.toNat))
  simp only [sub256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    EvalResult.ofOption, hgetX, hgetY, evalBinaryOp?]
  have hleft : decide (Int.ofNat x.toNat - Int.ofNat y.toNat < 0) = true := by
    exact decide_eq_true hneg
  rw [hleft]
  simp

theorem flapperDealSubGuard_eval_true (evm : EVM.State) (x y : UInt256)
    (hok : y.toNat ≤ x.toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperDealSubLocalsZ x y (UInt256.sub x y) }
        evm (.binary .le (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hgetZ : (flapperDealSubLocalsZ x y (UInt256.sub x y)).get? "z" =
      some (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
    simp [flapperDealSubLocalsZ]
  have hgetX : (flapperDealSubLocalsZ x y (UInt256.sub x y)).get? "x" =
      some (.int (Int.ofNat x.toNat)) := by
    change ((flapperDealSubLocals x y).insert "z"
      (.int (Int.ofNat (UInt256.sub x y).toNat))).get? "x" =
      some (.int (Int.ofNat x.toNat))
    rw [store_get_ne (flapperDealSubLocals x y) (k := "z") (a := "x")
      (.int (Int.ofNat (UInt256.sub x y).toNat)) (by decide)]
    simp [flapperDealSubLocals]
  simp only [evalExpr?, EvalResult.bind, bind, pure, EvalResult.ofOption, hgetZ, hgetX]
  have hleNat : (UInt256.sub x y).toNat ≤ x.toNat := by
    rw [usub_toNat (a := x) (b := y) hok]
    omega
  have hleInt :
      Int.ofNat (UInt256.sub x y).toNat ≤ Int.ofNat x.toNat := by
    exact Int.ofNat_le.mpr hleNat
  have hdec :
      decide (Int.ofNat (UInt256.sub x y).toNat ≤ Int.ofNat x.toNat) = true :=
    decide_eq_true hleInt
  simpa [evalBinaryOp?, hdec] using hleNat

theorem flapperDealSubGuard_eval_false (evm : EVM.State) (x y : UInt256)
    (hbad : x.toNat < y.toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperDealSubLocalsZ x y (UInt256.sub x y) }
        evm (.binary .le (.var "z") (.var "x")) =
      .ok (.bool false) := by
  have hgetZ : (flapperDealSubLocalsZ x y (UInt256.sub x y)).get? "z" =
      some (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
    simp [flapperDealSubLocalsZ]
  have hgetX : (flapperDealSubLocalsZ x y (UInt256.sub x y)).get? "x" =
      some (.int (Int.ofNat x.toNat)) := by
    change ((flapperDealSubLocals x y).insert "z"
      (.int (Int.ofNat (UInt256.sub x y).toNat))).get? "x" =
      some (.int (Int.ofNat x.toNat))
    rw [store_get_ne (flapperDealSubLocals x y) (k := "z") (a := "x")
      (.int (Int.ofNat (UInt256.sub x y).toNat)) (by decide)]
    simp [flapperDealSubLocals]
  simp only [evalExpr?, EvalResult.bind, bind, pure, EvalResult.ofOption, hgetZ, hgetX]
  have hlarge : x.toNat < (UInt256.sub x y).toNat := by
    rw [usub_toNat_underflow (a := x) (b := y) hbad]
    have hy : y.toNat < UInt256.size := y.val.isLt
    omega
  have hnotInt :
      ¬ Int.ofNat (UInt256.sub x y).toNat ≤ Int.ofNat x.toNat := by
    intro hle
    exact (not_le_of_gt hlarge) (Int.ofNat_le.mp hle)
  have hdec :
      decide (Int.ofNat (UInt256.sub x y).toNat ≤ Int.ofNat x.toNat) = false :=
    decide_eq_false hnotInt
  simpa [evalBinaryOp?, hdec] using hlarge

theorem flapperDealSubBodyReturns (evm : EVM.State) (x y : UInt256)
    (hok : y.toNat ≤ x.toNat) :
    ExecFuncBody config
      { contract := contract, locals := flapperDealSubLocals x y }
      evm subFunction.body
      (.returned
        { contract := contract, locals := flapperDealSubLocalsZ x y (UInt256.sub x y) }
        evm (some [.int (Int.ofNat (UInt256.sub x y).toNat)])) := by
  let localsXY := flapperDealSubLocals x y
  let frameXY : Frame := { contract := contract, locals := localsXY }
  let localsZ := flapperDealSubLocalsZ x y (UInt256.sub x y)
  let frameZ : Frame := { contract := contract, locals := localsZ }
  have hLet : evalExpr? config frameXY evm (sub256 (.var "x") (.var "y")) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
    simpa [frameXY, localsXY] using flapperDealSub_eval_ok evm x y hok
  have hGuard : evalExpr? config frameZ evm (.binary .le (.var "z") (.var "x")) =
      .ok (.bool true) := by
    simpa [frameZ, localsZ, localsXY] using flapperDealSubGuard_eval_true evm x y hok
  have hRetExpr :
      evalExprs? config frameZ evm [.var "z"] =
        .ok [.int (Int.ofNat (UInt256.sub x y).toNat)] := by
    simp [frameZ, localsZ, localsXY, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, flapperDealSubLocalsZ]
  have hblock :
      ExecBlock config frameXY evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned frameZ evm (some [.int (Int.ofNat (UInt256.sub x y).toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hLet) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hGuard) ?_
    exact ExecBlock.consReturn (ExecStmt.return hRetExpr)
  exact ExecFuncBody.execBlockRet <| by
    simpa [subFunction, checkedSubUintInto, localsXY, frameXY, localsZ, frameZ,
      flapperDealSubLocalsZ] using hblock

theorem flapperDealSubBodyReverts (evm : EVM.State) (x y : UInt256)
    (hbad : x.toNat < y.toNat) :
    ExecFuncBody config
      { contract := contract, locals := flapperDealSubLocals x y }
      evm subFunction.body .reverted := by
  let localsXY := flapperDealSubLocals x y
  let frameXY : Frame := { contract := contract, locals := localsXY }
  exact ExecFuncBody.execBlockRevert <| by
    simpa [subFunction, checkedSubUintInto, localsXY, frameXY] using
      (ExecBlock.consRevert (ExecStmt.letDeclRevert
        (by simpa [frameXY, localsXY] using flapperDealSub_eval_revert evm x y hbad)) :
      ExecBlock config frameXY evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ] .reverted)

theorem flapperDealInternalSubReturn (evm : EVM.State) (id lot : UInt256)
    (hok :
      (flapperDealFillNewWordOfState evm id lot).toNat ≤
        (flapperDealFillWordOfState (flapperDealDeletedState evm id)).toNat) :
    ExecStmt config
      { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
      (flapperDealDeletedState evm id)
      (.internalCall "sub" [.storage fillRef, .var "lot"] "fillNew")
      (.ok (flapperDealAfterSubFrame id lot (flapperDealFillNewWordOfState evm id lot))
        (flapperDealDeletedState evm id)) := by
  let evmDel := flapperDealDeletedState evm id
  let caller : Frame := { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
  let x := flapperDealFillWordOfState evmDel
  let y := lot
  have hargs : evalExprs? config
      caller
      evmDel [.storage fillRef, .var "lot"] =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simpa [caller, evmDel, x, y] using flapperDealSubArgs_eval evmDel id lot
  have hlookup : lookupCallable? contract "sub" = some subFunction.toCallable := by
    rfl
  have hbind : bindParams? subFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (flapperDealSubLocals x y) := by
    rfl
  have hbody :
      ExecFuncBody config
        { caller with locals := flapperDealSubLocals x y }
        evmDel subFunction.body
        (.returned
          { contract := contract, locals := flapperDealSubLocalsZ x y (UInt256.sub x y) }
          evmDel (some [.int (Int.ofNat (UInt256.sub x y).toNat)])) := by
    have hyx : y.toNat ≤ x.toNat := by
      by_contra hnot
      have hlt : x.toNat < y.toNat := Nat.lt_of_not_ge hnot
      have hgt : x.toNat < (UInt256.sub x y).toNat := by
        rw [usub_toNat_underflow (a := x) (b := y) hlt]
        have hy : y.toNat < UInt256.size := y.val.isLt
        omega
      exact (not_le_of_gt hgt) (by
        simpa [x, y, flapperDealFillNewWordOfState, evmDel] using hok)
    simpa [caller] using flapperDealSubBodyReturns evmDel x y hyx
  have hstmt := internalCallFunctionReturn (cfg := config)
      (caller := caller)
      (evm := evmDel) (calleeEvm := evmDel)
      (name := "sub") (args := [.storage fillRef, .var "lot"]) (retVar := "fillNew")
      (argVals := [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)])
      (callee := subFunction)
      (locals := flapperDealSubLocals x y)
      (calleeSolm :=
        { contract := contract, locals := flapperDealSubLocalsZ x y (UInt256.sub x y) })
      (value := some [Value.int (Int.ofNat (UInt256.sub x y).toNat)])
      hargs hlookup hbind hbody
  simpa [caller, resumeAfterInternalCall, flapperDealAfterSubFrame, flapperDealLocalsAfterSub,
    flapperDealFillNewWordOfState, evmDel, x, y] using hstmt

theorem flapperDealInternalSubRevert (evm : EVM.State) (id lot : UInt256)
    (hbad :
      ¬ (flapperDealFillNewWordOfState evm id lot).toNat ≤
        (flapperDealFillWordOfState (flapperDealDeletedState evm id)).toNat) :
    ExecStmt config
      { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
      (flapperDealDeletedState evm id)
      (.internalCall "sub" [.storage fillRef, .var "lot"] "fillNew")
      .reverted := by
  let evmDel := flapperDealDeletedState evm id
  let caller : Frame := { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
  let x := flapperDealFillWordOfState evmDel
  let y := lot
  have hargs : evalExprs? config
      caller
      evmDel [.storage fillRef, .var "lot"] =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simpa [caller, evmDel, x, y] using flapperDealSubArgs_eval evmDel id lot
  have hlookup : lookupCallable? contract "sub" = some subFunction.toCallable := by
    rfl
  have hbind : bindParams? subFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (flapperDealSubLocals x y) := by
    rfl
  have hbody :
      ExecFuncBody config
        { caller with locals := flapperDealSubLocals x y }
        evmDel subFunction.body .reverted := by
    have hlt : x.toNat < y.toNat := by
      by_contra hnot
      have hyx : y.toNat ≤ x.toNat := le_of_not_gt hnot
      have hsub := usub_toNat (a := x) (b := y) hyx
      have hle : (UInt256.sub x y).toNat ≤ x.toNat := by
        rw [hsub]
        omega
      exact hbad (by simpa [x, y, flapperDealFillNewWordOfState, evmDel] using hle)
    simpa [caller] using flapperDealSubBodyReverts evmDel x y hlt
  exact internalCallFunctionRevert (cfg := config)
      (caller := caller)
      (evm := evmDel)
      (name := "sub") (args := [.storage fillRef, .var "lot"]) (retVar := "fillNew")
      (argVals := [Value.int (Int.ofNat x.toNat), Value.int (Int.ofNat y.toNat)])
      (callee := subFunction)
      (locals := flapperDealSubLocals x y)
      hargs hlookup hbind hbody

theorem flapperDealAssignFill (evm : EVM.State) (id lot fillNew : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperDealLocalsAfterSub id lot fillNew } evm
      .storage fillRef (.int (Int.ofNat fillNew.toNat)) =
      .ok ({ contract := contract, locals := flapperDealLocalsAfterSub id lot fillNew },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 9) fillNew) := by
  let locals := flapperDealLocalsAfterSub id lot fillNew
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "fill", steps := [] }
  have hbase : locals.get? "fill" = none := by
    simp [locals, flapperDealLocalsAfterSub, flapperDealLocalsAfterBurn,
      flapperDealLocalsAfterMove, flapperDealLocalsLot, flapperDealLocals,
      flapperYankLocals]
  have her : evalStorageRef config solm evm fillRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨9⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨9⟩ : UInt256)) (.int (Int.ofNat fillNew.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 9) fillNew) := by
    simpa [wordLoc, uint256Loc, show (⟨9⟩ : UInt256) = UInt256.ofNat 9 by decide] using
      storageLocStore_uint256 evm (⟨9⟩ : UInt256) fillNew
  change assignStorageRef? config solm evm .storage fillRef
      (.int (Int.ofNat fillNew.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (UInt256.ofNat 9) fillNew)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperDealTailReturns (evm : EVM.State) (id lot : UInt256)
    (hok :
      (flapperDealFillNewWordOfState evm id lot).toNat ≤
        (flapperDealFillWordOfState (flapperDealDeletedState evm id)).toNat) :
    ExecBlock config { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
      evm
      [ .delete (bidRef (.var "id")),
        .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
        .assign .storage fillRef (.var "fillNew") ]
      (.ok (flapperDealAfterSubFrame id lot (flapperDealFillNewWordOfState evm id lot))
        (flapperDealAfterFillState evm id lot)) := by
  have hdelete := flapperDealDeleteStorage_afterBurnRet evm id lot
  have hsub := flapperDealInternalSubReturn evm id lot hok
  have hfillEval :
      evalExpr? config
        (flapperDealAfterSubFrame id lot (flapperDealFillNewWordOfState evm id lot))
        (flapperDealDeletedState evm id)
        (.var "fillNew") =
        .ok (.int (Int.ofNat (flapperDealFillNewWordOfState evm id lot).toNat)) := by
    exact flapperDealVarFillNew_eval (flapperDealDeletedState evm id) id lot
      (flapperDealFillNewWordOfState evm id lot)
  have hassign := flapperDealAssignFill (flapperDealDeletedState evm id) id lot
    (flapperDealFillNewWordOfState evm id lot)
  have hassignOk :
      assignStorageRef? config
        (flapperDealAfterSubFrame id lot (flapperDealFillNewWordOfState evm id lot))
        (flapperDealDeletedState evm id)
        .storage fillRef
        (.int (Int.ofNat (flapperDealFillNewWordOfState evm id lot).toNat)) =
        .ok (flapperDealAfterSubFrame id lot (flapperDealFillNewWordOfState evm id lot),
          flapperDealAfterFillState evm id lot) := by
    simpa [flapperDealAfterSubFrame, flapperDealAfterFillState,
      flapperDealDeletedState, flapperYankDeleteState, flapperYankDeleteTicState,
      flapperYankDeleteGuyState, flapperYankDeleteBidLotState, storageStore_executionEnv]
      using hassign
  refine ExecBlock.consNormal (ExecStmt.delete hdelete) ?_
  refine ExecBlock.consNormal hsub ?_
  exact ExecBlock.consNormal (ExecStmt.assign hfillEval hassignOk) ExecBlock.nil

theorem flapperDealTailRevertsSub (evm : EVM.State) (id lot : UInt256)
    (hbad :
      ¬ (flapperDealFillNewWordOfState evm id lot).toNat ≤
        (flapperDealFillWordOfState (flapperDealDeletedState evm id)).toNat) :
    ExecBlock config { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
      evm
      [ .delete (bidRef (.var "id")),
        .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
        .assign .storage fillRef (.var "fillNew") ]
      .reverted := by
  have hdelete := flapperDealDeleteStorage_afterBurnRet evm id lot
  have hsub := flapperDealInternalSubRevert evm id lot hbad
  exact ExecBlock.consNormal (ExecStmt.delete hdelete)
    (ExecBlock.consRevert hsub)

theorem flapperDealStorageLoad_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      storageRead I.codeOwner σworld slot := by
  have hmap :
      Solm.EVM.storageLoad
          (initState cAcur gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        Solm.EVM.storageLoad evm I.codeOwner slot := by
    exact storageLoad_accountMapEquiv
      (evm1 := initState cAcur gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
      (evm2 := evm)
      (by simpa [initState] using hState.accounts)
      I.codeOwner slot
  have hread :
      Solm.EVM.storageLoad
          (initState cAcur gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        storageRead I.codeOwner σworld slot := by
    simp [initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageRead_eq]
  have howner : evm.executionEnv.codeOwner = I.codeOwner := by
    rw [hState.env]
  rw [howner]
  exact hmap.symm.trans hread

theorem flapperDealAfterFillState_createdAccounts
    (evm : EVM.State) (id lot : UInt256) :
    (flapperDealAfterFillState evm id lot).createdAccounts = evm.createdAccounts := by
  simp [flapperDealAfterFillState, flapperDealDeletedState,
    flapperYankDeleteState_createdAccounts, storageStore_createdAccounts]

theorem flapperDealDeletedFillLoad_eq
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hEnv : evm.executionEnv = I) :
    flapperDealFillWordOfState
        (flapperDealDeletedState evm (flapperDealIdWord I)) =
      storageRead I.codeOwner (flapperDealDeletedAccountMap σ I)
        (UInt256.ofNat 9) := by
  have hdel :
      accountMapEquiv (flapperDealDeletedAccountMap σ I)
        (flapperDealDeletedState evm (flapperDealIdWord I)).accountMap := by
    simpa [flapperDealDeletedAccountMap, flapperDealDeletedState,
      flapperDealIdWord] using
      flapperYankDeleteState_accountMapEquiv
        (σ := σ) (evm := evm) (I := I) hAccounts hEnv
  have hfind := accountMapEquiv_storage_findD hdel I.codeOwner
    (UInt256.ofNat 9) (default : UInt256)
  have howner :
      (flapperDealDeletedState evm (flapperDealIdWord I)).executionEnv.codeOwner =
        I.codeOwner := by
    simp [flapperDealDeletedState, flapperYankDeleteState,
      flapperYankDeleteTicState, flapperYankDeleteGuyState,
      flapperYankDeleteBidLotState, storageStore_executionEnv, hEnv]
  simpa [flapperDealFillWordOfState, flapperKickFillWordOfState,
    storageRead_eq, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, howner] using hfind.symm

theorem flapperDealAfterFillWorldFrom_accountMapEquiv
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hEnv : evm.executionEnv = I) (lot : UInt256) :
    accountMapEquiv (flapperDealAfterFillWorldFrom σ I lot)
      (flapperDealAfterFillState evm (flapperDealIdWord I) lot).accountMap := by
  have hdel :
      accountMapEquiv (flapperDealDeletedAccountMap σ I)
        (flapperDealDeletedState evm (flapperDealIdWord I)).accountMap := by
    simpa [flapperDealDeletedAccountMap, flapperDealDeletedState,
      flapperDealIdWord] using
      flapperYankDeleteState_accountMapEquiv
        (σ := σ) (evm := evm) (I := I) hAccounts hEnv
  have hfillLoad :
      flapperDealFillWordOfState
          (flapperDealDeletedState evm (flapperDealIdWord I)) =
        storageRead I.codeOwner (flapperDealDeletedAccountMap σ I)
          (UInt256.ofNat 9) := by
    exact flapperDealDeletedFillLoad_eq hAccounts hEnv
  have hfillNew :
      flapperDealFillNewWordFrom σ I lot =
        flapperDealFillNewWordOfState evm (flapperDealIdWord I) lot := by
    simp [flapperDealFillNewWordFrom, flapperDealFillNewWordOfState,
      hfillLoad]
  have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner
    (UInt256.ofNat 9) (flapperDealFillNewWordFrom σ I lot) hdel
  simpa [flapperDealAfterFillWorldFrom, flapperDealAfterFillState,
    storageWrite_eq, storageStore_accountMap, hEnv, hfillNew] using hstore

theorem flapperX_deal_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3334)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd767⟩ := hreach
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
  have rd789 := flapperRuntimeBlocks.flapperRuntime_block_767_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd767
  have rd3334 := flapperRuntimeBlocks.flapperRuntime_block_789
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd789
  exact ⟨_, _, by simpa [flapperDealIdWord, flapperYankIdWord, calldataWord] using rd3334⟩

theorem flapperX_deal_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd767⟩ := hreach
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
  have rd785 := flapperRuntimeBlocks.flapperRuntime_block_767_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd767
  exact flapperRuntimeBlocks.flapperRuntime_block_785
    (R := flapperRuntimeBlocks.flapperRuntime_block_767_fallthrough_stack
      (ee := I) (R := [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_767_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd785

theorem flapperX_deal_live_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) ≠ UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3334) (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3334⟩ := hdecode
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 7)) =
        UInt256.ofNat 0 :=
    u256_eq_of_ne (by intro h; exact hlive h.symm)
  obtain ⟨_, _, rd3345⟩ := flapperRuntimeBlocks.flapperRuntime_block_3334_fallthrough
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLive rd3334
  exact flapperRuntimeBlocks.flapperRuntime_block_3345
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3345

theorem flapperX_deal_live_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3334) (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3408) (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3334⟩ := hdecode
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 7)) ≠
        UInt256.ofNat 0 := by
    rw [hlive]
    decide
  obtain ⟨aw, k, C, rd3408⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3334_taken_packed
      (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLive (by jump_dest) rd3334
  exact ⟨aw, k, C, rd3408⟩

@[simp] theorem flapperDealRuntimeTicRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.land (UInt256.ofNat 281474976710655)
        (UInt256.div
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperDealIdWord I).toByteArray.write 0 mem
                    0 32)
                  32 32))))
          (UInt256.ofNat 1461501637330902918203684832716283019655932542976)) =
      flapperDealTicWord σ I := by
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperYankBaseSlot (flapperDealIdWord I) := by
    simpa [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  rw [hhash]
  simp [flapperDealTicWord, flapperDealPackedWord, flapperYankPackedWord,
    flapperDealIdWord, flapperYankBaseSlot, flapperUint48Mask, flapperUint48Shift160,
    u256_add_comm]

@[simp] theorem flapperDealRuntimeEndRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.land (UInt256.ofNat 281474976710655)
        (UInt256.div
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperDealIdWord I).toByteArray.write 0 mem
                    0 32)
                  32 32))))
          (UInt256.ofNat 411376139330301510538742295639337626245683966408394965837152256)) =
      flapperDealEndWord σ I := by
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperYankBaseSlot (flapperDealIdWord I) := by
    simpa [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperDealIdWord I) mem
  rw [hhash]
  simp [flapperDealEndWord, flapperDealPackedWord, flapperYankPackedWord,
    flapperDealIdWord, flapperYankBaseSlot, flapperUint48Mask, flapperUint48Shift208,
    u256_add_comm]

theorem flapperX_deal_tic_zero_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (htic : flapperDealTicWord σ I = UInt256.ofNat 0)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw3408, _, _, rd3408⟩ := h3408
  have hcond3408 :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperDealIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) ≠
        UInt256.ofNat 0 := by
    have hzero : UInt256.isZero (flapperDealTicWord σ I) ≠ UInt256.ofNat 0 := by
      rw [htic]
      decide
    simpa [flapperDealTicWord, flapperDealPackedWord, flapperYankPackedWord,
      flapperYankMappingHashSlot, flapperYankBaseSlot, flapperUint48Mask,
      flapperUint48Shift160, u256_add_comm] using hzero
  obtain ⟨aw3529, k3529, C3529, rd3529raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3408_taken_packed
      (x0 := flapperDealIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond3408 (by jump_dest) rd3408
  have rd3529 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3529)
        (UInt256.ofNat 0 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealHashMem (flapperDealIdWord I)) aw3529 ByteArray.empty
        (cA, σ) k3529 C3529 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3408_taken_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3408_taken_memory,
      htic, flapperDealHashMem, flapperYankHashMem,
      flapperRuntimeBlocks.flapperRuntime_block_964_taken_memory,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3529raw
  have rd3534 := flapperRuntimeBlocks.flapperRuntime_block_3529_fallthrough
    (x0 := UInt256.ofNat 0)
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) rd3529
  exact flapperRuntimeBlocks.flapperRuntime_block_3534
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3534

theorem flapperX_deal_tic_ne_to_3450 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hticNe : flapperDealTicWord σ I ≠ UInt256.ofNat 0)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3450)
      (UInt256.ofNat 1 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealHashMem (flapperDealIdWord I)) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3408, _, _, rd3408⟩ := h3408
  have hcond3408 :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperDealIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) =
        UInt256.ofNat 0 := by
    have hnonzero :
        UInt256.isZero (flapperDealTicWord σ I) = UInt256.ofNat 0 :=
      isZero_eq_zero_of_ne hticNe
    simpa [flapperDealTicWord, flapperDealPackedWord, flapperYankPackedWord,
      flapperYankMappingHashSlot, flapperYankBaseSlot, flapperUint48Mask,
      flapperUint48Shift160, u256_add_comm] using hnonzero
  obtain ⟨aw3450, k3450, C3450, rd3450raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3408_fallthrough_packed
      (x0 := flapperDealIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond3408 rd3408
  have rd3450 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3450)
        (UInt256.ofNat 1 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealHashMem (flapperDealIdWord I)) aw3450 ByteArray.empty
        (cA, σ) k3450 C3450 := by
    have hnonzero :
        UInt256.isZero (flapperDealTicWord σ I) = UInt256.ofNat 0 :=
      isZero_eq_zero_of_ne hticNe
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3408_fallthrough_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3408_fallthrough_memory,
      hnonzero, flapperDealHashMem, flapperYankHashMem,
      flapperRuntimeBlocks.flapperRuntime_block_964_taken_memory,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3450raw
  exact ⟨aw3450, k3450, C3450, rd3450⟩

theorem flapperX_deal_tic_lt_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hticNe : flapperDealTicWord σ I ≠ UInt256.ofNat 0)
    (hticLt : (flapperDealTicWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3601)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealScratchMem (flapperDealIdWord I)
        (flapperDealHashMem (flapperDealIdWord I)))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3450, _, _, rd3450⟩ :=
    flapperX_deal_tic_ne_to_3450 (g := g) (sel := sel) hticNe h3408
  have hltWord : UInt256.lt (flapperDealTicWord σ I) (flapperDealTimestampWord I) =
      UInt256.ofNat 1 :=
    ult_one hticLt
  have hcond3450 :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperDealIdWord I).toByteArray.write 0
                        (flapperDealHashMem (flapperDealIdWord I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    have hcond : UInt256.lt (flapperDealTicWord σ I) (flapperDealTimestampWord I) ≠
        UInt256.ofNat 0 := by
      rw [hltWord]
      decide
    simpa [flapperDealTicWord, flapperDealPackedWord, flapperYankPackedWord,
      flapperDealTimestampWord, flapperYankMappingHashSlot, flapperYankBaseSlot,
      flapperDealHashMem, flapperYankHashMem_eq, twoWordHashMem, wordAt0Mem,
      wordAt32Mem, flapperUint48Mask, flapperUint48Shift160, u256_add_comm] using hcond
  obtain ⟨aw3529, k3529, C3529, rd3529raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3450_taken_packed
      (x0 := UInt256.ofNat 1) (x1 := flapperDealIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond3450 (by jump_dest) rd3450
  have rd3529 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3529)
        (UInt256.ofNat 1 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealScratchMem (flapperDealIdWord I)
          (flapperDealHashMem (flapperDealIdWord I)))
        aw3529 ByteArray.empty
        (cA, σ) k3529 C3529 := by
    have hltWordRaw :
        UInt256.lt (flapperDealTicWord σ I) (UInt256.ofNat I.header.timestamp) =
          UInt256.ofNat 1 := by
      simpa [flapperDealTimestampWord] using hltWord
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3450_taken_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3450_taken_memory,
      flapperDealTimestampWord, flapperDealScratchMem, flapperDealHashMem,
      flapperYankHashMem_eq,
      twoWordHashMem, wordAt0Mem, wordAt32Mem, hltWordRaw,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3529raw
  have rd3601 := flapperRuntimeBlocks.flapperRuntime_block_3529_taken
    (x0 := UInt256.ofNat 1)
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) rd3529
  exact ⟨aw3529, k3529 + 3, C3529 + 14, rd3601⟩

theorem flapperX_deal_tic_not_lt_to_3492 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hticNe : flapperDealTicWord σ I ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3492)
      (UInt256.ofNat 0 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealScratchMem (flapperDealIdWord I)
        (flapperDealHashMem (flapperDealIdWord I)))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3450, _, _, rd3450⟩ :=
    flapperX_deal_tic_ne_to_3450 (g := g) (sel := sel) hticNe h3408
  have hltWord : UInt256.lt (flapperDealTicWord σ I) (flapperDealTimestampWord I) =
      UInt256.ofNat 0 :=
    ult_zero (Nat.le_of_not_gt hticLt)
  have hcond3450 :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperDealIdWord I).toByteArray.write 0
                        (flapperDealHashMem (flapperDealIdWord I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp) = UInt256.ofNat 0 := by
    simpa [flapperDealTicWord, flapperDealPackedWord, flapperYankPackedWord,
      flapperDealTimestampWord, flapperYankMappingHashSlot, flapperYankBaseSlot,
      flapperDealHashMem, flapperYankHashMem_eq, twoWordHashMem, wordAt0Mem,
      wordAt32Mem, flapperUint48Mask, flapperUint48Shift160, u256_add_comm] using hltWord
  obtain ⟨aw3492, k3492, C3492, rd3492raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3450_fallthrough_packed
      (x0 := UInt256.ofNat 1) (x1 := flapperDealIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond3450 rd3450
  have rd3492 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3492)
        (UInt256.ofNat 0 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealScratchMem (flapperDealIdWord I)
          (flapperDealHashMem (flapperDealIdWord I)))
        aw3492 ByteArray.empty
        (cA, σ) k3492 C3492 := by
    have hltWordRaw :
        UInt256.lt (flapperDealTicWord σ I) (UInt256.ofNat I.header.timestamp) =
          UInt256.ofNat 0 := by
      simpa [flapperDealTimestampWord] using hltWord
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3450_fallthrough_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3450_fallthrough_memory,
      flapperDealTimestampWord, flapperDealScratchMem, flapperDealHashMem,
      flapperYankHashMem_eq,
      twoWordHashMem, wordAt0Mem, wordAt32Mem, hltWordRaw,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3492raw
  exact ⟨aw3492, k3492, C3492, rd3492⟩

theorem flapperX_deal_end_lt_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hticNe : flapperDealTicWord σ I ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (hendLt : (flapperDealEndWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3601)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealScratchMem (flapperDealIdWord I)
        (flapperDealScratchMem (flapperDealIdWord I)
          (flapperDealHashMem (flapperDealIdWord I))))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3492, _, _, rd3492⟩ :=
    flapperX_deal_tic_not_lt_to_3492 (g := g) (sel := sel) hticNe hticLt h3408
  have hltWord : UInt256.lt (flapperDealEndWord σ I) (flapperDealTimestampWord I) =
      UInt256.ofNat 1 :=
    ult_one hendLt
  obtain ⟨aw3529, k3529, C3529, rd3529raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3492_packed
      (x0 := UInt256.ofNat 0) (x1 := flapperDealIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      rd3492
  have rd3529 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3529)
        (UInt256.ofNat 1 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealScratchMem (flapperDealIdWord I)
          (flapperDealScratchMem (flapperDealIdWord I)
            (flapperDealHashMem (flapperDealIdWord I))))
        aw3529 ByteArray.empty
        (cA, σ) k3529 C3529 := by
    have hltWordRaw :
        UInt256.lt (flapperDealEndWord σ I) (UInt256.ofNat I.header.timestamp) =
          UInt256.ofNat 1 := by
      simpa [flapperDealTimestampWord] using hltWord
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3492_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3492_memory,
      flapperDealTimestampWord, flapperDealScratchMem, flapperDealHashMem,
      flapperYankHashMem_eq,
      twoWordHashMem, wordAt0Mem, wordAt32Mem, hltWordRaw,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3529raw
  have rd3601 := flapperRuntimeBlocks.flapperRuntime_block_3529_taken
    (x0 := UInt256.ofNat 1)
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) rd3529
  exact ⟨aw3529, k3529 + 3, C3529 + 14, rd3601⟩

theorem flapperX_deal_time_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hticNe : flapperDealTicWord σ I ≠ UInt256.ofNat 0)
    (hticLt :
      ¬ (flapperDealTicWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (hendLt :
      ¬ (flapperDealEndWord σ I).toNat < (flapperDealTimestampWord I).toNat)
    (h3408 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3408)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw3492, _, _, rd3492⟩ :=
    flapperX_deal_tic_not_lt_to_3492 (g := g) (sel := sel) hticNe hticLt h3408
  have hltWord : UInt256.lt (flapperDealEndWord σ I) (flapperDealTimestampWord I) =
      UInt256.ofNat 0 :=
    ult_zero (Nat.le_of_not_gt hendLt)
  obtain ⟨aw3529, k3529, C3529, rd3529raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3492_packed
      (x0 := UInt256.ofNat 0) (x1 := flapperDealIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      rd3492
  have rd3529 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3529)
        (UInt256.ofNat 0 :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        (flapperDealScratchMem (flapperDealIdWord I)
          (flapperDealScratchMem (flapperDealIdWord I)
            (flapperDealHashMem (flapperDealIdWord I))))
        aw3529 ByteArray.empty
        (cA, σ) k3529 C3529 := by
    have hltWordRaw :
        UInt256.lt (flapperDealEndWord σ I) (UInt256.ofNat I.header.timestamp) =
          UInt256.ofNat 0 := by
      simpa [flapperDealTimestampWord] using hltWord
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3492_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3492_memory,
      flapperDealTimestampWord, flapperDealScratchMem, flapperDealHashMem,
      flapperYankHashMem_eq,
      twoWordHashMem, wordAt0Mem, wordAt32Mem, hltWordRaw,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd3529raw
  have rd3534 := flapperRuntimeBlocks.flapperRuntime_block_3529_fallthrough
    (x0 := UInt256.ofNat 0)
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) rd3529
  exact flapperRuntimeBlocks.flapperRuntime_block_3534
    (R := flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3534

theorem flapperX_deal_move_setup {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hscratch : 96 ≤ (flapperDealScratchMem (flapperDealIdWord I) mem).size)
    (hread : (flapperDealScratchMem (flapperDealIdWord I) mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h3601 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3601)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3686)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 3140843579 :: flapperDealVatWord σ I ::
        flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealMoveCallMemFrom σ I
        (flapperDealScratchMem (flapperDealIdWord I) mem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3601, _, _, rd3601⟩ := h3601
  obtain ⟨aw3686, k3686, C3686, rd3686raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3601_packed
      (x0 := flapperDealIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      rd3601
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128 := by
    unfold memLoad
    rw [show (UInt256.ofNat 64).toNat = 64 by decide]
    rw [if_neg (by omega)]
    rw [hread, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  have hmem := flapperDealRuntimeMoveCallMem_eq_from σ I mem hbase
  have hstack := flapperDealRuntimeMoveCallStack_eq_from σ I sel mem hscratch hread
  exact ⟨aw3686, k3686, C3686, by simpa [hmem, hstack] using rd3686raw⟩

theorem flapperX_deal_vat_no_code_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperDealVatWord σ I) = UInt256.ofNat 0)
    (h3686 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3686)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 3140843579 :: flapperDealVatWord σ I ::
        flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw3686, _, _, rd3686⟩ := h3686
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperDealVatWord σ I))) =
        UInt256.ofNat 0 := by
    rw [hcodeSize]
    decide
  obtain ⟨_, _, _, rd3707⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3686_fallthrough_packed
      (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperDealVatWord σ I)
      (R := flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt rd3686
  exact flapperRuntimeBlocks.flapperRuntime_block_3707
    (R := flapperRuntimeBlocks.flapperRuntime_block_3686_fallthrough_stack
      (σ := σ) (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperDealVatWord σ I)
      (R := flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3686_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd3707

theorem flapperX_deal_vat_call_boundary {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperDealVatWord σ I) ≠ UInt256.ofNat 0)
    (h3686 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3686)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 3140843579 :: flapperDealVatWord σ I ::
        flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3714)
      (gasArg :: flapperDealVatWord σ I :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperDealMoveCallRest σ I sel)
      mem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw3686, _, _, rd3686⟩ := h3686
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperDealVatWord σ I))) ≠
        UInt256.ofNat 0 := by
    rw [isZero_eq_zero_of_ne hcodeSize]
    decide
  obtain ⟨aw3711, k3711, C3711, rd3711raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3686_taken_packed
      (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 128)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperDealVatWord σ I)
      (R := flapperDealLotWord σ I :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest) rd3686
  have rd3711 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3711)
        (UInt256.isZero (extCodeSizeWord σ (flapperDealVatWord σ I)) ::
          flapperDealVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperDealMoveCallRest σ I sel)
        mem aw3711 ByteArray.empty (cA, σ) k3711 C3711 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3686_taken_stack,
      flapperDealMoveCallRest,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
        decide,
      show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
      show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide]
      using rd3711raw
  have rd3713 := flapperRuntimeBlocks.flapperRuntime_block_3711
    (x0 := UInt256.isZero (extCodeSizeWord σ (flapperDealVatWord σ I)))
    (R := flapperDealVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperDealMoveCallRest σ I sel)
    (by simp only [flapperDealMoveCallRest, List.length_cons, List.length_nil]; omega)
    rd3711
  have rd3713' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3713)
        (flapperDealVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperDealMoveCallRest σ I sel)
        mem aw3711 ByteArray.empty (cA, σ) (k3711 + 2) (C3711 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3711_stack] using rd3713
  obtain ⟨gasArg, rd3714raw⟩ := RD.rawGas rd3713' (by native_decide)
    (by simp only [flapperDealMoveCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw3711, k3711 + 2 + 1, C3711 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_3711_stack,
    show UInt256.ofNat 3713 + ⟨1⟩ = UInt256.ofNat 3714 by native_decide]
    using rd3714raw

theorem flapperX_deal_vat_call_failure {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3715)
      (UInt256.ofNat 0 :: flapperDealMoveCallRest σ I sel) mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3722 := flapperRuntimeBlocks.flapperRuntime_block_3715_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperDealMoveCallRest σ I sel)
    (by simp only [flapperDealMoveCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_3722
    (R := flapperRuntimeBlocks.flapperRuntime_block_3715_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperDealMoveCallRest σ I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3715_fallthrough_stack,
        flapperDealMoveCallRest, List.length_cons, List.length_nil]
      omega)
    rd3722

theorem flapperX_deal_vat_call_success_to_burn_setup
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3715)
      (UInt256.ofNat 1 :: flapperDealMoveCallRest σ I sel) mem aw rdata world k C) :
    ∃ aw' k' C', RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3815)
      (flapperDealGemWord world.2 I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperDealBurnCallRest σ world.2 I sel)
      (flapperDealBurnCallMemFrom world.2 I mem)
      aw' rdata world k' C' := by
  cases world with
  | mk cAcur σcur =>
      have rd3731raw := flapperRuntimeBlocks.flapperRuntime_block_3715_taken
        (x0 := UInt256.ofNat 1) (R := flapperDealMoveCallRest σ I sel)
        (by simp only [flapperDealMoveCallRest, List.length_cons, List.length_nil]; omega)
        (by decide) (by jump_dest) h
      have rd3731 :
          RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3731)
            (UInt256.ofNat 0 :: flapperDealMoveCallRest σ I sel)
            mem aw rdata (cAcur, σcur) (k + 5) (C + 22) := by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_3715_taken_stack,
          flapperDealMoveCallRest] using rd3731raw
      obtain ⟨aw3815, k3815, C3815, rd3815raw⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_3731_packed
          (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
          (x2 := UInt256.ofNat 3140843579) (x3 := flapperDealVatWord σ I)
          (x4 := flapperDealLotWord σ I) (x5 := flapperDealIdWord I)
          (R := UInt256.ofNat 360 :: [sel])
          (by simp only [List.length_cons, List.length_nil]; omega)
          (by simpa [flapperDealMoveCallRest] using rd3731)
      have hbase : memLoad (UInt256.ofNat 64)
          (flapperDealScratchMem (flapperDealIdWord I) mem) = UInt256.ofNat 128 :=
        flapperDealScratchMem_mload64 (flapperDealIdWord I) mem hmem hread
      have hmemEq := flapperDealRuntimeBurnCallMem_eq_from σcur I mem hbase
      have hstackEq := flapperDealRuntimeBurnCallStack_eq_from σ σcur I sel mem hmem hread
      exact ⟨aw3815, k3815, C3815, by simpa [hmemEq, hstackEq] using rd3815raw⟩

theorem flapperX_deal_gem_no_code_revert {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperDealGemWord σ I) = UInt256.ofNat 0)
    (h3815 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3815)
      (flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperDealBurnCallRest σinit σ I sel)
      mem aw rdata (cAcur, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨aw3815, _, _, rd3815⟩ := h3815
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperDealGemWord σ I))) =
        UInt256.ofNat 0 := by
    rw [hcodeSize]
    decide
  obtain ⟨_, _, _, rd3824⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3815_fallthrough_packed
      (x0 := flapperDealGemWord σ I)
      (R := UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 68 ::
        UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperDealBurnCallRest σinit σ I sel)
      (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
      hcondExt rd3815
  exact flapperRuntimeBlocks.flapperRuntime_block_3824
    (R := flapperRuntimeBlocks.flapperRuntime_block_3815_fallthrough_stack
      (σ := σ) (x0 := flapperDealGemWord σ I)
      (R := UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 68 ::
        UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperDealBurnCallRest σinit σ I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3815_fallthrough_stack,
        flapperDealBurnCallRest, List.length_cons, List.length_nil]
      omega)
    rd3824

theorem flapperX_deal_gem_call_boundary {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperDealGemWord σ I) ≠ UInt256.ofNat 0)
    (h3815 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3815)
      (flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperDealBurnCallRest σinit σ I sel)
      mem aw rdata (cAcur, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3831)
      (gasArg :: flapperDealGemWord σ I :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 68 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperDealBurnCallRest σinit σ I sel)
      mem aw rdata (cAcur, σ) k C := by
  obtain ⟨aw3815, _, _, rd3815⟩ := h3815
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperDealGemWord σ I))) ≠
        UInt256.ofNat 0 := by
    rw [isZero_eq_zero_of_ne hcodeSize]
    decide
  obtain ⟨aw3828, k3828, C3828, rd3828raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3815_taken_packed
      (x0 := flapperDealGemWord σ I)
      (R := UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 68 ::
        UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperDealBurnCallRest σinit σ I sel)
      (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest) rd3815
  have rd3828 :
      RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3828)
        (UInt256.isZero (extCodeSizeWord σ (flapperDealGemWord σ I)) ::
          flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperDealBurnCallRest σinit σ I sel)
        mem aw3828 rdata (cAcur, σ) k3828 C3828 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3815_taken_stack,
      flapperDealBurnCallRest] using rd3828raw
  have rd3830 := flapperRuntimeBlocks.flapperRuntime_block_3828
    (x0 := UInt256.isZero (extCodeSizeWord σ (flapperDealGemWord σ I)))
    (R := flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperDealBurnCallRest σinit σ I sel)
    (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
    rd3828
  have rd3830' :
      RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3830)
        (flapperDealGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 68 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperDealBurnCallRest σinit σ I sel)
        mem aw3828 rdata (cAcur, σ) (k3828 + 2) (C3828 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3828_stack] using rd3830
  obtain ⟨gasArg, rd3831raw⟩ := RD.rawGas rd3830' (by native_decide)
    (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw3828, k3828 + 2 + 1, C3828 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_3828_stack,
    show UInt256.ofNat 3830 + ⟨1⟩ = UInt256.ofNat 3831 by native_decide]
    using rd3831raw

theorem flapperX_deal_gem_call_failure {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σburn : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3832)
      (UInt256.ofNat 0 :: flapperDealBurnCallRest σ σburn I sel)
      mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3839 := flapperRuntimeBlocks.flapperRuntime_block_3832_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperDealBurnCallRest σ σburn I sel)
    (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_3839
    (R := flapperRuntimeBlocks.flapperRuntime_block_3832_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperDealBurnCallRest σ σburn I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3832_fallthrough_stack,
        flapperDealBurnCallRest, List.length_cons, List.length_nil]
      omega)
    rd3839

theorem flapperX_deal_burn_call_success_to_sub
    {cA gh bl σinit σburn σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3832)
      (UInt256.ofNat 1 :: flapperDealBurnCallRest σinit σburn I sel)
      mem aw rdata world k C) :
    ∃ aw' k' C', RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4963)
      (flapperDealLotWord σinit I ::
        storageRead I.codeOwner (flapperDealDeletedAccountMap world.2 I) (UInt256.ofNat 9) ::
        UInt256.ofNat 3894 :: flapperDealLotWord σinit I ::
        flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperDealScratchMem (flapperDealIdWord I) mem)
      aw' rdata (world.1, flapperDealDeletedAccountMap world.2 I) k' C' := by
  cases world with
  | mk cAcur σcur =>
      have rd3848raw := flapperRuntimeBlocks.flapperRuntime_block_3832_taken
        (x0 := UInt256.ofNat 1) (R := flapperDealBurnCallRest σinit σburn I sel)
        (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
        (by decide) (by jump_dest) h
      have rd3848 :
          RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3848)
            (UInt256.ofNat 0 :: flapperDealBurnCallRest σinit σburn I sel)
            mem aw rdata (cAcur, σcur) (k + 5) (C + 22) := by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_3832_taken_stack,
          flapperDealBurnCallRest] using rd3848raw
      obtain ⟨aw4963, k4963, C4963, rd4963raw⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_3848_packed
          (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 196)
          (x2 := UInt256.ofNat 2646777772) (x3 := flapperDealGemWord σburn I)
          (x4 := flapperDealLotWord σinit I) (x5 := flapperDealIdWord I)
          (R := UInt256.ofNat 360 :: [sel])
          (by simp only [List.length_cons, List.length_nil]; omega)
          hperm (by jump_dest)
          (by simpa [flapperDealBurnCallRest] using rd3848)
      have hhashRaw :
          keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperDealIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
            flapperYankBaseSlot (flapperYankIdWord I) := by
        simpa [flapperDealIdWord,
          show (UInt256.ofNat 0).toNat = 0 by decide,
          show (UInt256.ofNat 32).toNat = 32 by decide] using
          flapperYankMappingHashSlot (flapperDealIdWord I) mem
      exact ⟨aw4963, k4963, C4963, by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_3848_stack,
          flapperRuntimeBlocks.flapperRuntime_block_3848_memory,
          flapperDealScratchMem, flapperDealDeletedAccountMap,
          flapperYankDeletedAccountMap, flapperDealBaseSlot, hhashRaw,
          u256_add_comm,
          show (UInt256.ofNat 0).toNat = 0 by decide,
          show (UInt256.ofNat 32).toNat = 32 by decide] using rd4963raw⟩

theorem flapperX_deal_sub_underflow_revert {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    {lot fill : UInt256}
    (hbad : fill.toNat < lot.toNat)
    (h4963 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4963)
      (lot :: fill :: UInt256.ofNat 3894 :: lot :: flapperDealIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw rdata (cAcur, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨aw4963, _, _, rd4963⟩ := h4963
  have hsubNat :
      (UInt256.sub fill lot).toNat = UInt256.size + fill.toNat - lot.toNat :=
    usub_toNat_underflow (a := fill) (b := lot) hbad
  have hgt : UInt256.gt (UInt256.sub fill lot) fill = UInt256.ofNat 1 := by
    show UInt256.fromBool (decide (UInt256.sub fill lot > fill)) = UInt256.ofNat 1
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub fill lot).toNat > fill.toNat
      rw [hsubNat]
      have hlot : lot.toNat < UInt256.size := lot.val.isLt
      omega
  have hcond :
      UInt256.isZero (UInt256.gt (UInt256.sub fill lot) fill) = UInt256.ofNat 0 := by
    rw [hgt]
    decide
  have rd4975 := flapperRuntimeBlocks.flapperRuntime_block_4963_fallthrough
    (x0 := lot) (x1 := fill)
    (R := UInt256.ofNat 3894 :: lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd4963
  exact flapperRuntimeBlocks.flapperRuntime_block_4975
    (R := flapperRuntimeBlocks.flapperRuntime_block_4963_fallthrough_stack
      (x0 := lot) (x1 := fill)
      (R := UInt256.ofNat 3894 :: lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_4963_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd4975

theorem flapperX_deal_sub_ok_success {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    {lot fill : UInt256}
    (hperm : I.perm = true)
    (hok : lot.toNat ≤ fill.toNat)
    (h4963 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4963)
      (lot :: fill :: UInt256.ofNat 3894 :: lot :: flapperDealIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw rdata (cAcur, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cAcur, storageWrite I.codeOwner σ (UInt256.ofNat 9) (UInt256.sub fill lot))
      ByteArray.empty := by
  obtain ⟨aw4963, _, _, rd4963⟩ := h4963
  have hsubNat : (UInt256.sub fill lot).toNat = fill.toNat - lot.toNat :=
    usub_toNat (a := fill) (b := lot) hok
  have hgt : UInt256.gt (UInt256.sub fill lot) fill = UInt256.ofNat 0 :=
    ugt_zero (by rw [hsubNat]; omega)
  have hcond :
      UInt256.isZero (UInt256.gt (UInt256.sub fill lot) fill) ≠ UInt256.ofNat 0 := by
    rw [hgt]
    decide
  obtain ⟨aw4930, k4930, C4930, rd4930raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4963_taken_packed
      (x0 := lot) (x1 := fill)
      (R := UInt256.ofNat 3894 :: lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond (by jump_dest) rd4963
  have rd4930 :
      RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4930)
        (UInt256.sub fill lot :: lot :: fill :: UInt256.ofNat 3894 ::
          lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        mem aw4930 rdata (cAcur, σ) k4930 C4930 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4963_taken_stack] using rd4930raw
  obtain ⟨aw3894, k3894, C3894, rd3894raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4930_packed
      (x0 := UInt256.sub fill lot) (x1 := lot) (x2 := fill)
      (x3 := UInt256.ofNat 3894)
      (R := lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd4930
  have rd3894 :
      RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 3894)
        (UInt256.sub fill lot :: lot :: flapperDealIdWord I :: UInt256.ofNat 360 :: [sel])
        mem aw3894 rdata (cAcur, σ) k3894 C3894 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4930_stack] using rd3894raw
  obtain ⟨aw360, k360, C360, rd360⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3894_packed
      (x0 := UInt256.sub fill lot) (x1 := lot) (x2 := flapperDealIdWord I)
      (x3 := UInt256.ofNat 360) (R := [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm (by jump_dest) rd3894
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel]) (by simp only [List.length_cons, List.length_nil]; omega) rd360

set_option maxHeartbeats 1000000 in
theorem flapperDealExternalTailProgress
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {mem3601 : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hperm : I.perm = true)
    (hmoveBaseSize :
      96 ≤ (flapperDealScratchMem (flapperDealIdWord I) mem3601).size)
    (hmoveBaseRead :
      (flapperDealScratchMem (flapperDealIdWord I) mem3601).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat 128))
    (h3601 : ∃ aw k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 3601)
      (flapperDealIdWord I :: UInt256.ofNat 360 :: [flapperSelWord I])
      mem3601 aw ByteArray.empty (cA, σ_evm) k C) :
    BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      config
      { contract := contract,
        locals := flapperDealLocalsLot (flapperDealIdWord I)
          (flapperDealLotWord σ_evm I) }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
        [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
       checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
        [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet" ++
       [ .delete (bidRef (.var "id")),
         .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
         .assign .storage fillRef (.var "fillNew") ])
      (runtimeExit (.abi dealTransition.returnType)) := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let id := flapperDealIdWord I
  let lot := flapperDealLotWord σ_evm I
  let frameLot : Frame := { contract := contract, locals := flapperDealLocalsLot id lot }
  let moveBase := flapperDealScratchMem id mem3601
  let moveMem := flapperDealMoveCallMemFrom σ_evm I moveBase
  have hStateInit :
      CallStateRel
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        I (cA, σ_evm) evmSolm := by
    simpa [evmSolm] using
      (CallStateRel.initState
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
        (σ_solm := σ_solm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
        (A := A) (I := I) hAccounts)
  have hPackedLoadEq :
      flapperDealPackedWordOfState evmSolm id =
        storageRead I.codeOwner σ_evm (flapperDealPackedSlot id) := by
    simpa [flapperDealPackedWordOfState, flapperYankPackedWordOfState,
      evmSolm, id] using
      flapperDealStorageLoad_eq_of_stateRel (g := g) hStateInit
        (flapperDealPackedSlot id)
  have hGuyWordSolm :
      flapperDealGuyWordOfState evmSolm id = flapperDealGuyWord σ_evm I := by
    simp [flapperDealGuyWordOfState, flapperYankGuyWordOfState,
      flapperDealGuyWord, flapperYankGuyWord, flapperYankPackedWord,
      flapperYankPackedSlot, flapperDealPackedSlot, hPackedLoadEq, id,
      flapperDealIdWord, u256_add_comm]
  have hVatLoadEq :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (UInt256.ofNat 2) =
        storageRead I.codeOwner σ_evm (UInt256.ofNat 2) := by
    simpa [evmSolm] using
      flapperDealStorageLoad_eq_of_stateRel (g := g) hStateInit (UInt256.ofNat 2)
  have hVatWordSolm :
      flapperDealVatWordOfState evmSolm = flapperDealVatWord σ_evm I := by
    simp [flapperDealVatWordOfState, flapperKickVatWordOfState,
      flapperDealVatWord, hVatLoadEq, flapperAddressMask_eq_solcAddrMask]
  have h3686 := flapperX_deal_move_setup
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
    (mem := mem3601) hmoveBaseSize hmoveBaseRead h3601
  by_cases hVatCodeSize :
      extCodeSizeWord σ_evm (flapperDealVatWord σ_evm I) = UInt256.ofNat 0
  · have hVatCodeSizeSolm :
        extCodeSizeWord evmSolm.accountMap (flapperDealVatWordOfState evmSolm) =
          UInt256.ofNat 0 := by
      have hmapCode := extCodeSizeWord_accountMapEquiv hStateInit.accounts
        (flapperDealVatWord σ_evm I)
      exact (by simpa [hVatWordSolm] using hmapCode.symm.trans hVatCodeSize)
    have hguardFalse :
        evalExpr? config frameLot evmSolm
          (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
            .ok (.bool false) := by
      simpa [frameLot, id, lot] using
        flapperDealVatExtGuard_false evmSolm id lot hVatCodeSizeSolm
    exact BlockProgress.ofRDrev
      (hsource := by
        simpa [checkedExternalCallStmts, frameLot] using
          (ExecBlock.consRevert (ExecStmt.requireFalse hguardFalse) :
            ExecBlock config frameLot evmSolm
              ((.require
                (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0))) ::
                (.externalCall (.storage vatRef) "move" (.intLit 0)
                  [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"]
                  "_moveRet") ::
                checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
                  [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet" ++
                [ .delete (bidRef (.var "id")),
                  .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
                  .assign .storage fillRef (.var "fillNew") ])
              .reverted))
      (flapperX_deal_vat_no_code_revert
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (sel := flapperSelWord I) hVatCodeSize h3686)
  · have hVatCodeSizeSolmNe :
        extCodeSizeWord evmSolm.accountMap (flapperDealVatWordOfState evmSolm) ≠
          UInt256.ofNat 0 := by
      intro hzero
      apply hVatCodeSize
      have hmapCode := extCodeSizeWord_accountMapEquiv hStateInit.accounts
        (flapperDealVatWord σ_evm I)
      have hzeroVat :
          extCodeSizeWord evmSolm.accountMap (flapperDealVatWord σ_evm I) =
            UInt256.ofNat 0 := by
        simpa [hVatWordSolm] using hzero
      exact hmapCode.trans hzeroVat
    have hguardTrue :
        evalExpr? config frameLot evmSolm
          (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [frameLot, id, lot] using
        flapperDealVatExtGuard_true evmSolm id lot hVatCodeSizeSolmNe
    have htailExternal :
        BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          config frameLot evmSolm
          [ .externalCall (.storage vatRef) "move" (.intLit 0)
              [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"]
              "_moveRet",
            .require (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)),
            .externalCall (.storage gemRef) "burn" (.intLit 0)
              [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet",
            .delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew") ]
          (runtimeExit (.abi dealTransition.returnType)) := by
      obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
        flapperX_deal_vat_call_boundary
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := flapperSelWord I) hVatCodeSize h3686
      refine BlockProgress.externalCall
        (h := rdCall) (hState := hStateInit)
        (receiver := .storage vatRef) (eth := .intLit 0)
        (args := [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"])
        (argVals := [.address I.codeOwner,
          .address (AccountAddress.ofNat (flapperDealGuyWord σ_evm I).toNat),
          .int (Int.ofNat lot.toNat)])
        (tgt := AccountAddress.ofNat (flapperDealVatWord σ_evm I).toNat)
        (name := "move") (retVar := "_moveRet") (value := 0)
        (stmts :=
          [ .require (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)),
            .externalCall (.storage gemRef) "burn" (.intLit 0)
              [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet",
            .delete (bidRef (.var "id")),
            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
            .assign .storage fillRef (.var "fillNew") ])
        ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
        (by simp only [flapperDealMoveCallRest, List.length_cons, List.length_nil]; omega)
        (by exact True.intro) ?_ ?_
      · have hrecv := flapperDealVat_eval_lot evmSolm id lot
        simpa [frameLot, hVatWordSolm] using hrecv
      · simp [evalExpr?, pure]
      · have hargs := flapperDealMoveArgs_eval evmSolm id lot
        rw [hGuyWordSolm] at hargs
        simpa [frameLot, evmSolm, initState, lot] using hargs
      · exact wordOfInt_zero.symm
      · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        apply Fin.ext
        simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
          AccountAddress.size]
      · simpa [
          moveBase, moveMem,
          show (UInt256.ofNat 128).toNat = 128 by decide,
          show (UInt256.ofNat 100).toNat = 100 by decide] using
          flapperDealMoveEncodeFrom_eq σ_evm I moveBase
      · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
        have hdecodeOut : config.externalABI.decode? "move" out = some [] := by
          simp [config, externalABI, decodeVoid?]
        rw [hdecodeOut]
        cases world' with
        | mk cAmove σmove =>
            let frameAfterMove : Frame :=
              { contract := contract, locals := flapperDealLocalsAfterMove id lot }
            let burnMem := flapperDealBurnCallMemFrom σmove I moveMem
            have hmin0 :
                (min (UInt256.ofNat 0) (UInt256.ofNat out.size)).toNat = 0 := by
              simpa [show (UInt256.ofNat 0).toNat = 0 by decide] using
                callCopyLength_toNat out (UInt256.ofNat 0) hsizeOut
            have h3715 :
                RD flapperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (UInt256.ofNat 3715)
                  (UInt256.ofNat 1 :: flapperDealMoveCallRest σ_evm I (flapperSelWord I))
                  moveMem cur.aw out (cAmove, σmove) k' C' := by
              simpa [callCursor, hmin0, byteArray_write_len_zero, moveMem,
                show UInt256.ofNat 3714 + ⟨1⟩ = UInt256.ofNat 3715 by native_decide]
                using rdSucc
            have hmoveMemSize : 96 ≤ moveMem.size := by
              have hsz := flapperDealMoveCallMemFrom_size_ge_228 σ_evm I moveBase
              exact le_trans (show 96 ≤ 228 by decide) (by simpa [moveMem] using hsz)
            have hmoveMemRead :
                moveMem.readWithPadding 64 32 =
                  UInt256.toByteArray (UInt256.ofNat 128) := by
              simpa [moveMem, moveBase] using
                flapperDealMoveCallMemFrom_read64 σ_evm I moveBase
                  hmoveBaseSize hmoveBaseRead
            have h3815 := flapperX_deal_vat_call_success_to_burn_setup
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (sel := flapperSelWord I) hmoveMemSize hmoveMemRead h3715
            have hGemLoadEq :
                Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
                    (UInt256.ofNat 3) =
                  storageRead I.codeOwner σmove (UInt256.ofNat 3) := by
              simpa using
                flapperDealStorageLoad_eq_of_stateRel (g := g) hState'
                  (UInt256.ofNat 3)
            have hGemWordSolm :
                flapperDealGemWordOfState evm' = flapperDealGemWord σmove I := by
              simp [flapperDealGemWordOfState, flapperYankGemWordOfState,
                flapperDealGemWord, flapperYankGemWord, hGemLoadEq]
            have hBidLoadEq :
                flapperDealBidWordOfState evm' id = flapperDealBidWord σmove I := by
              have hload := flapperDealStorageLoad_eq_of_stateRel (g := g) hState'
                (flapperDealBaseSlot id)
              simpa [flapperDealBidWordOfState, flapperYankBidWordOfState,
                flapperDealBidWord, flapperYankBidWord, flapperDealBaseSlot,
                id] using hload
            by_cases hGemCodeSize :
                extCodeSizeWord σmove (flapperDealGemWord σmove I) = UInt256.ofNat 0
            · have hGemCodeSizeSolm :
                  extCodeSizeWord evm'.accountMap (flapperDealGemWordOfState evm') =
                    UInt256.ofNat 0 := by
                have hmapCode := extCodeSizeWord_accountMapEquiv hState'.accounts
                  (flapperDealGemWord σmove I)
                exact (by simpa [hGemWordSolm] using hmapCode.symm.trans hGemCodeSize)
              have hguardFalse :
                  evalExpr? config frameAfterMove evm'
                    (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
                      .ok (.bool false) := by
                simpa [frameAfterMove] using
                  flapperDealGemExtGuard_false evm' id lot hGemCodeSizeSolm
              exact BlockProgress.ofRDrev
                (hsource := by
                  simpa [checkedExternalCallStmts, frameAfterMove] using
                    (ExecBlock.consRevert (ExecStmt.requireFalse hguardFalse) :
                      ExecBlock config frameAfterMove evm'
                        ((.require
                          (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0))) ::
                          (.externalCall (.storage gemRef) "burn" (.intLit 0)
                            [thisAddr, .storage (bidsF (.var "id") "bid")]
                            "_burnRet") ::
                          [ .delete (bidRef (.var "id")),
                            .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
                            .assign .storage fillRef (.var "fillNew") ])
                        .reverted))
                (flapperX_deal_gem_no_code_revert
                  (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
                  (σ := σmove) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                  hGemCodeSize h3815)
            · have hGemCodeSizeSolmNe :
                  extCodeSizeWord evm'.accountMap (flapperDealGemWordOfState evm') ≠
                    UInt256.ofNat 0 := by
                intro hzero
                apply hGemCodeSize
                have hmapCode := extCodeSizeWord_accountMapEquiv hState'.accounts
                  (flapperDealGemWord σmove I)
                have hzeroGem :
                    extCodeSizeWord evm'.accountMap (flapperDealGemWord σmove I) =
                      UInt256.ofNat 0 := by
                  simpa [hGemWordSolm] using hzero
                exact hmapCode.trans hzeroGem
              have hguardTrueGem :
                  evalExpr? config frameAfterMove evm'
                    (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
                      .ok (.bool true) := by
                simpa [frameAfterMove] using
                  flapperDealGemExtGuard_true evm' id lot hGemCodeSizeSolmNe
              have htailExternalGem :
                  BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config frameAfterMove evm'
                    [ .externalCall (.storage gemRef) "burn" (.intLit 0)
                        [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet",
                      .delete (bidRef (.var "id")),
                      .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
                      .assign .storage fillRef (.var "fillNew") ]
                    (runtimeExit (.abi dealTransition.returnType)) := by
                obtain ⟨gasArg2, awCall2, kCall2, CCall2, rdCall2⟩ :=
                  flapperX_deal_gem_call_boundary
                    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
                    (σ := σmove) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                    hGemCodeSize h3815
                refine BlockProgress.externalCall
                  (h := rdCall2) (hState := hState')
                  (receiver := .storage gemRef) (eth := .intLit 0)
                  (args := [thisAddr, .storage (bidsF (.var "id") "bid")])
                  (argVals := [.address I.codeOwner,
                    .int (Int.ofNat (flapperDealBidWord σmove I).toNat)])
                  (tgt := AccountAddress.ofNat (flapperDealGemWord σmove I).toNat)
                  (name := "burn") (retVar := "_burnRet") (value := 0)
                  (stmts :=
                    [ .delete (bidRef (.var "id")),
                      .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
                      .assign .storage fillRef (.var "fillNew") ])
                  ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
                  (by simp only [flapperDealBurnCallRest, List.length_cons, List.length_nil]; omega)
                  (by exact True.intro) ?_ ?_
                · have hrecv := flapperDealGem_eval_afterMove evm' id lot
                  simpa [frameAfterMove, hGemWordSolm] using hrecv
                · simp [evalExpr?, pure]
                · have hargs := flapperDealBurnArgs_eval evm' id lot
                  have howner : evm'.executionEnv.codeOwner = I.codeOwner := by
                    rw [hState'.env]
                  rw [hBidLoadEq] at hargs
                  simpa [frameAfterMove, howner] using hargs
                · exact wordOfInt_zero.symm
                · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                  apply Fin.ext
                  simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
                    AccountAddress.size]
                · simpa [burnMem,
                    show (UInt256.ofNat 128).toNat = 128 by decide,
                    show (UInt256.ofNat 68).toNat = 68 by decide] using
                    flapperDealBurnEncodeFrom_eq σmove I moveMem
                · intro out2 evm'' world2 k2 C2 cur2 rdSucc2 hcall2 hState'' hsizeOut2
                  have hdecodeOut2 : config.externalABI.decode? "burn" out2 = some [] := by
                    simp [config, externalABI, decodeVoid?]
                  rw [hdecodeOut2]
                  cases world2 with
                  | mk cAburn σburn =>
                      let frameAfterBurn : Frame :=
                        { contract := contract, locals := flapperDealLocalsAfterBurn id lot }
                      let fill :=
                        storageRead I.codeOwner (flapperDealDeletedAccountMap σburn I)
                          (UInt256.ofNat 9)
                      have hmin02 :
                          (min (UInt256.ofNat 0) (UInt256.ofNat out2.size)).toNat = 0 := by
                        simpa [show (UInt256.ofNat 0).toNat = 0 by decide] using
                          callCopyLength_toNat out2 (UInt256.ofNat 0) hsizeOut2
                      have h3832 :
                          RD flapperBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            (UInt256.ofNat 3832)
                            (UInt256.ofNat 1 ::
                              flapperDealBurnCallRest σ_evm σmove I (flapperSelWord I))
                            burnMem cur2.aw out2 (cAburn, σburn) k2 C2 := by
                        simpa [callCursor, hmin02, byteArray_write_len_zero, burnMem,
                          show UInt256.ofNat 3831 + ⟨1⟩ = UInt256.ofNat 3832 by native_decide]
                          using rdSucc2
                      have h4963 := flapperX_deal_burn_call_success_to_sub
                        (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
                        (σburn := σmove) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                        hperm h3832
                      have hFillLoadEq :
                          flapperDealFillWordOfState
                              (flapperDealDeletedState evm'' id) = fill := by
                        simpa [id, fill] using
                          flapperDealDeletedFillLoad_eq
                            (σ := σburn) (evm := evm'') (I := I)
                            hState''.accounts hState''.env
                      have hFillNewEq :
                          flapperDealFillNewWordOfState evm'' id lot =
                            UInt256.sub fill lot := by
                        simp [flapperDealFillNewWordOfState, hFillLoadEq]
                      by_cases hok : lot.toNat ≤ fill.toNat
                      · have hSubOk :
                            (flapperDealFillNewWordOfState evm'' id lot).toNat ≤
                              (flapperDealFillWordOfState
                                (flapperDealDeletedState evm'' id)).toNat := by
                          have hsubNat :
                              (UInt256.sub fill lot).toNat = fill.toNat - lot.toNat :=
                            usub_toNat (a := fill) (b := lot) hok
                          rw [hFillNewEq, hFillLoadEq, hsubNat]
                          omega
                        have htailSource := flapperDealTailReturns evm'' id lot hSubOk
                        have hret : RDret flapperBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            (cAburn, flapperDealAfterFillWorldFrom σburn I lot)
                            ByteArray.empty := by
                          have hretRaw := flapperX_deal_sub_ok_success
                            (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
                            (σ := flapperDealDeletedAccountMap σburn I)
                            (σ₀ := σ₀) (A := A) (I := I)
                            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                            (mem := flapperDealScratchMem id burnMem) (rdata := out2)
                            (lot := lot) (fill := fill) hperm hok
                            (by simpa [id, lot, fill] using h4963)
                          simpa [flapperDealAfterFillWorldFrom, fill] using hretRaw
                        exact BlockProgress.ofRDret
                          (frame' :=
                            flapperDealAfterSubFrame id lot
                              (flapperDealFillNewWordOfState evm'' id lot))
                          (evm' := flapperDealAfterFillState evm'' id lot)
                          (value := none)
                          (hsource := by
                            simpa [frameAfterBurn] using htailSource)
                          hret
                          (by
                            rw [flapperDealAfterFillState_createdAccounts]
                            exact hState''.created.symm)
                          (by
                            have hacc :=
                              flapperDealAfterFillWorldFrom_accountMapEquiv
                                (σ := σburn) (evm := evm'') (I := I)
                                hState''.accounts hState''.env lot
                            simpa [id, fill] using hacc)
                          (by simpa [dealTransition] using abiVoidFallthrough)
                      · have hfillLt : fill.toNat < lot.toNat :=
                          Nat.lt_of_not_ge hok
                        have hSubBad :
                            ¬ (flapperDealFillNewWordOfState evm'' id lot).toNat ≤
                              (flapperDealFillWordOfState
                                (flapperDealDeletedState evm'' id)).toNat := by
                          intro hle
                          have hsubNat :
                              (UInt256.sub fill lot).toNat =
                                UInt256.size + fill.toNat - lot.toNat :=
                            usub_toNat_underflow (a := fill) (b := lot) hfillLt
                          have hlarge : fill.toNat < (UInt256.sub fill lot).toNat := by
                            rw [hsubNat]
                            have hlot : lot.toNat < UInt256.size := lot.val.isLt
                            omega
                          exact (not_le_of_gt hlarge) (by
                            simpa [hFillNewEq, hFillLoadEq] using hle)
                        have htailSource := flapperDealTailRevertsSub evm'' id lot hSubBad
                        have hrev := flapperX_deal_sub_underflow_revert
                          (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
                          (σ := flapperDealDeletedAccountMap σburn I)
                          (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                          (mem := flapperDealScratchMem id burnMem) (rdata := out2)
                          (lot := lot) (fill := fill) hfillLt
                          (by simpa [id, lot, fill] using h4963)
                        exact BlockProgress.ofRDrev
                          (hsource := by
                            simpa [frameAfterBurn] using htailSource)
                          hrev
                · intro out2 world2 k2 C2 cur2 rdFail2
                  exact flapperX_deal_gem_call_failure
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                    (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                    (σburn := σmove) (h := by
                      simpa [callCursor,
                        show UInt256.ofNat 3831 + ⟨1⟩ = UInt256.ofNat 3832 by native_decide]
                        using rdFail2)
              have htailGem :
                  BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config frameAfterMove evm'
                    (checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
                      [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet" ++
                      [ .delete (bidRef (.var "id")),
                        .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
                        .assign .storage fillRef (.var "fillNew") ])
                    (runtimeExit (.abi dealTransition.returnType)) := by
                simpa [checkedExternalCallStmts] using
                  BlockProgress.cons (ExecStmt.requireTrue hguardTrueGem) htailExternalGem
              simpa [frameAfterMove, flapperDealLocalsAfterMove] using htailGem
      · intro out world' k' C' cur rdFail
        exact flapperX_deal_vat_call_failure
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (sel := flapperSelWord I) (h := by
            simpa [callCursor,
              show UInt256.ofNat 3714 + ⟨1⟩ = UInt256.ofNat 3715 by native_decide]
              using rdFail)
    have htail :
        BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          config frameLot evmSolm
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "guy"), .var "lot"] "_moveRet" ++
           checkedExternalCallStmts (.storage gemRef) "burn" (.intLit 0)
            [thisAddr, .storage (bidsF (.var "id") "bid")] "_burnRet" ++
           [ .delete (bidRef (.var "id")),
             .internalCall "sub" [.storage fillRef, .var "lot"] "fillNew",
             .assign .storage fillRef (.var "fillNew") ])
          (runtimeExit (.abi dealTransition.returnType)) := by
      simpa [checkedExternalCallStmts] using
        BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
    simpa [frameLot, evmSolm, id, lot] using htail

set_option maxHeartbeats 1000000 in
theorem flapperDealBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 3))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨767⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hselLit :
      ((⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) == I.calldata.extract 0 4) =
        true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 3) (by decide) hsel
  have hd : dispatchMsg contract I.calldata = some dealTransition :=
    flapperDispatch_deal hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_deal_ok (I := I) hsz36
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let id := flapperDealIdWord I
    let lot := flapperDealLotWord σ_evm I
    have hdecode := flapperX_deal_decode_ok
      (g := Sat256.ofUInt256 g) hsize hsz36 hreach
    have hloadLiveEq :
        flapperDealLiveWordOfState evmSolm =
          storageRead I.codeOwner σ_evm (UInt256.ofNat 7) := by
      simpa [flapperDealLiveWordOfState, evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 7)
    by_cases hliveEvm : storageRead I.codeOwner σ_evm (UInt256.ofNat 7) = UInt256.ofNat 1
    · have h3408 := flapperX_deal_live_ok
        (g := Sat256.ofUInt256 g) hliveEvm hdecode
      have hliveSolm :
          flapperDealLiveWordOfState evmSolm = UInt256.ofNat 1 := by
        rw [hloadLiveEq, hliveEvm]
      have hPackedLoadEq :
          flapperDealPackedWordOfState evmSolm id =
            storageRead I.codeOwner σ_evm (flapperDealPackedSlot id) := by
        simpa [flapperDealPackedWordOfState, flapperYankPackedWordOfState,
          evmSolm, initState, id] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperDealPackedSlot id)
      have hTicWordSolm :
          flapperDealTicWordOfState evmSolm id = flapperDealTicWord σ_evm I := by
        simp [flapperDealTicWordOfState, flapperDealTicWord,
          flapperDealPackedWordOfState, flapperDealPackedWord,
          flapperYankPackedWord, flapperYankPackedSlot, flapperDealPackedSlot,
          hPackedLoadEq, id, flapperDealIdWord, u256_add_comm, u256_land_comm]
      have hEndWordSolm :
          flapperDealEndWordOfState evmSolm id = flapperDealEndWord σ_evm I := by
        simp [flapperDealEndWordOfState, flapperDealEndWord,
          flapperDealPackedWordOfState, flapperDealPackedWord,
          flapperYankPackedWord, flapperYankPackedSlot, flapperDealPackedSlot,
          hPackedLoadEq, id, flapperDealIdWord, u256_add_comm, u256_land_comm]
      have hTimestampSolm :
          flapperDealTimestampWordOfState evmSolm = flapperDealTimestampWord I := by
        simp [flapperDealTimestampWordOfState, flapperDealTimestampWord, evmSolm, initState]
      have hLotWordSolm :
          flapperDealLotWordOfState evmSolm id = flapperDealLotWord σ_evm I := by
        simpa [flapperDealLotWordOfState, flapperDealLotWord, evmSolm, initState,
          id] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperDealBaseSlot id + UInt256.ofNat 1)
      have hlotSolm : lot = flapperDealLotWordOfState evmSolm id := by
        simpa [lot] using hLotWordSolm.symm
      by_cases hticZero : flapperDealTicWord σ_evm I = UInt256.ofNat 0
      · have hticSolm :
            flapperDealTicWordOfState evmSolm id = UInt256.ofNat 0 := by
          rw [hTicWordSolm, hticZero]
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperDealLocals id)
              dealTransition.body .reverted := by
          simpa [evmSolm, id] using
            flapperDealBodyRevertsTimingTicZero evmSolm id
              (by simp only [evmSolm, initState]; exact hwv)
              hliveSolm hticSolm
        exact (flapperX_deal_tic_zero_revert
            (g := Sat256.ofUInt256 g) hticZero h3408)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hticSolmNe :
            flapperDealTicWordOfState evmSolm id ≠ UInt256.ofNat 0 := by
          intro hzero
          exact hticZero (by rw [← hTicWordSolm]; exact hzero)
        by_cases hticLt :
            (flapperDealTicWord σ_evm I).toNat <
              (flapperDealTimestampWord I).toNat
        · have hticLtSolm :
              (flapperDealTicWordOfState evmSolm id).toNat <
                (flapperDealTimestampWordOfState evmSolm).toNat := by
            simpa [hTicWordSolm, hTimestampSolm] using hticLt
          have hpref :
              ExecBlock config { contract := contract, locals := flapperDealLocals id }
                evmSolm
                (nonpayable ++
                  [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                    .require
                      (.binary .and
                        (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                        (.binary .or
                          (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))),
                    .letDecl "lot" (some uint256) (.storage (bidsF (.var "id") "lot")) ])
                (.ok { contract := contract, locals := flapperDealLocalsLot id lot } evmSolm) := by
            simpa [evmSolm, id, lot] using
              flapperDealPrefixOk_tic evmSolm id lot
                (by simp only [evmSolm, initState]; exact hwv)
                hliveSolm hticSolmNe hticLtSolm hlotSolm
          have h3601 := flapperX_deal_tic_lt_ok
            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
            hticZero hticLt h3408
          have hHashSize := flapperDealHashMem_size_ge_96 id
          have hHashRead := flapperDealHashMem_read64 id
          have hTimingSize :=
            flapperDealScratchMem_size_ge_96 id (flapperDealHashMem id)
              hHashSize
          have hTimingRead :=
            flapperDealScratchMem_read64 id (flapperDealHashMem id)
              hHashSize hHashRead
          have hMoveBaseSize :
              96 ≤
                (flapperDealScratchMem id
                  (flapperDealScratchMem id (flapperDealHashMem id))).size :=
            flapperDealScratchMem_size_ge_96 id
              (flapperDealScratchMem id (flapperDealHashMem id)) hTimingSize
          have hMoveBaseRead :
              (flapperDealScratchMem id
                  (flapperDealScratchMem id (flapperDealHashMem id))).readWithPadding 64 32 =
                UInt256.toByteArray (UInt256.ofNat 128) :=
            flapperDealScratchMem_read64 id
              (flapperDealScratchMem id (flapperDealHashMem id)) hTimingSize hTimingRead
          have htail := flapperDealExternalTailProgress
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (mem3601 := flapperDealScratchMem id (flapperDealHashMem id))
            hAccounts hperm
            (by simpa [id] using hMoveBaseSize)
            (by simpa [id] using hMoveBaseRead)
            (by simpa [id] using h3601)
          have hprogress :
              BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := flapperDealLocals id }
                evmSolm dealTransition.body
                (runtimeExit (.abi dealTransition.returnType)) := by
            have hp := BlockProgress.prepend hpref htail
            simpa [dealTransition, nonpayable, checkedExternalCallStmts,
              evmSolm, id, lot] using hp
          exact hprogress.toRuntimeEquivalenceFor hcode
            (fun result hfunc => by
              exact solmExec.intro (flapperSelectorDispatch_deal hselLit) rfl hdec
                (by simp [evmSolm, initState, Sat256.ofUInt256, Sat256.toUInt256])
                hfunc)
            (by intro result endpoint h; exact h)
        · have hticLtSolmNot :
              ¬ (flapperDealTicWordOfState evmSolm id).toNat <
                (flapperDealTimestampWordOfState evmSolm).toNat := by
            intro hlt
            exact hticLt (by simpa [hTicWordSolm, hTimestampSolm] using hlt)
          by_cases hendLt :
              (flapperDealEndWord σ_evm I).toNat <
                (flapperDealTimestampWord I).toNat
          · have hendLtSolm :
                (flapperDealEndWordOfState evmSolm id).toNat <
                  (flapperDealTimestampWordOfState evmSolm).toNat := by
              simpa [hEndWordSolm, hTimestampSolm] using hendLt
            have hpref :
                ExecBlock config { contract := contract, locals := flapperDealLocals id }
                  evmSolm
                  (nonpayable ++
                    [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                      .require
                        (.binary .and
                          (.binary .ne (.storage (bidsF (.var "id") "tic")) (.intLit 0))
                          (.binary .or
                            (.binary .lt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
                            (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)))),
                      .letDecl "lot" (some uint256) (.storage (bidsF (.var "id") "lot")) ])
                  (.ok { contract := contract, locals := flapperDealLocalsLot id lot } evmSolm) := by
              simpa [evmSolm, id, lot] using
                flapperDealPrefixOk_end evmSolm id lot
                  (by simp only [evmSolm, initState]; exact hwv)
                  hliveSolm hticSolmNe hticLtSolmNot hendLtSolm hlotSolm
            have h3601 := flapperX_deal_end_lt_ok
              (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
              hticZero hticLt hendLt h3408
            have hHashSize := flapperDealHashMem_size_ge_96 id
            have hHashRead := flapperDealHashMem_read64 id
            have hScratch1Size :=
              flapperDealScratchMem_size_ge_96 id (flapperDealHashMem id)
                hHashSize
            have hScratch1Read :=
              flapperDealScratchMem_read64 id (flapperDealHashMem id)
                hHashSize hHashRead
            have hScratch2Size :=
              flapperDealScratchMem_size_ge_96 id
                (flapperDealScratchMem id (flapperDealHashMem id))
                hScratch1Size
            have hScratch2Read :=
              flapperDealScratchMem_read64 id
                (flapperDealScratchMem id (flapperDealHashMem id))
                hScratch1Size hScratch1Read
            have hMoveBaseSize :
                96 ≤
                  (flapperDealScratchMem id
                    (flapperDealScratchMem id
                      (flapperDealScratchMem id (flapperDealHashMem id)))).size :=
              flapperDealScratchMem_size_ge_96 id
                (flapperDealScratchMem id
                  (flapperDealScratchMem id (flapperDealHashMem id)))
                hScratch2Size
            have hMoveBaseRead :
                (flapperDealScratchMem id
                    (flapperDealScratchMem id
                      (flapperDealScratchMem id (flapperDealHashMem id)))).readWithPadding 64 32 =
                  UInt256.toByteArray (UInt256.ofNat 128) :=
              flapperDealScratchMem_read64 id
                (flapperDealScratchMem id
                  (flapperDealScratchMem id (flapperDealHashMem id)))
                hScratch2Size hScratch2Read
            have htail := flapperDealExternalTailProgress
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (mem3601 := flapperDealScratchMem id
                (flapperDealScratchMem id (flapperDealHashMem id)))
              hAccounts hperm
              (by simpa [id] using hMoveBaseSize)
              (by simpa [id] using hMoveBaseRead)
              (by simpa [id] using h3601)
            have hprogress :
                BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  config { contract := contract, locals := flapperDealLocals id }
                  evmSolm dealTransition.body
                  (runtimeExit (.abi dealTransition.returnType)) := by
              have hp := BlockProgress.prepend hpref htail
              simpa [dealTransition, nonpayable, checkedExternalCallStmts,
                evmSolm, id, lot] using hp
            exact hprogress.toRuntimeEquivalenceFor hcode
              (fun result hfunc => by
                exact solmExec.intro (flapperSelectorDispatch_deal hselLit) rfl hdec
                  (by simp [evmSolm, initState, Sat256.ofUInt256, Sat256.toUInt256])
                  hfunc)
              (by intro result endpoint h; exact h)
          · have hendLtSolmNot :
                ¬ (flapperDealEndWordOfState evmSolm id).toNat <
                  (flapperDealTimestampWordOfState evmSolm).toNat := by
              intro hlt
              exact hendLt (by simpa [hEndWordSolm, hTimestampSolm] using hlt)
            have hbody :
                ExecTransitionBody config contract evmSolm (flapperDealLocals id)
                  dealTransition.body .reverted := by
              simpa [evmSolm, id] using
                flapperDealBodyRevertsTimingTime evmSolm id
                  (by simp only [evmSolm, initState]; exact hwv)
                  hliveSolm hticSolmNe hticLtSolmNot hendLtSolmNot
            exact (flapperX_deal_time_revert
                (g := Sat256.ofUInt256 g) hticZero hticLt hendLt h3408)
              |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hliveSolmNe :
          flapperDealLiveWordOfState evmSolm ≠ UInt256.ofNat 1 := by
        intro hLive
        exact hliveEvm (by rw [← hloadLiveEq]; exact hLive)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperDealLocals id)
            dealTransition.body .reverted := by
        simpa [evmSolm, id] using
          flapperDealBodyRevertsLive evmSolm id
            (by simp only [evmSolm, initState]; exact hwv) hliveSolmNe
      exact (flapperX_deal_live_revert
          (g := Sat256.ofUInt256 g) hliveEvm hdecode)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_deal_none_short (I := I) hsz4 hshort
    have hrev := flapperX_deal_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
