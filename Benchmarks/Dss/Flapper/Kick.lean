import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.Rely
import Benchmarks.Dss.Flapper.Tick
import Benchmarks.Dss.Flapper.RuntimeBlocks_003
import Benchmarks.Dss.Flapper.RuntimeBlocks_005
import Benchmarks.Dss.Flapper.RuntimeBlocks_002
import Benchmarks.Dss.Flapper.RuntimeBlocks_006
import Benchmarks.Dss.Flapper.RuntimeBlocks_007
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

def flapperKickLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperKickBidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def flapperKickLocals (lot bid : UInt256) : Store :=
  ((∅ : Store).insert "lot" (.int (Int.ofNat lot.toNat))).insert "bid"
    (.int (Int.ofNat bid.toNat))

def flapperKickLocalsFillNew (lot bid fillNew : UInt256) : Store :=
  (flapperKickLocals lot bid).insert "fillNew" (.int (Int.ofNat fillNew.toNat))

def flapperKickLocalsId (lot bid fillNew idWord : UInt256) : Store :=
  (flapperKickLocalsFillNew lot bid fillNew).insert "id"
    (.int (Int.ofNat idWord.toNat))

def flapperKickLocalsEnd (lot bid fillNew idWord endWord : UInt256) : Store :=
  (flapperKickLocalsId lot bid fillNew idWord).insert "end_"
    (.int (Int.ofNat endWord.toNat))

def flapperKickFillWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 9)

def flapperKickLidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 8)

def flapperKickKicksWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 6)

def flapperKickFillNewWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperKickFillWord σ I + flapperKickLotWord I

def flapperKickAfterFillWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I)

def flapperKickIdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat 1 + flapperKickKicksWord σ I

def flapperKickBaseSlot (idWord : UInt256) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 1) idWord

def flapperKickPackedSlot (idWord : UInt256) : UInt256 :=
  flapperKickBaseSlot idWord + UInt256.ofNat 2

def flapperKickAfterKicksWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (flapperKickAfterFillWorld σ I) (UInt256.ofNat 6)
    (flapperKickIdWord σ I)

def flapperKickAfterBidWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (flapperKickAfterKicksWorld σ I)
    (flapperKickBaseSlot (flapperKickIdWord σ I)) (flapperKickBidWord I)

def flapperKickAfterLotWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (flapperKickAfterBidWorld σ I)
    (flapperKickBaseSlot (flapperKickIdWord σ I) + UInt256.ofNat 1)
    (flapperKickLotWord I)

def flapperKickGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (UInt256.ofNat I.source.val)
    (UInt256.land (UInt256.lnot flapperAddressMask)
      (storageRead I.codeOwner (flapperKickAfterLotWorld σ I)
        (flapperKickPackedSlot (flapperKickIdWord σ I))))

def flapperKickAfterGuyWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner (flapperKickAfterLotWorld σ I)
    (flapperKickPackedSlot (flapperKickIdWord σ I)) (flapperKickGuyWord σ I)

def flapperKickTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Shift)
    flapperUint48Mask

def flapperKickTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def flapperKickNowWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperKickTimestampWord I) flapperUint48Mask

def flapperKickNewEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperKickTimestampWord I + flapperKickTauWord σ I) flapperUint48Mask

def flapperKickPackedEndWord (old newEnd : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))
    (UInt256.mul flapperUint48Shift208
      (UInt256.land newEnd flapperUint48Mask))

def flapperKickAfterEndWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let idWord := flapperKickIdWord σ I
  let packedSlot := flapperKickPackedSlot idWord
  let ω := flapperKickAfterGuyWorld σ I
  storageWrite I.codeOwner ω packedSlot
    (flapperKickPackedEndWord (storageRead I.codeOwner ω packedSlot)
      (flapperKickNewEndWord ω I))

def flapperKickVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 2)) flapperAddressMask

def flapperKickLiveWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7)

def flapperKickFillWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 9)

def flapperKickLidWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 8)

def flapperKickKicksWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6)

def flapperKickFillNewWordOfState (evm : EVM.State) (lot : UInt256) : UInt256 :=
  flapperKickFillWordOfState evm + lot

def flapperKickIdWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.ofNat 1 + flapperKickKicksWordOfState evm

def flapperKickBaseSlotOfState (evm : EVM.State) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 1) (flapperKickIdWordOfState evm)

def flapperKickPackedSlotOfState (evm : EVM.State) : UInt256 :=
  flapperKickBaseSlotOfState evm + UInt256.ofNat 2

def flapperKickTauWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
      flapperUint48Shift)
    flapperUint48Mask

def flapperKickTimestampWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

def flapperKickNowWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land (flapperKickTimestampWordOfState evm) flapperUint48Mask

def flapperKickNewEndWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land (flapperKickTimestampWordOfState evm + flapperKickTauWordOfState evm)
    flapperUint48Mask

def flapperKickPackedEndWordOfState (evm : EVM.State) : UInt256 :=
  flapperKickPackedEndWord
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flapperKickPackedSlotOfState evm))
    (flapperKickNewEndWordOfState evm)

def flapperKickVatWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
    flapperAddressMask

def flapperKickSourceAfterFill (evm : EVM.State) (fillNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 9) fillNew

def flapperKickSourceAfterKicks (evm : EVM.State) (fillNew idWord : UInt256) :
    EVM.State :=
  let evmFill := flapperKickSourceAfterFill evm fillNew
  Solm.EVM.storageStore evmFill evmFill.executionEnv.codeOwner (UInt256.ofNat 6) idWord

def flapperKickSourceAfterBid (evm : EVM.State) (bid fillNew idWord : UInt256) :
    EVM.State :=
  let evmKicks := flapperKickSourceAfterKicks evm fillNew idWord
  Solm.EVM.storageStore evmKicks evmKicks.executionEnv.codeOwner
    (flapperKickBaseSlot idWord) bid

def flapperKickSourceAfterLot (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    EVM.State :=
  let evmBid := flapperKickSourceAfterBid evm bid fillNew idWord
  Solm.EVM.storageStore evmBid evmBid.executionEnv.codeOwner
    (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot

def flapperKickSourceAfterGuy (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    EVM.State :=
  let evmLot := flapperKickSourceAfterLot evm lot bid fillNew idWord
  Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner (flapperKickPackedSlot idWord)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner
        (flapperKickPackedSlot idWord))
      (UInt256.ofNat evmLot.executionEnv.source.val))

def flapperKickSourceAfterEnd (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) : EVM.State :=
  let evmGuy := flapperKickSourceAfterGuy evm lot bid fillNew idWord
  Solm.EVM.storageStore evmGuy evmGuy.executionEnv.codeOwner (flapperKickPackedSlot idWord)
    (flapperKickPackedEndWord
      (Solm.EVM.storageLoad evmGuy evmGuy.executionEnv.codeOwner
        (flapperKickPackedSlot idWord))
      endWord)

abbrev flapperKickMoveSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)

def flapperKickAuthMem (I : ExecutionEnv) : ByteArray :=
  flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
    (ee := I) (mem := solcFreePtrMem)

def flapperKickHashMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  flapperRuntimeBlocks.flapperRuntime_block_4233_memory
    (ee := I) (mem := flapperKickAuthMem I)
    (σ := flapperKickAfterFillWorld σ I)

def flapperKickCallBaseMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0
    ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickHashMem σ I)
      (UInt256.ofNat 0).toNat 32)
    (UInt256.ofNat 32).toNat 32

def flapperKickCallMemSelector (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  flapperKickMoveSelectorWord.toByteArray.write 0 (flapperKickCallBaseMem σ I) 128 32

def flapperKickCallMemSender (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0
    (flapperKickCallMemSelector σ I) 132 32

def flapperKickCallMemThis (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (flapperKickCallMemSender σ I) 164 32

def flapperKickMoveCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperKickLotWord I).toByteArray.write 0 (flapperKickCallMemThis σ I) 196 32

def flapperKickEventMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  flapperRuntimeBlocks.flapperRuntime_block_4478_memory
    (mem := flapperKickMoveCallMem σ I) (x4 := flapperKickIdWord σ I)
    (x5 := flapperKickBidWord I) (x6 := flapperKickLotWord I)

def flapperKickReturnMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I) 128 32

def flapperKickCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [UInt256.ofNat 228, UInt256.ofNat 3140843579,
    flapperKickVatWord (flapperKickAfterEndWorld σ I) I,
    flapperKickIdWord σ I, flapperKickBidWord I, flapperKickLotWord I,
    UInt256.ofNat 313, sel]

theorem decodeScalarWordsWithMode_uint256_uint256_ok {mode : DecodeMode}
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeScalarWordsWithMode? mode [abiUInt256, abiUInt256] bytes 0 =
      some
        [ .int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
          .int (Int.ofNat
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := mode) (bytes := bytes) (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind, Nat.zero_add]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := mode) (bytes := bytes) (start := 32) hlen32]
  simp only [List.drop_zero]

theorem decodeScalarWordsWithMode_uint256_uint256_none_short {mode : DecodeMode}
    {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWordsWithMode? mode [abiUInt256, abiUInt256] bytes 0 = none := by
  by_cases hlen0 : 32 ≤ bytes.length
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok
      (mode := mode) (bytes := bytes) (start := 0) (by simpa using htake0)]
    simp only [Option.bind, bind, Nat.zero_add]
    rw [decodeScalarWordWithMode_uint256_none_short
      (mode := mode) (bytes := bytes) (start := 32) htake32n]
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short
      (mode := mode) (bytes := bytes) (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem flapperDecode_kick_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata =
      some (flapperKickLocals (flapperKickLotWord I) (flapperKickBidWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["lot", "bid"]
      [abiUInt256, abiUInt256] I.calldata =
    some (flapperKickLocals (flapperKickLotWord I) (flapperKickBidWord I))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = flapperKickLotWord I := by
    simpa [flapperKickLotWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
        flapperKickBidWord I := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      flapperKickBidWord] using
      decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["lot", "bid"])
    (types := [abiUInt256, abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [decodeScalarWordsWithMode_uint256_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4) htake36']
  change decodeCalldata.insertValues ["lot", "bid"]
      [ .int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat) ]
      ∅ =
    some (flapperKickLocals (flapperKickLotWord I) (flapperKickBidWord I))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues, flapperKickLocals]

theorem flapperDecode_kick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode
      (kickTransition.params.map Param.name)
      (transitionSignature kickTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["lot", "bid"]
      [abiUInt256, abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["lot", "bid"])
    (types := [abiUInt256, abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [decodeScalarWordsWithMode_uint256_uint256_none_short
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (by rw [List.length_drop, htlen]; omega)]

theorem flapperDispatch_kick {cd : ByteArray}
    (hsel : ((⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some kickTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition, denyTransition,
      fileTransition, fillTransition, gemTransition])
    (post := [kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
      tendTransition, tickTransition, ttlTransition, vatTransition, wardsTransition,
      yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
    · rw [flapperFileSelectorBytes, hcd]; decide
    · rw [flapperFillSelectorBytes, hcd]; decide
    · rw [flapperGemSelectorBytes, hcd]; decide
  · rw [flapperKickSelectorBytes]
    exact hsel

theorem flapperSelectorDispatch_kick {cd : ByteArray}
    (hsel : ((⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some kickTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList]
  rw [show contract.transitions =
      [begTransition, bidsTransition, cageTransition, dealTransition, denyTransition,
        fileTransition, fillTransition, gemTransition] ++ kickTransition ::
        [kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
          tendTransition, tickTransition, ttlTransition, vatTransition, wardsTransition,
          yankTransition] by rfl]
  refine dispatchList_eq_some_of_split ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
    · rw [flapperFileSelectorBytes, hcd]; decide
    · rw [flapperFillSelectorBytes, hcd]; decide
    · rw [flapperGemSelectorBytes, hcd]; decide
  · rw [flapperKickSelectorBytes]
    exact hsel

theorem flapperX_kick_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3901⟩
      [flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd796⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 64) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 64)
      (by simpa using hsz68) hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 64)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd818 := flapperRuntimeBlocks.flapperRuntime_block_796_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond (by jump_dest) rd796
  have rd3901 := flapperRuntimeBlocks.flapperRuntime_block_818
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd818
  exact ⟨_, _, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_818_stack,
      flapperKickBidWord, flapperKickLotWord, calldataWord,
      show ((UInt256.ofNat 32) + (UInt256.ofNat 4)).toNat = 36 by decide,
      show (UInt256.ofNat 4).toNat = 4 by decide] using rd3901⟩

theorem flapperX_kick_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd796⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 64) = UInt256.ofNat 1 := by
    apply ult_one
    rw [usub_ofNat_word_toNat
      (c := UInt256.ofNat 4)
      (by change 4 ≤ I.calldata.size; omega) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 64)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd814 := flapperRuntimeBlocks.flapperRuntime_block_796_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd796
  exact flapperRuntimeBlocks.flapperRuntime_block_814
    (R := flapperRuntimeBlocks.flapperRuntime_block_796_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_796_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd814

theorem flapperKickAuthHashSlot (I : ExecutionEnv) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
          (ee := I) (mem := mem)) =
      flapperRelyAuthSlot I := by
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (flapperRelyAuthWord I) (UInt256.ofNat 0) mem) =
    flapperRelyAuthSlot I
  simpa [flapperRelyAuthSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyAuthWord I)
      (UInt256.ofNat 0) mem

theorem flapperKickMappingHashSlot (idWord : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          (idWord.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      flapperKickBaseSlot idWord := by
  simpa [flapperKickBaseSlot, flapperTickBaseSlot] using
    flapperTickMappingHashSlot idWord mem

theorem flapperKickAuthHashMem_eq (I : ExecutionEnv) :
    flapperKickAuthMem I =
      twoWordHashMem (flapperRelyAuthWord I) (UInt256.ofNat 0) solcFreePtrMem := by
  simp [flapperKickAuthMem, flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory,
    flapperRelyAuthWord, twoWordHashMem, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperKickAuthMem_size (I : ExecutionEnv) :
    (flapperKickAuthMem I).size = 96 := by
  rw [flapperKickAuthHashMem_eq]
  exact twoWordHashMem_size_96 (flapperRelyAuthWord I) (UInt256.ofNat 0)
    solcFreePtrMem_size

theorem flapperKickAuthMem_read64 (I : ExecutionEnv) :
    (flapperKickAuthMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  rw [flapperKickAuthHashMem_eq]
  simpa using twoWordHashMem_read64 (flapperRelyAuthWord I) (UInt256.ofNat 0)
    solcFreePtrMem_size solcFreePtrMem_read64

@[simp] theorem flapperKickAuthMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickAuthMem I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperKickAuthMem_size I]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperKickAuthMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperKickHashMem_eq (σ : AccountMap) (I : ExecutionEnv) :
    flapperKickHashMem σ I =
      twoWordHashMem (flapperKickIdWord σ I) (UInt256.ofNat 1)
        (flapperKickAuthMem I) := by
  have hreadKicks :
      storageRead I.codeOwner (flapperKickAfterFillWorld σ I) (UInt256.ofNat 6) =
        flapperKickKicksWord σ I := by
    simpa [flapperKickAfterFillWorld, flapperKickKicksWord] using
      storageRead_storageWrite_ne I.codeOwner σ
        (readSlot := UInt256.ofNat 6) (writeSlot := UInt256.ofNat 9)
        (value := flapperKickFillNewWord σ I) (by decide)
  simp [flapperKickHashMem, flapperRuntimeBlocks.flapperRuntime_block_4233_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem, flapperKickIdWord,
    flapperKickKicksWord, hreadKicks,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperKickHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickHashMem σ I).size = 96 := by
  rw [flapperKickHashMem_eq]
  exact twoWordHashMem_size_96 (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickAuthMem_size I)

theorem flapperKickHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickHashMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  rw [flapperKickHashMem_eq]
  simpa using twoWordHashMem_read64 (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickAuthMem_size I) (flapperKickAuthMem_read64 I)

@[simp] theorem flapperKickHashMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickHashMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperKickHashMem_size σ I]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperKickHashMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperKickCallBaseMem_expr_eq (σ : AccountMap) (I : ExecutionEnv) :
    (UInt256.ofNat 1).toByteArray.write 0
        ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickHashMem σ I)
          (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32 =
      flapperKickCallBaseMem σ I := by
  rfl

theorem flapperKickCallBaseMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickCallBaseMem σ I).size = 96 := by
  change (twoWordHashMem (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickHashMem σ I)).size = 96
  exact twoWordHashMem_size_96 (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickHashMem_size σ I)

theorem flapperKickCallBaseMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickCallBaseMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  change (twoWordHashMem (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickHashMem σ I)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)
  simpa using twoWordHashMem_read64 (flapperKickIdWord σ I) (UInt256.ofNat 1)
    (flapperKickHashMem_size σ I) (flapperKickHashMem_read64 σ I)

@[simp] theorem flapperKickCallBaseMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickCallBaseMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperKickCallBaseMem_size σ I]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperKickCallBaseMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperKickRuntimeCallSetupMem_eq (σ : AccountMap) (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_4319_memory
        (ee := I) (mem := flapperKickHashMem σ I)
        (x1 := flapperKickIdWord σ I) =
      flapperKickCallMemThis σ I := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_4319_memory,
    flapperKickCallMemThis, flapperKickCallMemSender, flapperKickCallMemSelector,
    flapperKickMoveSelectorWord,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide]

@[simp] theorem flapperKickMoveCallMem_expr_eq (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickLotWord I).toByteArray.write 0 (flapperKickCallMemThis σ I) 196 32 =
      flapperKickMoveCallMem σ I := by
  rfl

theorem flapperKickCallMemSelector_size_ge_160 (σ : AccountMap) (I : ExecutionEnv) :
    160 ≤ (flapperKickCallMemSelector σ I).size := by
  unfold flapperKickCallMemSelector
  exact toByteArray_write_size_ge_off_add32_unbounded flapperKickMoveSelectorWord
    (flapperKickCallBaseMem σ I) 128

theorem flapperKickCallMemSender_size_ge_164 (σ : AccountMap) (I : ExecutionEnv) :
    164 ≤ (flapperKickCallMemSender σ I).size := by
  unfold flapperKickCallMemSender
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.source.val)
    (flapperKickCallMemSelector σ I) 132

theorem flapperKickCallMemThis_size_ge_196 (σ : AccountMap) (I : ExecutionEnv) :
    196 ≤ (flapperKickCallMemThis σ I).size := by
  unfold flapperKickCallMemThis
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperKickCallMemSender σ I) 164

theorem flapperKickMoveCallMem_size_ge_228 (σ : AccountMap) (I : ExecutionEnv) :
    228 ≤ (flapperKickMoveCallMem σ I).size := by
  unfold flapperKickMoveCallMem
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperKickLotWord I)
    (flapperKickCallMemThis σ I) 196

theorem flapperKickMoveCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperKickMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickLotWord I) _ 196 64
    (by
      have h := flapperKickCallMemThis_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 164 64
    (by
      have h := flapperKickCallMemSender_size_ge_164 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemSender
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val) _ 132 64
    (by
      have h := flapperKickCallMemSelector_size_ge_160 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemSelector
  rw [toByteArray_write_read_below_of_gap_unbounded flapperKickMoveSelectorWord _
    128 64
    (by rw [flapperKickCallBaseMem_size σ I])
    (by omega)]
  exact flapperKickCallBaseMem_read64 σ I

@[simp] theorem flapperKickMoveCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickMoveCallMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperKickMoveCallMem_size_ge_228 σ I
    omega)]
  rw [flapperKickMoveCallMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperKickMoveSelectorPrefix :
    flapperKickMoveSelectorWord.toByteArray.extract 0 4 = moveSelector := by
  native_decide

theorem flapperKickMoveCallMem_read196 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (flapperKickLotWord I) := by
  unfold flapperKickMoveCallMem
  exact toByteArray_write_read_back_of_gap_unbounded (flapperKickLotWord I) _ 196

theorem flapperKickMoveCallMem_read164 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperKickMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickLotWord I) _ 196 164
    (by
      have h := flapperKickCallMemThis_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemThis
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.codeOwner.val) (flapperKickCallMemSender σ I) 164

theorem flapperKickMoveCallMem_read132 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold flapperKickMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickLotWord I) _ 196 132
    (by
      have h := flapperKickCallMemThis_size_ge_196 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 164 132
    (by
      have h := flapperKickCallMemSender_size_ge_164 σ I
      omega)
    (by omega)]
  unfold flapperKickCallMemSender
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.source.val) (flapperKickCallMemSelector σ I) 132

theorem flapperKickMoveCallMem_read128_4 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 128 4 = moveSelector := by
  unfold flapperKickMoveCallMem
  rw [toByteArray_write_read_below_len_of_gap (flapperKickLotWord I) _ 196 128 4
    (by
      have h := flapperKickCallMemThis_size_ge_196 σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperKickCallMemThis_size_ge_196 σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperKickCallMemThis
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 164 128 4
    (by
      have h := flapperKickCallMemSender_size_ge_164 σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperKickCallMemSender_size_ge_164 σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperKickCallMemSender
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.source.val) _ 132 128 4
    (by
      have h := flapperKickCallMemSelector_size_ge_160 σ I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperKickCallMemSelector_size_ge_160 σ I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperKickCallMemSelector
  rw [toByteArray_write_read_window_of_gap_unbounded flapperKickMoveSelectorWord
    (flapperKickCallBaseMem σ I) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperKickMoveSelectorPrefix

theorem flapperKickMoveCallMem_read128_100 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickMoveCallMem σ I).readWithPadding 128 100 =
      moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperKickLotWord I) := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (flapperKickMoveCallMem σ I) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperKickMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperKickMoveCallMem σ I) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperKickMoveCallMem_size_ge_228 σ I
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperKickMoveCallMem σ I) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperKickMoveCallMem_size_ge_228 σ I
      omega)]
  rw [flapperKickMoveCallMem_read128_4, flapperKickMoveCallMem_read132,
    flapperKickMoveCallMem_read164, flapperKickMoveCallMem_read196]
  simp [ByteArray.append_assoc]

theorem flapperKickMoveEncode_eq (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
        [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (flapperKickLotWord I).toNat)] =
      some ((flapperKickMoveCallMem σ I).readWithPadding 128 100) := by
  rw [flapperKickMoveCallMem_read128_100]
  have hlot :
      0 ≤ Int.ofNat (flapperKickLotWord I).toNat ∧
        Int.ofNat (flapperKickLotWord I).toNat < Int.ofNat (EVM.twoPow 256) := by
    constructor
    · exact Int.natCast_nonneg (flapperKickLotWord I).toNat
    ·
      have hltNat : (flapperKickLotWord I).toNat < EVM.twoPow 256 := by
        change (flapperKickLotWord I).val.val < EVM.twoPow 256
        exact (flapperKickLotWord I).val.isLt
      exact Int.ofNat_lt.mpr hltNat
  change externalABI.encode? "move"
        [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (flapperKickLotWord I).toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperKickLotWord I))
  have hencSource :
      encodeABIValue? addr (.address I.source) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) := by
    have hword : EVM.word I.source.val = UInt256.ofNat I.source.val := by
      apply u256_inj
      unfold EVM.word EVM.uintN UInt256.ofNat UInt256.toNat
      simp only [Fin.ofNat]
      change I.source.val % EVM.twoPow 256 = I.source.val % UInt256.size
      simp [EVM.twoPow, UInt256.size]
    simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rw [hword]
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
  have hencLot :
      encodeABIValue? uint256 (.int (Int.ofNat (flapperKickLotWord I).toNat)) =
        some (EVM.Word.toBytesBE (flapperKickLotWord I)) := by
    have hword : EVM.word (flapperKickLotWord I).toNat = flapperKickLotWord I :=
      u256_ofNat_toNat (flapperKickLotWord I)
    have hltNat : (flapperKickLotWord I).toNat < EVM.twoPow 256 := by
      change (flapperKickLotWord I).val.val < EVM.twoPow 256
      exact (flapperKickLotWord I).val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hltNat]
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.source, .address I.codeOwner,
            .int (Int.ofNat (flapperKickLotWord I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val) ++
          EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (flapperKickLotWord I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencSource, hencOwner,
      hencLot, hdynAddr, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem flapperKickEventMem_size_ge_224 (σ : AccountMap) (I : ExecutionEnv) :
    224 ≤ (flapperKickEventMem σ I).size := by
  unfold flapperKickEventMem flapperRuntimeBlocks.flapperRuntime_block_4478_memory
  rw [flapperKickMoveCallMem_mload64]
  rw [show (UInt256.ofNat 128).toNat = 128 by decide]
  rw [show ((UInt256.ofNat 128) + (UInt256.ofNat 32)).toNat = 160 by decide]
  rw [show ((UInt256.ofNat 64) + (UInt256.ofNat 128)).toNat = 192 by decide]
  exact toByteArray_write_size_ge_off_add32_unbounded (flapperKickBidWord I)
    ((flapperKickLotWord I).toByteArray.write 0
      ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickMoveCallMem σ I)
        128 32)
      160 32)
    192

theorem flapperKickEventMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickEventMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperKickEventMem flapperRuntimeBlocks.flapperRuntime_block_4478_memory
  rw [flapperKickMoveCallMem_mload64]
  rw [show (UInt256.ofNat 128).toNat = 128 by decide]
  rw [show ((UInt256.ofNat 128) + (UInt256.ofNat 32)).toNat = 160 by decide]
  rw [show ((UInt256.ofNat 64) + (UInt256.ofNat 128)).toNat = 192 by decide]
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickBidWord I) _ 192 64
    (by
      have h := toByteArray_write_size_ge_off_add32_unbounded (flapperKickLotWord I)
        ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickMoveCallMem σ I)
          128 32) 160
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickLotWord I) _ 160 64
    (by
      have h := toByteArray_write_size_ge_off_add32_unbounded (flapperKickIdWord σ I)
        (flapperKickMoveCallMem σ I) 128
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickIdWord σ I) _
    128 64
    (by
      have h := flapperKickMoveCallMem_size_ge_228 σ I
      omega)
    (by decide)]
  exact flapperKickMoveCallMem_read64 σ I

@[simp] theorem flapperKickEventMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickEventMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperKickEventMem_size_ge_224 σ I
    omega)]
  rw [flapperKickEventMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperKickReturnMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickReturnMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperKickReturnMem
  rw [toByteArray_write_read_below_of_gap_unbounded (flapperKickIdWord σ I) _
    128 64
    (by
      have h := flapperKickEventMem_size_ge_224 σ I
      omega)
    (by omega)]
  exact flapperKickEventMem_read64 σ I

@[simp] theorem flapperKickReturnMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperKickReturnMem σ I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    unfold flapperKickReturnMem
    have h := toByteArray_write_size_ge_off_add32_unbounded
      (flapperKickIdWord σ I) (flapperKickEventMem σ I) 128
    omega)]
  rw [flapperKickReturnMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperKickReturnMem_read128 (σ : AccountMap) (I : ExecutionEnv) :
    (flapperKickReturnMem σ I).readWithPadding 128 32 =
      UInt256.toByteArray (flapperKickIdWord σ I) := by
  unfold flapperKickReturnMem
  exact toByteArray_write_read_back_of_gap_unbounded
    (flapperKickIdWord σ I) (flapperKickEventMem σ I) 128

theorem flapperKickReturnPayload_eq (σ : AccountMap) (I : ExecutionEnv) :
    (((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I)
          (memLoad (UInt256.ofNat 64) (flapperKickEventMem σ I)).toNat 32).readWithPadding
        (memLoad (UInt256.ofNat 64)
          ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I)
            (memLoad (UInt256.ofNat 64) (flapperKickEventMem σ I)).toNat 32)).toNat
        ((UInt256.ofNat 32) +
          (UInt256.sub (memLoad (UInt256.ofNat 64) (flapperKickEventMem σ I))
            (memLoad (UInt256.ofNat 64)
              ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I)
                (memLoad (UInt256.ofNat 64) (flapperKickEventMem σ I)).toNat 32)))).toNat) =
      UInt256.toByteArray (flapperKickIdWord σ I) := by
  rw [flapperKickEventMem_mload64]
  rw [show (UInt256.ofNat 128).toNat = 128 by decide]
  change (flapperKickReturnMem σ I).readWithPadding
      (memLoad (UInt256.ofNat 64) (flapperKickReturnMem σ I)).toNat
      ((UInt256.ofNat 32) +
        UInt256.sub (UInt256.ofNat 128)
          (memLoad (UInt256.ofNat 64) (flapperKickReturnMem σ I))).toNat =
      UInt256.toByteArray (flapperKickIdWord σ I)
  rw [flapperKickReturnMem_mload64]
  rw [show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) =
    UInt256.ofNat 0 by decide]
  rw [show UInt256.ofNat 32 + UInt256.ofNat 0 = UInt256.ofNat 32 by decide]
  exact flapperKickReturnMem_read128 σ I

@[simp] theorem flapperKickReturnWrite_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
        ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I) 128 32) =
      UInt256.ofNat 128 := by
  simpa [flapperKickReturnMem] using flapperKickReturnMem_mload64 σ I

theorem flapperKickReturnWrite_read128 (σ : AccountMap) (I : ExecutionEnv) :
    ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I) 128 32).readWithPadding
        128 32 =
      UInt256.toByteArray (flapperKickIdWord σ I) := by
  simpa [flapperKickReturnMem] using flapperKickReturnMem_read128 σ I

@[simp] theorem flapperKickReturnWrite_mload64_u256off
    (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64)
        ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I)
          (UInt256.ofNat 128).toNat 32) =
      UInt256.ofNat 128 := by
  rw [show (UInt256.ofNat 128).toNat = 128 by decide]
  exact flapperKickReturnWrite_mload64 σ I

theorem flapperKickReturnWrite_read128_u256off
    (σ : AccountMap) (I : ExecutionEnv) :
    ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickEventMem σ I)
        (UInt256.ofNat 128).toNat 32).readWithPadding
        (UInt256.ofNat 128).toNat 32 =
      UInt256.toByteArray (flapperKickIdWord σ I) := by
  rw [show (UInt256.ofNat 128).toNat = 128 by decide]
  exact flapperKickReturnWrite_read128 σ I

theorem flapperX_kick_after_auth_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3994⟩
      [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3901⟩ := flapperX_kick_decode_ok
    (g := g) hsize hsz68 hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ UInt256.ofNat 0 := by
    rw [show
      ((UInt256.ofNat 0).toByteArray.write 0
        ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
          (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) =
          flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
            (ee := I) (mem := solcFreePtrMem) by rfl]
    rw [flapperKickAuthHashSlot, hauth]
    decide
  obtain ⟨_, _, _, rd3994⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3901_taken_packed
      (R := [flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondAuth (by jump_dest) rd3901
  exact ⟨_, _, _, rd3994⟩

theorem flapperX_kick_auth_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) ≠ UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3901⟩ := flapperX_kick_decode_ok
    (g := g) hsize hsz68 hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = UInt256.ofNat 0 := by
    rw [show
      ((UInt256.ofNat 0).toByteArray.write 0
        ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
          (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) =
          flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
            (ee := I) (mem := solcFreePtrMem) by rfl]
    rw [flapperKickAuthHashSlot]
    exact u256_eq_of_ne (by
      intro h
      exact hauth h.symm)
  obtain ⟨_, _, _, rd3925⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3901_fallthrough_packed
      (R := [flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondAuth rd3901
  exact flapperRuntimeBlocks.flapperRuntime_block_3925
    (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3925

theorem flapperX_kick_live_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4068⟩
      [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, _, rd3994⟩ := flapperX_kick_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ (UInt256.ofNat 7)) ≠ UInt256.ofNat 0 := by
    rw [hlive]
    decide
  obtain ⟨_, _, _, rd4068⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3994_taken_packed
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLive (by jump_dest) rd3994
  exact ⟨_, _, _, rd4068⟩

theorem flapperX_kick_live_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) ≠ UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd3994⟩ := flapperX_kick_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ (UInt256.ofNat 7)) = UInt256.ofNat 0 := by
    exact u256_eq_of_ne (by
      intro h
      exact hlive h.symm)
  obtain ⟨_, _, _, rd4005⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3994_fallthrough_packed
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLive rd3994
  exact flapperRuntimeBlocks.flapperRuntime_block_4005
    (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd4005

theorem flapperX_kick_kicks_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4143⟩
      [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, _, rd4068⟩ := flapperX_kick_live_ok
    (g := g) hsize hsz68 hauth hlive hreach
  have hlt :
      UInt256.lt (storageRead I.codeOwner σ (UInt256.ofNat 6))
          (UInt256.lnot (UInt256.ofNat 0)) = UInt256.ofNat 1 :=
    ult_one hkicks
  have hcondKicks :
      UInt256.lt (storageRead I.codeOwner σ (UInt256.ofNat 6))
          (UInt256.lnot (UInt256.ofNat 0)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  obtain ⟨_, _, _, rd4143⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4068_taken_packed
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondKicks (by jump_dest) rd4068
  exact ⟨_, _, _, rd4143⟩

theorem flapperX_kick_kicks_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      ¬ (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4068⟩ := flapperX_kick_live_ok
    (g := g) hsize hsz68 hauth hlive hreach
  have hge :
      (UInt256.lnot (UInt256.ofNat 0)).toNat ≤
        (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat := by
    omega
  have hlt :
      UInt256.lt (storageRead I.codeOwner σ (UInt256.ofNat 6))
          (UInt256.lnot (UInt256.ofNat 0)) = UInt256.ofNat 0 :=
    ult_zero hge
  have hcondKicks :
      UInt256.lt (storageRead I.codeOwner σ (UInt256.ofNat 6))
          (UInt256.lnot (UInt256.ofNat 0)) = UInt256.ofNat 0 := by
    exact hlt
  obtain ⟨_, _, _, rd4080⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4068_fallthrough_packed
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondKicks rd4068
  exact flapperRuntimeBlocks.flapperRuntime_block_4080
    (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd4080

theorem flapperX_kick_fill_overflow_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4143⟩ := flapperX_kick_kicks_ok
    (g := g) hsize hsz68 hauth hlive hkicks hreach
  obtain ⟨_, _, rd4979⟩ := flapperRuntimeBlocks.flapperRuntime_block_4143
    (x0 := UInt256.ofNat 0) (x1 := flapperKickBidWord I)
    (x2 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4143
  have hlt :
      UInt256.lt (flapperKickFillWord σ I + flapperKickLotWord I)
          (flapperKickFillWord σ I) = UInt256.ofNat 1 := by
    exact ult_one (by simpa [flapperKickFillNewWord] using hfill)
  have hcondFill :
      UInt256.isZero
          (UInt256.lt (flapperKickFillWord σ I + flapperKickLotWord I)
            (flapperKickFillWord σ I)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd4991 := flapperRuntimeBlocks.flapperRuntime_block_4979_fallthrough
    (x0 := flapperKickLotWord I) (x1 := flapperKickFillWord σ I)
    (R := [UInt256.ofNat 4155, UInt256.ofNat 0, flapperKickBidWord I,
      flapperKickLotWord I, UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondFill rd4979
  exact flapperRuntimeBlocks.flapperRuntime_block_4991
    (R := [flapperKickFillNewWord σ I, flapperKickLotWord I, flapperKickFillWord σ I,
      UInt256.ofNat 4155, UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa [flapperKickFillNewWord] using rd4991)

theorem flapperX_kick_after_fill_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4155⟩
      [flapperKickFillNewWord σ I, UInt256.ofNat 0, flapperKickBidWord I,
        flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, _, rd4143⟩ := flapperX_kick_kicks_ok
    (g := g) hsize hsz68 hauth hlive hkicks hreach
  obtain ⟨_, _, rd4979⟩ := flapperRuntimeBlocks.flapperRuntime_block_4143
    (x0 := UInt256.ofNat 0) (x1 := flapperKickBidWord I)
    (x2 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4143
  have hge :
      (flapperKickFillWord σ I).toNat ≤
        (flapperKickFillWord σ I + flapperKickLotWord I).toNat := by
    simpa [flapperKickFillNewWord] using (not_lt.mp hfill)
  have hlt :
      UInt256.lt (flapperKickFillWord σ I + flapperKickLotWord I)
          (flapperKickFillWord σ I) = UInt256.ofNat 0 :=
    ult_zero hge
  have hcondFill :
      UInt256.isZero
          (UInt256.lt (flapperKickFillWord σ I + flapperKickLotWord I)
            (flapperKickFillWord σ I)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd4930 := flapperRuntimeBlocks.flapperRuntime_block_4979_taken
    (x0 := flapperKickLotWord I) (x1 := flapperKickFillWord σ I)
    (R := [UInt256.ofNat 4155, UInt256.ofNat 0, flapperKickBidWord I,
      flapperKickLotWord I, UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondFill (by jump_dest) rd4979
  have rd4155 := flapperRuntimeBlocks.flapperRuntime_block_4930
    (x0 := flapperKickFillNewWord σ I) (x1 := flapperKickLotWord I)
    (x2 := flapperKickFillWord σ I) (x3 := UInt256.ofNat 4155)
    (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    (by simpa [flapperRuntimeBlocks.flapperRuntime_block_4979_taken_stack,
      flapperKickFillNewWord] using rd4930)
  exact ⟨_, _, _, rd4155⟩

theorem flapperX_kick_lid_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hlid :
      ¬ (flapperKickFillNewWord σ I).toNat ≤ (flapperKickLidWord σ I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4155⟩ := flapperX_kick_after_fill_ok
    (g := g) hsize hsz68 hauth hlive hkicks hfill hreach
  have hreadLid :
      storageRead I.codeOwner
          (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
          (UInt256.ofNat 8) =
        flapperKickLidWord σ I := by
    simpa [flapperKickLidWord] using
      storageRead_storageWrite_ne I.codeOwner σ
        (readSlot := UInt256.ofNat 8) (writeSlot := UInt256.ofNat 9)
        (value := flapperKickFillNewWord σ I) (by decide)
  have hlt :
      UInt256.lt
          (storageRead I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
            (UInt256.ofNat 8))
          (flapperKickFillNewWord σ I) = UInt256.ofNat 1 := by
    rw [hreadLid]
    exact ult_one (by omega)
  have hcondLid :
      UInt256.isZero
          (UInt256.lt
            (storageRead I.codeOwner
              (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
              (UInt256.ofNat 8))
            (flapperKickFillNewWord σ I)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  obtain ⟨_, _, _, rd4170⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4155_fallthrough_packed
      (x0 := flapperKickFillNewWord σ I)
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm hcondLid rd4155
  exact flapperRuntimeBlocks.flapperRuntime_block_4170
    (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd4170

theorem flapperX_kick_lid_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hlid :
      (flapperKickFillNewWord σ I).toNat ≤ (flapperKickLidWord σ I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4233⟩
      [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, flapperKickAfterFillWorld σ I) k C := by
  obtain ⟨_, _, _, rd4155⟩ := flapperX_kick_after_fill_ok
    (g := g) hsize hsz68 hauth hlive hkicks hfill hreach
  have hreadLid :
      storageRead I.codeOwner
          (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
          (UInt256.ofNat 8) =
        flapperKickLidWord σ I := by
    simpa [flapperKickLidWord] using
      storageRead_storageWrite_ne I.codeOwner σ
        (readSlot := UInt256.ofNat 8) (writeSlot := UInt256.ofNat 9)
        (value := flapperKickFillNewWord σ I) (by decide)
  have hlt :
      UInt256.lt
          (storageRead I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
            (UInt256.ofNat 8))
          (flapperKickFillNewWord σ I) = UInt256.ofNat 0 := by
    rw [hreadLid]
    exact ult_zero hlid
  have hcondLid :
      UInt256.isZero
          (UInt256.lt
            (storageRead I.codeOwner
              (storageWrite I.codeOwner σ (UInt256.ofNat 9) (flapperKickFillNewWord σ I))
              (UInt256.ofNat 8))
            (flapperKickFillNewWord σ I)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  obtain ⟨_, _, _, rd4233⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4155_taken_packed
      (x0 := flapperKickFillNewWord σ I)
      (R := [UInt256.ofNat 0, flapperKickBidWord I, flapperKickLotWord I,
        UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm hcondLid (by jump_dest) rd4155
  exact ⟨_, _, _, by simpa [flapperKickAfterFillWorld] using rd4233⟩

theorem flapperX_kick_after_guy_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hlid :
      (flapperKickFillNewWord σ I).toNat ≤ (flapperKickLidWord σ I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4936⟩
      [flapperKickTauWord (flapperKickAfterGuyWorld σ I) I,
        flapperKickTimestampWord I, UInt256.ofNat 4319, flapperKickIdWord σ I,
        flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperKickHashMem σ I)
      aw ByteArray.empty (cA, flapperKickAfterGuyWorld σ I) k C := by
  obtain ⟨_, _, _, rd4233⟩ := flapperX_kick_lid_ok
    (g := g) hsize hsz68 hperm hauth hlive hkicks hfill hlid hreach
  have hreadKicks :
      storageRead I.codeOwner (flapperKickAfterFillWorld σ I) (UInt256.ofNat 6) =
        flapperKickKicksWord σ I := by
    simpa [flapperKickAfterFillWorld, flapperKickKicksWord] using
      storageRead_storageWrite_ne I.codeOwner σ
        (readSlot := UInt256.ofNat 6) (writeSlot := UInt256.ofNat 9)
        (value := flapperKickFillNewWord σ I) (by decide)
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperKickIdWord σ I).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
                (ee := I) (mem := solcFreePtrMem))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperKickBaseSlot (flapperKickIdWord σ I) :=
    flapperKickMappingHashSlot (flapperKickIdWord σ I)
      (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
        (ee := I) (mem := solcFreePtrMem))
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((UInt256.ofNat 1 + storageRead I.codeOwner σ (UInt256.ofNat 6)).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_3901_taken_memory
                (ee := I) (mem := solcFreePtrMem))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot (UInt256.ofNat 1)
          (UInt256.ofNat 1 + storageRead I.codeOwner σ (UInt256.ofNat 6)) := by
    simpa [flapperKickIdWord, flapperKickKicksWord, flapperKickBaseSlot] using hhash
  obtain ⟨_, _, _, rd4936⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4233_packed
      (σ := flapperKickAfterFillWorld σ I)
      (x0 := UInt256.ofNat 0) (x1 := flapperKickBidWord I)
      (x2 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm (by jump_dest) rd4233
  exact ⟨_, _, _, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4233_stack,
      flapperKickAfterKicksWorld, flapperKickAfterBidWorld,
      flapperKickAfterLotWorld, flapperKickAfterGuyWorld, flapperKickGuyWord,
      flapperKickIdWord, flapperKickKicksWord, flapperKickBaseSlot,
      flapperKickPackedSlot, flapperKickTauWord, flapperKickTimestampWord,
      flapperKickHashMem, flapperKickAuthMem, flapperAddressMask, flapperUint48Mask,
      flapperUint48Shift,
      hreadKicks, hhashRaw, u256_add_comm] using rd4936⟩

theorem flapperX_kick_end_overflow_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hlid :
      (flapperKickFillNewWord σ I).toNat ≤ (flapperKickLidWord σ I).toNat)
    (hwrap :
      (flapperKickNewEndWord (flapperKickAfterGuyWorld σ I) I).toNat <
        (flapperKickNowWord I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4936⟩ := flapperX_kick_after_guy_ok
    (g := g) hsize hsz68 hperm hauth hlive hkicks hfill hlid hreach
  have hltWrap :
      UInt256.lt (flapperKickNewEndWord (flapperKickAfterGuyWorld σ I) I)
          (flapperKickNowWord I) = UInt256.ofNat 1 := by
    exact ult_one hwrap
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              (flapperKickTimestampWord I +
                flapperKickTauWord (flapperKickAfterGuyWorld σ I) I)
              flapperUint48Mask)
            (UInt256.land (flapperKickTimestampWord I) flapperUint48Mask)) =
        UInt256.ofNat 0 := by
    simpa [flapperKickNewEndWord, flapperKickNowWord] using
      (by rw [hltWrap]; decide :
        UInt256.isZero
          (UInt256.lt (flapperKickNewEndWord (flapperKickAfterGuyWorld σ I) I)
            (flapperKickNowWord I)) = UInt256.ofNat 0)
  have rd4959 := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough
    (x0 := flapperKickTauWord (flapperKickAfterGuyWorld σ I) I)
    (x1 := flapperKickTimestampWord I)
    (R := [UInt256.ofNat 4319, flapperKickIdWord σ I, flapperKickBidWord I,
      flapperKickLotWord I, UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa [flapperKickTauWord, flapperKickTimestampWord, flapperUint48Mask]
      using hcondWrap)
    rd4936
  exact flapperRuntimeBlocks.flapperRuntime_block_4959
    (R := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack
      (x0 := flapperKickTauWord (flapperKickAfterGuyWorld σ I) I)
      (x1 := flapperKickTimestampWord I)
      (R := [UInt256.ofNat 4319, flapperKickIdWord σ I, flapperKickBidWord I,
        flapperKickLotWord I, UInt256.ofNat 313, sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd4959

theorem flapperX_kick_after_end_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hkicks :
      (storageRead I.codeOwner σ (UInt256.ofNat 6)).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfill :
      ¬ (flapperKickFillNewWord σ I).toNat < (flapperKickFillWord σ I).toNat)
    (hlid :
      (flapperKickFillNewWord σ I).toNat ≤ (flapperKickLidWord σ I).toNat)
    (hwrap :
      ¬ (flapperKickNewEndWord (flapperKickAfterGuyWorld σ I) I).toNat <
        (flapperKickNowWord I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨796⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4407⟩
      [UInt256.ofNat 196, UInt256.ofNat 128,
        storageRead I.codeOwner (flapperKickAfterEndWorld σ I) (UInt256.ofNat 2),
        UInt256.ofNat 0, UInt256.ofNat 64, flapperKickIdWord σ I,
        flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperKickCallMemThis σ I) aw ByteArray.empty
      (cA, flapperKickAfterEndWorld σ I) k C := by
  obtain ⟨_, _, _, rd4936⟩ := flapperX_kick_after_guy_ok
    (g := g) hsize hsz68 hperm hauth hlive hkicks hfill hlid hreach
  let ω := flapperKickAfterGuyWorld σ I
  have hwrapω :
      ¬ (flapperKickNewEndWord ω I).toNat < (flapperKickNowWord I).toNat := by
    simpa [ω] using hwrap
  have hltWrap :
      UInt256.lt (flapperKickNewEndWord ω I) (flapperKickNowWord I) =
        UInt256.ofNat 0 := by
    exact ult_zero (not_lt.mp hwrapω)
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              (flapperKickTimestampWord I + flapperKickTauWord ω I)
              flapperUint48Mask)
            (UInt256.land (flapperKickTimestampWord I) flapperUint48Mask)) ≠
        UInt256.ofNat 0 := by
    simpa [flapperKickNewEndWord, flapperKickNowWord, ω] using
      (by rw [hltWrap]; decide :
        UInt256.isZero
          (UInt256.lt (flapperKickNewEndWord ω I) (flapperKickNowWord I)) ≠
            UInt256.ofNat 0)
  have rd4930 := flapperRuntimeBlocks.flapperRuntime_block_4936_taken
    (x0 := flapperKickTauWord ω I) (x1 := flapperKickTimestampWord I)
    (R := [UInt256.ofNat 4319, flapperKickIdWord σ I, flapperKickBidWord I,
      flapperKickLotWord I, UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa [flapperKickTauWord, flapperKickTimestampWord, flapperUint48Mask, ω]
      using hcondWrap)
    (by jump_dest) rd4936
  have rd4319 := flapperRuntimeBlocks.flapperRuntime_block_4930
    (x0 := flapperKickTimestampWord I + flapperKickTauWord ω I)
    (x1 := flapperKickTauWord ω I) (x2 := flapperKickTimestampWord I)
    (x3 := UInt256.ofNat 4319)
    (R := [flapperKickIdWord σ I, flapperKickBidWord I, flapperKickLotWord I,
      UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4930
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickHashMem σ I)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperKickBaseSlot (flapperKickIdWord σ I) :=
    flapperKickMappingHashSlot (flapperKickIdWord σ I) (flapperKickHashMem σ I)
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (flapperKickCallBaseMem σ I) =
        solcMappingSlot (UInt256.ofNat 1) (flapperKickIdWord σ I) := by
    change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          ((flapperKickIdWord σ I).toByteArray.write 0 (flapperKickHashMem σ I)
            (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      solcMappingSlot (UInt256.ofNat 1) (flapperKickIdWord σ I)
    simpa [flapperKickBaseSlot] using hhash
  have hnewClean :
      UInt256.land (flapperKickNewEndWord ω I) flapperUint48Mask =
        flapperKickNewEndWord ω I := by
    simpa [flapperKickNewEndWord] using
      flapperUint48Mask_clean_right_file
        (flapperKickTimestampWord I + flapperKickTauWord ω I)
  have hnewActual :
      UInt256.land flapperUint48Mask
          (flapperKickTimestampWord I + flapperKickTauWord ω I) =
        flapperKickNewEndWord ω I := by
    rw [u256_land_comm flapperUint48Mask
      (flapperKickTimestampWord I + flapperKickTauWord ω I)]
    rfl
  have hnewActualRaw :
      UInt256.land flapperUint48Mask
          (flapperKickTauWord ω I + flapperKickTimestampWord I) =
        flapperKickNewEndWord ω I := by
    rw [u256_add_comm (flapperKickTauWord ω I) (flapperKickTimestampWord I)]
    exact hnewActual
  obtain ⟨_, _, _, rd4407⟩ := flapperRuntimeBlocks.flapperRuntime_block_4319_packed
    (x0 := flapperKickTimestampWord I + flapperKickTauWord ω I)
    (x1 := flapperKickIdWord σ I)
    (R := [flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm rd4319
  exact ⟨_, _, _, by
    simpa [ω, flapperRuntimeBlocks.flapperRuntime_block_4319_stack,
      flapperKickAfterEndWorld, flapperKickPackedEndWord, flapperKickPackedSlot,
      flapperKickBaseSlot, flapperKickNewEndWord, flapperKickCallMemThis,
      flapperKickRuntimeCallSetupMem_eq, hhashRaw, hnewActual, hnewActualRaw,
      hnewClean, flapperUint48Mask_clean_right_file, flapperUint48Mask,
      flapperUint48Shift208, u256_add_comm,
      show UInt256.ofNat 68 + UInt256.ofNat 128 = UInt256.ofNat 196 by decide]
      using rd4407⟩

theorem flapperX_kick_no_code_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcodeSize :
      extCodeSizeWord (flapperKickAfterEndWorld σ I)
          (flapperKickVatWord (flapperKickAfterEndWorld σ I) I) =
        UInt256.ofNat 0)
    (h4407 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4407⟩
      [UInt256.ofNat 196, UInt256.ofNat 128,
        storageRead I.codeOwner (flapperKickAfterEndWorld σ I) (UInt256.ofNat 2),
        UInt256.ofNat 0, UInt256.ofNat 64, flapperKickIdWord σ I,
        flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperKickCallMemThis σ I) aw ByteArray.empty
      (cA, flapperKickAfterEndWorld σ I) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd4407⟩ := h4407
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord (flapperKickAfterEndWorld σ I)
              (UInt256.land
                (storageRead I.codeOwner (flapperKickAfterEndWorld σ I)
                  (UInt256.ofNat 2))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    simpa [flapperKickVatWord, flapperAddressMask] using
      (by rw [hcodeSize]; decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord (flapperKickAfterEndWorld σ I)
            (flapperKickVatWord (flapperKickAfterEndWorld σ I) I))) =
          UInt256.ofNat 0)
  obtain ⟨_, _, _, rd4454⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4407_fallthrough_packed
      (σ := flapperKickAfterEndWorld σ I)
      (x0 := UInt256.ofNat 196) (x1 := UInt256.ofNat 128)
      (x2 := storageRead I.codeOwner (flapperKickAfterEndWorld σ I)
        (UInt256.ofNat 2))
      (x3 := UInt256.ofNat 0) (x4 := UInt256.ofNat 64)
      (x5 := flapperKickIdWord σ I) (x6 := flapperKickBidWord I)
      (x7 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt rd4407
  exact flapperRuntimeBlocks.flapperRuntime_block_4454
    (R := flapperRuntimeBlocks.flapperRuntime_block_4407_fallthrough_stack
      (mem := flapperKickCallMemThis σ I) (σ := flapperKickAfterEndWorld σ I)
      (x0 := UInt256.ofNat 196) (x1 := UInt256.ofNat 128)
      (x2 := storageRead I.codeOwner (flapperKickAfterEndWorld σ I)
        (UInt256.ofNat 2))
      (x3 := UInt256.ofNat 0) (x4 := UInt256.ofNat 64)
      (x5 := flapperKickIdWord σ I) (x6 := flapperKickBidWord I)
      (x7 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_4407_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd4454

theorem flapperX_kick_call_boundary {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hcodeSize :
      extCodeSizeWord (flapperKickAfterEndWorld σ I)
          (flapperKickVatWord (flapperKickAfterEndWorld σ I) I) ≠
        UInt256.ofNat 0)
    (h4407 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4407⟩
      [UInt256.ofNat 196, UInt256.ofNat 128,
        storageRead I.codeOwner (flapperKickAfterEndWorld σ I) (UInt256.ofNat 2),
        UInt256.ofNat 0, UInt256.ofNat 64, flapperKickIdWord σ I,
        flapperKickBidWord I, flapperKickLotWord I, UInt256.ofNat 313, sel]
      (flapperKickCallMemThis σ I) aw ByteArray.empty
      (cA, flapperKickAfterEndWorld σ I) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4461⟩
      (gasArg :: flapperKickVatWord (flapperKickAfterEndWorld σ I) I ::
        UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 100 ::
        UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperKickCallRest σ I sel)
      (flapperKickMoveCallMem σ I) aw ByteArray.empty
      (cA, flapperKickAfterEndWorld σ I) k C := by
  obtain ⟨aw, _, _, rd4407⟩ := h4407
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord (flapperKickAfterEndWorld σ I)
              (UInt256.land
                (storageRead I.codeOwner (flapperKickAfterEndWorld σ I)
                  (UInt256.ofNat 2))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠
        UInt256.ofNat 0 := by
    simpa [flapperKickVatWord, flapperAddressMask] using
      (by
        rw [isZero_eq_zero_of_ne hcodeSize]
        decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord (flapperKickAfterEndWorld σ I)
            (flapperKickVatWord (flapperKickAfterEndWorld σ I) I))) ≠
          UInt256.ofNat 0)
  obtain ⟨aw4458, k4458, C4458, rd4458raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4407_taken_packed
      (σ := flapperKickAfterEndWorld σ I)
      (x0 := UInt256.ofNat 196) (x1 := UInt256.ofNat 128)
      (x2 := storageRead I.codeOwner (flapperKickAfterEndWorld σ I)
        (UInt256.ofNat 2))
      (x3 := UInt256.ofNat 0) (x4 := UInt256.ofNat 64)
      (x5 := flapperKickIdWord σ I) (x6 := flapperKickBidWord I)
      (x7 := flapperKickLotWord I) (R := [UInt256.ofNat 313, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest) rd4407
  have rd4458 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4458⟩
        (UInt256.isZero
            (extCodeSizeWord (flapperKickAfterEndWorld σ I)
              (flapperKickVatWord (flapperKickAfterEndWorld σ I) I)) ::
          flapperKickVatWord (flapperKickAfterEndWorld σ I) I ::
          UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 100 ::
          UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperKickCallRest σ I sel)
        (flapperKickMoveCallMem σ I) aw4458 ByteArray.empty
        (cA, flapperKickAfterEndWorld σ I) k4458 C4458 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4407_taken_stack,
      flapperRuntimeBlocks.flapperRuntime_block_4407_taken_memory,
      flapperKickVatWord, flapperKickCallRest, flapperAddressMask,
      show (UInt256.ofNat 196).toNat = 196 by decide,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
        decide,
      show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
      show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide]
      using rd4458raw
  have rd4460 := flapperRuntimeBlocks.flapperRuntime_block_4458
    (x0 := UInt256.isZero
      (extCodeSizeWord (flapperKickAfterEndWorld σ I)
        (flapperKickVatWord (flapperKickAfterEndWorld σ I) I)))
    (R := flapperKickVatWord (flapperKickAfterEndWorld σ I) I ::
      UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 100 ::
      UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperKickCallRest σ I sel)
    (by simp only [flapperKickCallRest, List.length_cons, List.length_nil]; omega)
    rd4458
  have rd4460' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4460⟩
        (flapperKickVatWord (flapperKickAfterEndWorld σ I) I ::
          UInt256.ofNat 0 :: UInt256.ofNat 128 :: UInt256.ofNat 100 ::
          UInt256.ofNat 128 :: UInt256.ofNat 0 :: flapperKickCallRest σ I sel)
        (flapperKickMoveCallMem σ I) aw4458 ByteArray.empty
        (cA, flapperKickAfterEndWorld σ I) (k4458 + 2) (C4458 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4458_stack] using rd4460
  obtain ⟨gasArg, rd4461raw⟩ := RD.rawGas rd4460' (by native_decide)
    (by simp only [flapperKickCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw4458, k4458 + 2 + 1, C4458 + 3 + 2, ?_⟩
  simpa [show UInt256.ofNat 4460 + ⟨1⟩ = UInt256.ofNat 4461 by native_decide]
    using rd4461raw

theorem flapperX_kick_call_failure {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4462⟩
      (UInt256.ofNat 0 :: flapperKickCallRest σ I sel) mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4469 := flapperRuntimeBlocks.flapperRuntime_block_4462_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperKickCallRest σ I sel)
    (by simp only [flapperKickCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_4469
    (R := flapperRuntimeBlocks.flapperRuntime_block_4462_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperKickCallRest σ I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_4462_fallthrough_stack,
        flapperKickCallRest, List.length_cons, List.length_nil]
      omega)
    rd4469

set_option maxHeartbeats 1000000 in
theorem flapperX_kick_call_success {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4462⟩
      (UInt256.ofNat 1 :: flapperKickCallRest σ I sel)
      (flapperKickMoveCallMem σ I) aw rdata world k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) world
      (UInt256.toByteArray (flapperKickIdWord σ I)) := by
  have rd4478 := flapperRuntimeBlocks.flapperRuntime_block_4462_taken
    (x0 := UInt256.ofNat 1) (R := flapperKickCallRest σ I sel)
    (by simp only [flapperKickCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) h
  have rd4478' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4478⟩
        (UInt256.ofNat 0 :: flapperKickCallRest σ I sel)
        (flapperKickMoveCallMem σ I) aw rdata world (k + 5) (C + 22) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4462_taken_stack,
      flapperKickCallRest] using rd4478
  obtain ⟨aw313, k313, C313, rd313⟩ := flapperRuntimeBlocks.flapperRuntime_block_4478_packed
    (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
    (x2 := UInt256.ofNat 3140843579)
    (x3 := flapperKickVatWord (flapperKickAfterEndWorld σ I) I)
    (x4 := flapperKickIdWord σ I) (x5 := flapperKickBidWord I)
    (x6 := flapperKickLotWord I) (x7 := UInt256.ofNat 313)
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd4478'
  have rd313Packed :
      ∃ aw' k' C',
        RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨313⟩
          [flapperKickIdWord σ I, sel] (flapperKickEventMem σ I)
          aw' rdata world k' C' := by
    refine ⟨aw313, k313, C313, ?_⟩
    simpa [flapperRuntimeBlocks.flapperRuntime_block_4478_stack,
      flapperRuntimeBlocks.flapperRuntime_block_4478_memory, flapperKickCallRest,
      flapperKickEventMem, flapperKickMoveCallMem_mload64, flapperKickEventMem_mload64,
      show UInt256.ofNat 128 + UInt256.ofNat 32 = UInt256.ofNat 160 by decide,
      show UInt256.ofNat 64 + UInt256.ofNat 128 = UInt256.ofNat 192 by decide,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
        decide,
      show UInt256.ofNat 96 + UInt256.ofNat 0 = UInt256.ofNat 96 by decide]
      using rd313
  obtain ⟨_, _, _, rd313'⟩ := rd313Packed
  have hret := flapperRuntimeBlocks.flapperRuntime_block_313
    (x0 := flapperKickIdWord σ I) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd313'
  simpa [flapperKickEventMem_mload64, flapperKickReturnWrite_mload64,
    flapperKickReturnWrite_mload64_u256off, flapperKickReturnWrite_read128,
    flapperKickReturnWrite_read128_u256off,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
      decide,
    show UInt256.ofNat 32 + UInt256.ofNat 0 = UInt256.ofNat 32 by decide]
    using hret

theorem flapperKickAddNoWrap_not_lt_left (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    ¬ (a + b).toNat < a.toNat := by
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  omega

theorem flapperKickAddWrap_lt_left (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    (a + b).toNat < a.toNat := by
  have hsumLt : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod :
      (a.toNat + b.toNat) % UInt256.size =
        a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  rw [uadd_toNat, hmod]
  have hb : b.toNat < UInt256.size := b.val.isLt
  omega

theorem flapperKickAddNoWrap_toNat (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]

theorem flapperKickIntOneBeq_true (w : UInt256) (h : w = UInt256.ofNat 1) :
    ((Value.int (Int.ofNat w.toNat)) == Value.int 1) = true := by
  subst w
  decide

theorem flapperKickIntOneBeq_false (w : UInt256) (h : w ≠ UInt256.ofNat 1) :
    ((Value.int (Int.ofNat w.toNat)) == Value.int 1) = false := by
  cases hbeq : ((Value.int (Int.ofNat w.toNat)) == Value.int 1)
  · rfl
  · exact False.elim <| h <| by
      have hval := beq_iff_eq.mp hbeq
      injection hval with hint
      apply u256_inj
      simpa using hint

theorem flapperKickVarInt_eval {evm : EVM.State} {locals : Store}
    {name : Ident} {word : UInt256}
    (hget : locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat word.toNat)) := by
  unfold evalExpr?
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat word.toNat))
  rw [hget]
  rfl

theorem flapperKickLot_eval (evm : EVM.State) (lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperKickLocals lot bid } evm
        (.var "lot") =
      .ok (.int (Int.ofNat lot.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocals
  rw [store_get_ne (k := "bid") (a := "lot")
    (v := Solm.Value.int (Int.ofNat bid.toNat)) (h := by decide)]
  exact store_get_self (∅ : Store) "lot" (Solm.Value.int (Int.ofNat lot.toNat))

theorem flapperKickBid_eval (evm : EVM.State) (lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperKickLocals lot bid } evm
        (.var "bid") =
      .ok (.int (Int.ofNat bid.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocals
  exact store_get_self ((∅ : Store).insert "lot" (Solm.Value.int (Int.ofNat lot.toNat)))
    "bid" (Solm.Value.int (Int.ofNat bid.toNat))

theorem flapperKickLot_eval_id (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
        (.var "lot") =
      .ok (.int (Int.ofNat lot.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsId flapperKickLocalsFillNew flapperKickLocals
  rw [store_get_ne (k := "id") (a := "lot")
    (v := Solm.Value.int (Int.ofNat idWord.toNat)) (h := by decide)]
  rw [store_get_ne (k := "fillNew") (a := "lot")
    (v := Solm.Value.int (Int.ofNat fillNew.toNat)) (h := by decide)]
  rw [store_get_ne (k := "bid") (a := "lot")
    (v := Solm.Value.int (Int.ofNat bid.toNat)) (h := by decide)]
  exact store_get_self (∅ : Store) "lot" (Solm.Value.int (Int.ofNat lot.toNat))

theorem flapperKickBid_eval_id (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
        (.var "bid") =
      .ok (.int (Int.ofNat bid.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsId flapperKickLocalsFillNew flapperKickLocals
  rw [store_get_ne (k := "id") (a := "bid")
    (v := Solm.Value.int (Int.ofNat idWord.toNat)) (h := by decide)]
  rw [store_get_ne (k := "fillNew") (a := "bid")
    (v := Solm.Value.int (Int.ofNat fillNew.toNat)) (h := by decide)]
  exact store_get_self ((∅ : Store).insert "lot" (Solm.Value.int (Int.ofNat lot.toNat)))
    "bid" (Solm.Value.int (Int.ofNat bid.toNat))

theorem flapperKickFillNew_eval (evm : EVM.State)
    (lot bid fillNew : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew } evm
        (.var "fillNew") =
      .ok (.int (Int.ofNat fillNew.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsFillNew
  exact store_get_self (flapperKickLocals lot bid) "fillNew"
    (Solm.Value.int (Int.ofNat fillNew.toNat))

theorem flapperKickFillNew_eval_id (evm : EVM.State)
    (lot bid fillNew idWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
        (.var "fillNew") =
      .ok (.int (Int.ofNat fillNew.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsId
  rw [store_get_ne (k := "id") (a := "fillNew")
    (v := Solm.Value.int (Int.ofNat idWord.toNat)) (h := by decide)]
  exact store_get_self (flapperKickLocals lot bid) "fillNew"
    (Solm.Value.int (Int.ofNat fillNew.toNat))

theorem flapperKickId_eval (evm : EVM.State)
    (lot bid fillNew idWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
        (.var "id") =
      .ok (.int (Int.ofNat idWord.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsId
  exact store_get_self (flapperKickLocalsFillNew lot bid fillNew) "id"
    (Solm.Value.int (Int.ofNat idWord.toNat))

theorem flapperKickId_eval_end (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord } evm
        (.var "id") =
      .ok (.int (Int.ofNat idWord.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsEnd
  rw [store_get_ne (k := "end_") (a := "id")
    (v := Solm.Value.int (Int.ofNat endWord.toNat)) (h := by decide)]
  exact store_get_self (flapperKickLocalsFillNew lot bid fillNew) "id"
    (Solm.Value.int (Int.ofNat idWord.toNat))

theorem flapperKickEnd_eval (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord } evm
        (.var "end_") =
      .ok (.int (Int.ofNat endWord.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsEnd
  exact store_get_self (flapperKickLocalsId lot bid fillNew idWord) "end_"
    (Solm.Value.int (Int.ofNat endWord.toNat))

theorem flapperKickLive_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (flapperKickLiveWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "live", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm liveRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨7⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [flapperKickLiveWordOfState,
    show (⟨7⟩ : UInt256) = UInt256.ofNat 7 by decide]

theorem flapperKickKicks_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "kicks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage kicksRef) =
      .ok (.int (Int.ofNat (flapperKickKicksWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "kicks", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm kicksRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨6⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [flapperKickKicksWordOfState,
    show (⟨6⟩ : UInt256) = UInt256.ofNat 6 by decide]

theorem flapperKickFill_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "fill" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage fillRef) =
      .ok (.int (Int.ofNat (flapperKickFillWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "fill", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm fillRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, fillRef, EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨9⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [flapperKickFillWordOfState,
    show (⟨9⟩ : UInt256) = UInt256.ofNat 9 by decide]

theorem flapperKickLid_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "lid" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage lidRef) =
      .ok (.int (Int.ofNat (flapperKickLidWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "lid", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm lidRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, lidRef, EvalResult.bind, bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨8⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [flapperKickLidWordOfState,
    show (⟨8⟩ : UInt256) = UInt256.ofNat 8 by decide]

theorem flapperKickTau_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage tauRef) =
      .ok (.int (Int.ofNat (flapperKickTauWordOfState evm).toNat)) := by
  let erTau : EvaledStorageRef := { base := "tau", steps := [] }
  have herTau : evalStorageRef config { contract := contract, locals := locals } evm
      tauRef = .ok erTau := by
    simp [erTau, evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind]
  have htyTau : storageTypeAt? contract.storage erTau =
      some (.elem (.int uint48Int)) := by
    simp [erTau, contract, storageDecls, storageTypeAt?, uint48St]
  have hlocTau : config.storage.layout erTau =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTau]
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herTau)
    (hty := htyTau) (hloc := hlocTau), flapperStorageLocLoad_uint48_offset6]
  simp [flapperKickTauWordOfState,
    show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide]

theorem flapperKickVat_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat (flapperKickVatWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "vat", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm vatRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    decide
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨2⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc), flapperStorageLocLoad_address]
  simp [flapperKickVatWordOfState, flapperAddressMask_eq_solcAddrMask,
    show (⟨2⟩ : UInt256) = UInt256.ofNat 2 by decide]

theorem flapperKickLiveGuard_eval_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  have hLiveEval := flapperKickLive_eval evm locals hbase
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLiveEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLiveEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperKickIntOneBeq_true (flapperKickLiveWordOfState evm) hlive]

theorem flapperKickLiveGuard_eval_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none)
    (hlive : flapperKickLiveWordOfState evm ≠ UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  have hLiveEval := flapperKickLive_eval evm locals hbase
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLiveEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLiveEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperKickIntOneBeq_false (flapperKickLiveWordOfState evm) hlive]

theorem flapperKickKicksGuard_eval_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "kicks" = none)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
      .ok (.bool true) := by
  have hKicksEval := flapperKickKicks_eval evm locals hbase
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hKicksEval
  have hmax : (UInt256.lnot (UInt256.ofNat 0)).toNat = (2 : Nat) ^ 256 - 1 := by
    native_decide
  have hkNat :
      (flapperKickKicksWordOfState evm).toNat < (2 : Nat) ^ 256 - 1 := by
    simpa [hmax] using hkicks
  have hltInt :
      Int.ofNat (flapperKickKicksWordOfState evm).toNat < maxUint256 := by
    have hmaxInt : maxUint256 = Int.ofNat ((2 : Nat) ^ 256 - 1) := by
      native_decide
    rw [hmaxInt]
    exact Int.ofNat_lt.mpr hkNat
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hKicksEval]
  simpa [evalBinaryOp?] using hltInt

theorem flapperKickKicksGuard_eval_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "kicks" = none)
    (hkicks :
      ¬ (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
      .ok (.bool false) := by
  have hKicksEval := flapperKickKicks_eval evm locals hbase
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hKicksEval
  have hmax : (UInt256.lnot (UInt256.ofNat 0)).toNat = (2 : Nat) ^ 256 - 1 := by
    native_decide
  have hkNat :
      ¬ (flapperKickKicksWordOfState evm).toNat < (2 : Nat) ^ 256 - 1 := by
    simpa [hmax] using hkicks
  have hnotInt :
      ¬ Int.ofNat (flapperKickKicksWordOfState evm).toNat < maxUint256 := by
    have hmaxInt : maxUint256 = Int.ofNat ((2 : Nat) ^ 256 - 1) := by
      native_decide
    rw [hmaxInt]
    intro hlt
    apply hkNat
    exact Int.ofNat_lt.mp hlt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hKicksEval]
  simpa [evalBinaryOp?] using hnotInt

theorem flapperKickFillAdd_eval_ok (evm : EVM.State) (lot bid : UInt256)
    (hfit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := flapperKickLocals lot bid } evm
        (add256 (.storage fillRef) (.var "lot")) =
      .ok (.int (Int.ofNat (flapperKickFillNewWordOfState evm lot).toNat)) := by
  have hFillEval := flapperKickFill_eval evm (flapperKickLocals lot bid) (by
    simp [flapperKickLocals])
  have hLotEval := flapperKickLot_eval evm lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hFillEval hLotEval
  have hsumEq :
      Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat =
        Int.ofNat (flapperKickFillNewWordOfState evm lot).toNat := by
    have hn :
        (flapperKickFillNewWordOfState evm lot).toNat =
          (flapperKickFillWordOfState evm).toNat + lot.toNat := by
      simpa [flapperKickFillNewWordOfState] using
        flapperKickAddNoWrap_toNat (flapperKickFillWordOfState evm) lot hfit
    calc
      Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat =
          Int.ofNat ((flapperKickFillWordOfState evm).toNat + lot.toNat) := by
        norm_num
      _ = Int.ofNat (flapperKickFillNewWordOfState evm lot).toNat := by
        rw [hn]
  have hnot :
      ¬ (Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat < 0 ∨
        Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat ≥
          (2 : Int) ^ 256) := by
    intro hor
    rcases hor with hneg | hge
    · have hnonneg :
          0 ≤ Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat := by
        have h₁ : 0 ≤ Int.ofNat (flapperKickFillWordOfState evm).toNat := by
          exact Int.natCast_nonneg _
        have h₂ : 0 ≤ Int.ofNat lot.toNat := by
          exact Int.natCast_nonneg _
        omega
      omega
    ·
      have hfitInt :
          Int.ofNat ((flapperKickFillWordOfState evm).toNat + lot.toNat) <
            (2 : Int) ^ 256 := by
        have hfitNat :
            (flapperKickFillWordOfState evm).toNat + lot.toNat < (2 : Nat) ^ 256 := by
          simpa [UInt256.size] using hfit
        exact Int.ofNat_lt.mpr hfitNat
      have hsum :
          Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat =
            Int.ofNat ((flapperKickFillWordOfState evm).toNat + lot.toNat) := by
        norm_num
      omega
  simp only [add256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hFillEval, hLotEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  have hleft :
      decide
          (Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat < 0) =
        false := by
    exact decide_eq_false (fun h => hnot (Or.inl h))
  have hright :
      decide
          (Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat ≥
            (2 : Int) ^ 256) = false := by
    exact decide_eq_false (fun h => hnot (Or.inr h))
  rw [hleft, hright]
  simpa [hsumEq]

theorem flapperKickFillAdd_eval_revert (evm : EVM.State) (lot bid : UInt256)
    (hover :
      UInt256.size ≤ (flapperKickFillWordOfState evm).toNat + lot.toNat) :
    evalExpr? config { contract := contract, locals := flapperKickLocals lot bid } evm
        (add256 (.storage fillRef) (.var "lot")) =
      .revert := by
  have hFillEval := flapperKickFill_eval evm (flapperKickLocals lot bid) (by
    simp [flapperKickLocals])
  have hLotEval := flapperKickLot_eval evm lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hFillEval hLotEval
  have hbad :
      Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat ≥
        (2 : Int) ^ 256 := by
    have hsum :
        Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat =
          Int.ofNat ((flapperKickFillWordOfState evm).toNat + lot.toNat) := by
      norm_num
    rw [hsum]
    have hoverNat :
        (2 : Nat) ^ 256 ≤ (flapperKickFillWordOfState evm).toNat + lot.toNat := by
      simpa [UInt256.size] using hover
    exact Int.ofNat_le.mpr hoverNat
  have hor :
      Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat < 0 ∨
        Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat ≥
          (2 : Int) ^ 256 := Or.inr hbad
  simp only [add256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hFillEval, hLotEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  have hright :
      decide
          (Int.ofNat (flapperKickFillWordOfState evm).toNat + Int.ofNat lot.toNat ≥
            (2 : Int) ^ 256) = true := by
    exact decide_eq_true hbad
  rw [hright]
  simp

theorem flapperKickFillCheckedGuard_eval_true (evm : EVM.State)
    (lot bid fillNew : UInt256)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew } evm
        (.binary .ge (.var "fillNew") (.storage fillRef)) =
      .ok (.bool true) := by
  subst fillNew
  have hFillNewEval := flapperKickFillNew_eval evm lot bid
    (flapperKickFillNewWordOfState evm lot)
  have hFillEval := flapperKickFill_eval evm
    (flapperKickLocalsFillNew lot bid (flapperKickFillNewWordOfState evm lot)) (by
      simp [flapperKickLocalsFillNew, flapperKickLocals])
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hFillNewEval hFillEval
  have hge :
      Int.ofNat (flapperKickFillWordOfState evm).toNat ≤
        Int.ofNat (flapperKickFillNewWordOfState evm lot).toNat := by
    have hn := flapperKickAddNoWrap_toNat (flapperKickFillWordOfState evm) lot hfit
    have hn' :
        (flapperKickFillNewWordOfState evm lot).toNat =
          (flapperKickFillWordOfState evm).toNat + lot.toNat := by
      simpa [flapperKickFillNewWordOfState] using hn
    exact (Int.ofNat_le).mpr (by omega)
  have hgeNat :
      (flapperKickFillWordOfState evm).toNat ≤
        (flapperKickFillNewWordOfState evm lot).toNat :=
    Int.ofNat_le.mp hge
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hFillNewEval, hFillEval]
  simpa [evalBinaryOp?] using hgeNat

theorem flapperKickIdAdd_eval_ok (evm : EVM.State)
    (lot bid fillNew idWord : UInt256)
    (hid : idWord = flapperKickIdWordOfState evm)
    (hfit : (flapperKickKicksWordOfState evm).toNat + 1 < UInt256.size) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew } evm
        (add256 (.storage kicksRef) (.intLit 1)) =
      .ok (.int (Int.ofNat idWord.toNat)) := by
  subst idWord
  have hKicksEval := flapperKickKicks_eval evm (flapperKickLocalsFillNew lot bid fillNew) (by
    simp [flapperKickLocalsFillNew, flapperKickLocals])
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hKicksEval
  have hidNat :
      (flapperKickIdWordOfState evm).toNat =
        (flapperKickKicksWordOfState evm).toNat + 1 := by
    rw [flapperKickIdWordOfState, u256_add_comm]
    exact flapperKickAddNoWrap_toNat (flapperKickKicksWordOfState evm) (UInt256.ofNat 1)
      (by simpa using hfit)
  have hsumEq :
      Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 =
        Int.ofNat (flapperKickIdWordOfState evm).toNat := by
    rw [hidNat]
    norm_num
  have hnot :
      ¬ (Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 < 0 ∨
        Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 ≥
          (2 : Int) ^ 256) := by
    intro hor
    rcases hor with hneg | hge
    · have hnonneg :
          0 ≤ Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 := by
        have h₁ : 0 ≤ Int.ofNat (flapperKickKicksWordOfState evm).toNat := by
          exact Int.natCast_nonneg _
        omega
      omega
    · have hfitInt :
          Int.ofNat ((flapperKickKicksWordOfState evm).toNat + 1) <
            (2 : Int) ^ 256 := by
        have hfitNat :
            (flapperKickKicksWordOfState evm).toNat + 1 < (2 : Nat) ^ 256 := by
          simpa [UInt256.size] using hfit
        exact Int.ofNat_lt.mpr hfitNat
      have hsum :
          Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 =
            Int.ofNat ((flapperKickKicksWordOfState evm).toNat + 1) := by
        norm_num
      omega
  simp only [add256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hKicksEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  have hleft :
      decide (Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 < 0) = false := by
    exact decide_eq_false (fun h => hnot (Or.inl h))
  have hright :
      decide
          (Int.ofNat (flapperKickKicksWordOfState evm).toNat + 1 ≥
            (2 : Int) ^ 256) = false := by
    exact decide_eq_false (fun h => hnot (Or.inr h))
  rw [hleft, hright]
  simpa [hsumEq]

theorem flapperKickIdCheckedGuard_eval_true (evm : EVM.State)
    (lot bid fillNew idWord : UInt256)
    (hid : idWord = flapperKickIdWordOfState evm)
    (hfit : (flapperKickKicksWordOfState evm).toNat + 1 < UInt256.size) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
        (.binary .ge (.var "id") (.storage kicksRef)) =
      .ok (.bool true) := by
  subst idWord
  have hIdEval := flapperKickId_eval evm lot bid fillNew (flapperKickIdWordOfState evm)
  have hKicksEval := flapperKickKicks_eval evm
    (flapperKickLocalsId lot bid fillNew (flapperKickIdWordOfState evm)) (by
      simp [flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals])
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hIdEval hKicksEval
  have hge :
      Int.ofNat (flapperKickKicksWordOfState evm).toNat ≤
        Int.ofNat (flapperKickIdWordOfState evm).toNat := by
    have hidNat :
        (flapperKickIdWordOfState evm).toNat =
          (flapperKickKicksWordOfState evm).toNat + 1 := by
      rw [flapperKickIdWordOfState, u256_add_comm]
      exact flapperKickAddNoWrap_toNat (flapperKickKicksWordOfState evm) (UInt256.ofNat 1)
        (by simpa using hfit)
    rw [hidNat]
    exact Int.ofNat_le.mpr (Nat.le_add_right (flapperKickKicksWordOfState evm).toNat 1)
  have hgeNat :
      (flapperKickKicksWordOfState evm).toNat ≤
        (flapperKickIdWordOfState evm).toNat :=
    Int.ofNat_le.mp hge
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hIdEval, hKicksEval]
  simpa [evalBinaryOp?] using hgeNat

theorem flapperKickLot_eval_end (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord } evm
        (.var "lot") =
      .ok (.int (Int.ofNat lot.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperKickLocalsEnd flapperKickLocalsId flapperKickLocalsFillNew flapperKickLocals
  rw [store_get_ne (k := "end_") (a := "lot")
    (v := Solm.Value.int (Int.ofNat endWord.toNat)) (h := by decide)]
  rw [store_get_ne (k := "id") (a := "lot")
    (v := Solm.Value.int (Int.ofNat idWord.toNat)) (h := by decide)]
  rw [store_get_ne (k := "fillNew") (a := "lot")
    (v := Solm.Value.int (Int.ofNat fillNew.toNat)) (h := by decide)]
  rw [store_get_ne (k := "bid") (a := "lot")
    (v := Solm.Value.int (Int.ofNat bid.toNat)) (h := by decide)]
  exact store_get_self (∅ : Store) "lot" (Solm.Value.int (Int.ofNat lot.toNat))

theorem flapperKickId_eval_afterMoveRet (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) :
    evalExpr? config
        { contract := contract,
          locals :=
            (flapperKickLocalsEnd lot bid fillNew idWord endWord).insert "_moveRet"
              (collapseReturns []) } evm (.var "id") =
      .ok (.int (Int.ofNat idWord.toNat)) := by
  apply flapperKickVarInt_eval
  rw [store_get_ne (k := "_moveRet") (a := "id")
    (v := collapseReturns []) (h := by decide)]
  change (flapperKickLocalsEnd lot bid fillNew idWord endWord).get? "id" =
    some (.int (Int.ofNat idWord.toNat))
  unfold flapperKickLocalsEnd
  rw [store_get_ne (k := "end_") (a := "id")
    (v := Solm.Value.int (Int.ofNat endWord.toNat)) (h := by decide)]
  exact store_get_self (flapperKickLocalsFillNew lot bid fillNew) "id"
    (Solm.Value.int (Int.ofNat idWord.toNat))

theorem flapperKickFillLidGuard_eval_true (evm : EVM.State) (locals : Store)
    (hbaseFill : locals.get? "fill" = none)
    (hbaseLid : locals.get? "lid" = none)
    (hlid : (flapperKickFillWordOfState evm).toNat ≤
      (flapperKickLidWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.storage fillRef) (.storage lidRef)) =
      .ok (.bool true) := by
  have hFillEval := flapperKickFill_eval evm locals hbaseFill
  have hLidEval := flapperKickLid_eval evm locals hbaseLid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hFillEval hLidEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hFillEval, hLidEval]
  simpa [evalBinaryOp?] using hlid

theorem flapperKickFillLidGuard_eval_false (evm : EVM.State) (locals : Store)
    (hbaseFill : locals.get? "fill" = none)
    (hbaseLid : locals.get? "lid" = none)
    (hlid : ¬ (flapperKickFillWordOfState evm).toNat ≤
      (flapperKickLidWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .le (.storage fillRef) (.storage lidRef)) =
      .ok (.bool false) := by
  have hFillEval := flapperKickFill_eval evm locals hbaseFill
  have hLidEval := flapperKickLid_eval evm locals hbaseLid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hFillEval hLidEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hFillEval, hLidEval]
  simpa [evalBinaryOp?] using hlid

theorem flapperKickNow48_eval (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (flapperKickNowWordOfState evm).toNat)) := by
  simpa [flapperKickNowWordOfState, flapperKickTimestampWordOfState,
    flapperTickNowWordOfState, flapperTickTimestampWordOfState] using
    flapperTickNow48_eval evm locals

theorem flapperKickNewEnd_eval (evm : EVM.State) (locals : Store)
    (hbaseTau : locals.get? "tau" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (flapperKickNewEndWordOfState evm).toNat)) := by
  let nowWord := flapperKickNowWordOfState evm
  let tauWord := flapperKickTauWordOfState evm
  have htauLt : tauWord.toNat < 2 ^ 48 := by
    simpa [tauWord, flapperKickTauWordOfState] using
      flapperUint48Word_lt
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
          flapperUint48Shift)
  have hmod :
      (Int.ofNat nowWord.toNat + Int.ofNat tauWord.toNat) % uint48Modulus =
        Int.ofNat (flapperKickNewEndWordOfState evm).toNat := by
    rw [uint48Modulus]
    change (Int.ofNat (nowWord.toNat + tauWord.toNat)) %
        (Int.ofNat ((2 : Nat) ^ 48)) =
      Int.ofNat (flapperKickNewEndWordOfState evm).toNat
    calc
      (Int.ofNat (nowWord.toNat + tauWord.toNat)) %
          (Int.ofNat ((2 : Nat) ^ 48)) =
        Int.ofNat ((nowWord.toNat + tauWord.toNat) % (2 : Nat) ^ 48) := by
          exact (Int.natCast_emod (nowWord.toNat + tauWord.toNat)
            ((2 : Nat) ^ 48)).symm
      _ = Int.ofNat (flapperKickNewEndWordOfState evm).toNat := by
        exact congrArg Int.ofNat
          (by
            simpa [nowWord, tauWord, flapperKickNowWordOfState,
              flapperKickNewEndWordOfState] using
              flapperUint48Low_add_mod
                (flapperKickTimestampWordOfState evm)
                (flapperKickTauWordOfState evm) htauLt)
  have hnonzero : uint48Modulus ≠ 0 := by
    norm_num [uint48Modulus]
  simp only [wrap48, evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [flapperKickNow48_eval evm locals]
  have hTauEval := flapperKickTau_eval evm locals hbaseTau
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTauEval
  rw [hTauEval]
  change (if uint48Modulus = 0 then EvalResult.revert
    else EvalResult.ok (Value.int
      ((Int.ofNat nowWord.toNat + Int.ofNat tauWord.toNat) % uint48Modulus))) =
    EvalResult.ok (Value.int (Int.ofNat (flapperKickNewEndWordOfState evm).toNat))
  rw [if_neg hnonzero, hmod]

theorem flapperKickEndCheckedGuard_eval_true (evm : EVM.State)
    (lot bid fillNew idWord : UInt256)
    (hwrap :
      ¬ (flapperKickNewEndWordOfState evm).toNat <
        (flapperKickNowWordOfState evm).toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperKickLocalsEnd lot bid fillNew idWord
            (flapperKickNewEndWordOfState evm) } evm
        (.binary .ge (.var "end_") now48) =
      .ok (.bool true) := by
  have hEndLocal := flapperKickEnd_eval evm lot bid fillNew idWord
    (flapperKickNewEndWordOfState evm)
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndLocal
  have hNowEval := flapperKickNow48_eval evm
    (flapperKickLocalsEnd lot bid fillNew idWord (flapperKickNewEndWordOfState evm))
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndLocal, hNowEval]
  have hgeNat :
      (flapperKickNowWordOfState evm).toNat ≤
        (flapperKickNewEndWordOfState evm).toNat := by
    omega
  simpa [evalBinaryOp?] using hgeNat

theorem flapperKickEndCheckedGuard_eval_false (evm : EVM.State)
    (lot bid fillNew idWord : UInt256)
    (hwrap :
      (flapperKickNewEndWordOfState evm).toNat <
        (flapperKickNowWordOfState evm).toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperKickLocalsEnd lot bid fillNew idWord
            (flapperKickNewEndWordOfState evm) } evm
        (.binary .ge (.var "end_") now48) =
      .ok (.bool false) := by
  have hEndLocal := flapperKickEnd_eval evm lot bid fillNew idWord
    (flapperKickNewEndWordOfState evm)
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndLocal
  have hNowEval := flapperKickNow48_eval evm
    (flapperKickLocalsEnd lot bid fillNew idWord (flapperKickNewEndWordOfState evm))
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndLocal, hNowEval]
  have hnotNat :
      ¬ (flapperKickNowWordOfState evm).toNat ≤
        (flapperKickNewEndWordOfState evm).toNat := by
    omega
  simpa [evalBinaryOp?] using hnotNat

theorem flapperKickAssignFill (evm : EVM.State) (lot bid fillNew : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew } evm
      .storage fillRef (.int (Int.ofNat fillNew.toNat)) =
      .ok ({ contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 9) fillNew) := by
  let locals := flapperKickLocalsFillNew lot bid fillNew
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "fill", steps := [] }
  have hbase : locals.get? "fill" = none := by
    simp [locals, flapperKickLocalsFillNew, flapperKickLocals]
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

theorem flapperKickAssignKicks (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
      .storage kicksRef (.int (Int.ofNat idWord.toNat)) =
      .ok ({ contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 6) idWord) := by
  let locals := flapperKickLocalsId lot bid fillNew idWord
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "kicks", steps := [] }
  have hbase : locals.get? "kicks" = none := by
    simp [locals, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals]
  have her : evalStorageRef config solm evm kicksRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨6⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨6⟩ : UInt256)) (.int (Int.ofNat idWord.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 6) idWord) := by
    simpa [wordLoc, uint256Loc, show (⟨6⟩ : UInt256) = UInt256.ofNat 6 by decide] using
      storageLocStore_uint256 evm (⟨6⟩ : UInt256) idWord
  change assignStorageRef? config solm evm .storage kicksRef
      (.int (Int.ofNat idWord.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (UInt256.ofNat 6) idWord)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperKickAssignBid (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat bid.toNat)) =
      .ok ({ contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickBaseSlot idWord) bid) := by
  let locals := flapperKickLocalsId lot bid fillNew idWord
  let solm : Frame := { contract := contract, locals := locals }
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "bid"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat idWord.toNat)) := by
    simp [locals, flapperKickLocalsId]
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat idWord.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herBid : evalStorageRef config solm evm
      (bidsF (.var "id") "bid") = .ok erBid := by
    simp [solm, erBid, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperKickBaseSlot idWord)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperKickBaseSlot]
    rw [hkey]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (flapperKickBaseSlot idWord))
          (.int (Int.ofNat bid.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickBaseSlot idWord) bid) := by
    simpa [wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (flapperKickBaseSlot idWord) bid
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "bid")
      (.int (Int.ofNat bid.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperKickBaseSlot idWord) bid)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := herBid) (hty := htyBid) (hloc := hlocBid)
    (hstore := hstore)

theorem flapperKickAssignLot (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
      .storage (bidsF (.var "id") "lot") (.int (Int.ofNat lot.toNat)) =
      .ok ({ contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot) := by
  let locals := flapperKickLocalsId lot bid fillNew idWord
  let solm : Frame := { contract := contract, locals := locals }
  let erLot : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "lot"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat idWord.toNat)) := by
    simp [locals, flapperKickLocalsId]
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat idWord.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herLot : evalStorageRef config solm evm
      (bidsF (.var "id") "lot") = .ok erLot := by
    simp [solm, erLot, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyLot : storageTypeAt? contract.storage erLot =
      some (.elem (.int uint256Int)) := by
    simp [erLot, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocLot : config.storage.layout erLot =
      fun _ => some (wordLoc (flapperKickBaseSlot idWord + UInt256.ofNat 1)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erLot,
      bidsBase, mapSlot, solcMappingSlot, flapperKickBaseSlot]
    rw [hkey]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (flapperKickBaseSlot idWord + UInt256.ofNat 1))
          (.int (Int.ofNat lot.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot) := by
    simpa [wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "lot")
      (.int (Int.ofNat lot.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := herLot) (hty := htyLot) (hloc := hlocLot)
    (hstore := hstore)

theorem flapperKickAddrLoc_eq_addressOffset0Loc (slot : UInt256) :
    addrLoc slot = addressOffset0Loc slot := by
  unfold addrLoc addressOffset0Loc
  congr

theorem flapperKickStorageLocStore_address_source (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addrLoc slot) (.address evm.executionEnv.source) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat evm.executionEnv.source.val))) := by
  let senderWord := UInt256.ofNat evm.executionEnv.source.val
  have hsenderWord :
      senderWord.toNat = evm.executionEnv.source.val := by
    have hword : evm.executionEnv.source.val < UInt256.size := by
      exact lt_of_lt_of_le evm.executionEnv.source.isLt (by decide)
    simpa [senderWord] using ulit_toNat' evm.executionEnv.source.val hword
  have hcanon : senderWord.toNat < EVM.addressModulus := by
    rw [hsenderWord]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
      evm.executionEnv.source.isLt
  have haddrEq : AccountAddress.ofNat senderWord.toNat = evm.executionEnv.source := by
    apply Fin.ext
    simp [AccountAddress.ofNat, hsenderWord]
  have hstore :=
    storageLocStore_address_offset0 evm slot senderWord hcanon
  rw [flapperKickAddrLoc_eq_addressOffset0Loc]
  simpa [haddrEq, senderWord] using hstore

theorem flapperKickAssignGuy (evm : EVM.State) (lot bid fillNew idWord : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord } evm
      .storage (bidsF (.var "id") "guy") (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := flapperKickLocalsId lot bid fillNew idWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickPackedSlot idWord)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperKickPackedSlot idWord))
            (UInt256.ofNat evm.executionEnv.source.val))) := by
  let locals := flapperKickLocalsId lot bid fillNew idWord
  let solm : Frame := { contract := contract, locals := locals }
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "guy"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat idWord.toNat)) := by
    simp [locals, flapperKickLocalsId]
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat idWord.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herGuy : evalStorageRef config solm evm
      (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [solm, erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyGuy : storageTypeAt? contract.storage erGuy = some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperKickPackedSlot idWord)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperKickPackedSlot, flapperKickBaseSlot]
    rw [hkey]
    change addrLoc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2) =
      addrLoc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
    rfl
  have hstore :
      storageLocStore evm (addrLoc (flapperKickPackedSlot idWord))
          (.address evm.executionEnv.source) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickPackedSlot idWord)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperKickPackedSlot idWord))
            (UInt256.ofNat evm.executionEnv.source.val))) :=
    flapperKickStorageLocStore_address_source evm (flapperKickPackedSlot idWord)
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "guy")
      (.address evm.executionEnv.source) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperKickPackedSlot idWord)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (flapperKickPackedSlot idWord))
        (UInt256.ofNat evm.executionEnv.source.val)))
  exact assignStorageRef_storage_scalar_value (ty := .elem .address)
    (hbase := hbase) (her := herGuy) (hty := htyGuy) (hloc := hlocGuy)
    (hscalar := by trivial) (hstore := hstore)

theorem flapperKickGuyWord_eq_setAddress (σ : AccountMap) (I : ExecutionEnv) :
    flapperKickGuyWord σ I =
      setAddressOffset0Word
        (storageRead I.codeOwner (flapperKickAfterLotWorld σ I)
          (flapperKickPackedSlot (flapperKickIdWord σ I)))
        (UInt256.ofNat I.source.val) := by
  unfold flapperKickGuyWord setAddressOffset0Word
  rw [flapperAddressMask_eq_solcAddrMask]
  have hsenderWord :
      (UInt256.ofNat I.source.val).toNat = I.source.val := by
    have hword : I.source.val < UInt256.size := by
      exact lt_of_lt_of_le I.source.isLt (by decide)
    simpa using ulit_toNat' I.source.val hword
  have hcanon : (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
    rw [hsenderWord]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt
  rw [solcAddrMask_clean hcanon]
  rw [u256_land_comm
    (storageRead I.codeOwner (flapperKickAfterLotWorld σ I)
      (flapperKickPackedSlot (flapperKickIdWord σ I)))
    (UInt256.lnot solcAddrMask)]
  exact u256_lor_comm (UInt256.ofNat I.source.val)
    (UInt256.land (UInt256.lnot solcAddrMask)
      (storageRead I.codeOwner (flapperKickAfterLotWorld σ I)
        (flapperKickPackedSlot (flapperKickIdWord σ I))))

theorem flapperKickAssignEnd (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256)
    (hclean : UInt256.land endWord flapperUint48Mask = endWord) :
    assignStorageRef? config
      { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord } evm
      .storage (bidsF (.var "id") "end") (.int (Int.ofNat endWord.toNat)) =
      .ok ({ contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (flapperKickPackedSlot idWord)
          (flapperKickPackedEndWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperKickPackedSlot idWord))
            endWord)) := by
  let locals := flapperKickLocalsEnd lot bid fillNew idWord endWord
  let solm : Frame := { contract := contract, locals := locals }
  let erEnd : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "end"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperKickLocalsEnd, flapperKickLocalsId, flapperKickLocalsFillNew,
      flapperKickLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat idWord.toNat)) := by
    change (flapperKickLocalsEnd lot bid fillNew idWord endWord).get? "id" =
      some (.int (Int.ofNat idWord.toNat))
    unfold flapperKickLocalsEnd
    rw [store_get_ne (k := "end_") (a := "id")
      (v := Solm.Value.int (Int.ofNat endWord.toNat)) (h := by decide)]
    exact store_get_self (flapperKickLocalsFillNew lot bid fillNew) "id"
      (Solm.Value.int (Int.ofNat idWord.toNat))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat idWord.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herEnd : evalStorageRef config solm evm
      (bidsF (.var "id") "end") = .ok erEnd := by
    simp [solm, erEnd, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyEnd : storageTypeAt? contract.storage erEnd =
      some (.elem (.int uint48Int)) := by
    simp [erEnd, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocEnd : config.storage.layout erEnd =
      fun _ => some (uint48Loc (flapperKickPackedSlot idWord)
        ⟨26, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erEnd,
      bidsBase, mapSlot, solcMappingSlot, flapperKickPackedSlot, flapperKickBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)
    rfl
  have hstore :
      storageLocStore evm
          (uint48Loc (flapperKickPackedSlot idWord) ⟨26, by decide⟩ (by decide))
          (.int (Int.ofNat endWord.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperKickPackedSlot idWord)
          (flapperKickPackedEndWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperKickPackedSlot idWord))
            endWord)) := by
    simpa [flapperKickPackedEndWord, hclean] using
      flapperStorageLocStore_uint48_offset26 evm (flapperKickPackedSlot idWord) endWord
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "end")
      (.int (Int.ofNat endWord.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperKickPackedSlot idWord)
      (flapperKickPackedEndWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (flapperKickPackedSlot idWord))
        endWord))
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
    (hbase := hbase) (her := herEnd) (hty := htyEnd) (hloc := hlocEnd)
    (hstore := hstore)

theorem flapperKickPrefixOk (evm : EVM.State) (lot bid fillNew idWord endWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size)
    (hfillLid :
      (flapperKickFillWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat ≤
        (flapperKickLidWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat)
    (hid :
      idWord = flapperKickIdWordOfState (flapperKickSourceAfterFill evm fillNew))
    (hidFit :
      (flapperKickKicksWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat + 1 <
        UInt256.size)
    (hend :
      endWord =
        flapperKickNewEndWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord))
    (hwrap :
      ¬ endWord.toNat <
        (flapperKickNowWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord)).toNat) :
    ExecBlock config
      { contract := contract, locals := flapperKickLocals lot bid } evm
      (nonpayable ++ auth ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
        checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
        [ .assign .storage fillRef (.var "fillNew"),
          .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
        checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
        [ .assign .storage kicksRef (.var "id"),
          .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
          .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
          .assign .storage (bidsF (.var "id") "guy") sender ] ++
        checkedAdd48Into "end_" now48 (.storage tauRef) ++
        [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ])
      (.ok
        { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord }
        (flapperKickSourceAfterEnd evm lot bid fillNew idWord endWord)) := by
  let locals0 := flapperKickLocals lot bid
  let frame0 : Frame := { contract := contract, locals := locals0 }
  let localsFill := flapperKickLocalsFillNew lot bid fillNew
  let frameFill : Frame := { contract := contract, locals := localsFill }
  let evmFill := flapperKickSourceAfterFill evm fillNew
  let localsId := flapperKickLocalsId lot bid fillNew idWord
  let frameId : Frame := { contract := contract, locals := localsId }
  let evmKicks := flapperKickSourceAfterKicks evm fillNew idWord
  let evmBid := flapperKickSourceAfterBid evm bid fillNew idWord
  let evmLot := flapperKickSourceAfterLot evm lot bid fillNew idWord
  let evmGuy := flapperKickSourceAfterGuy evm lot bid fillNew idWord
  let localsEnd := flapperKickLocalsEnd lot bid fillNew idWord endWord
  let frameEnd : Frame := { contract := contract, locals := localsEnd }
  let evmEnd := flapperKickSourceAfterEnd evm lot bid fillNew idWord endWord
  have hAuthGuard :
      evalExpr? config frame0 evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals0
      (by simp [locals0, flapperKickLocals]) hauth
  have hLiveGuard :
      evalExpr? config frame0 evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperKickLiveGuard_eval_true evm locals0
      (by simp [locals0, flapperKickLocals]) hlive
  have hKicksGuard :
      evalExpr? config frame0 evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
          .ok (.bool true) := by
    exact flapperKickKicksGuard_eval_true evm locals0
      (by simp [locals0, flapperKickLocals]) hkicks
  have hLetFill :
      evalExpr? config frame0 evm (add256 (.storage fillRef) (.var "lot")) =
        .ok (.int (Int.ofNat fillNew.toNat)) := by
    rw [hfillNew]
    exact flapperKickFillAdd_eval_ok evm lot bid hfillFit
  have hFillCheck :
      evalExpr? config frameFill evm
        (.binary .ge (.var "fillNew") (.storage fillRef)) =
          .ok (.bool true) := by
    simpa [frameFill, localsFill] using
      flapperKickFillCheckedGuard_eval_true evm lot bid fillNew hfillNew hfillFit
  have hFillRhs :
      evalExpr? config frameFill evm (.var "fillNew") =
        .ok (.int (Int.ofNat fillNew.toNat)) := by
    exact flapperKickFillNew_eval evm lot bid fillNew
  have hAssignFill :
      assignStorageRef? config frameFill evm .storage fillRef
          (.int (Int.ofNat fillNew.toNat)) =
        .ok (frameFill, evmFill) := by
    simpa [frameFill, localsFill, evmFill, flapperKickSourceAfterFill] using
      flapperKickAssignFill evm lot bid fillNew
  have hFillLidGuard :
      evalExpr? config frameFill evmFill
        (.binary .le (.storage fillRef) (.storage lidRef)) =
          .ok (.bool true) := by
    exact flapperKickFillLidGuard_eval_true evmFill localsFill
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simpa [evmFill] using hfillLid)
  have hLetId :
      evalExpr? config frameFill evmFill (add256 (.storage kicksRef) (.intLit 1)) =
        .ok (.int (Int.ofNat idWord.toNat)) := by
    exact flapperKickIdAdd_eval_ok evmFill lot bid fillNew idWord
      (by simpa [evmFill] using hid) (by simpa [evmFill] using hidFit)
  have hIdCheck :
      evalExpr? config frameId evmFill (.binary .ge (.var "id") (.storage kicksRef)) =
        .ok (.bool true) := by
    exact flapperKickIdCheckedGuard_eval_true evmFill lot bid fillNew idWord
      (by simpa [evmFill] using hid) (by simpa [evmFill] using hidFit)
  have hIdRhs :
      evalExpr? config frameId evmFill (.var "id") =
        .ok (.int (Int.ofNat idWord.toNat)) := by
    exact flapperKickId_eval evmFill lot bid fillNew idWord
  have hAssignKicks :
      assignStorageRef? config frameId evmFill .storage kicksRef
          (.int (Int.ofNat idWord.toNat)) =
        .ok (frameId, evmKicks) := by
    simpa [frameId, localsId, evmKicks, flapperKickSourceAfterKicks, evmFill] using
      flapperKickAssignKicks evmFill lot bid fillNew idWord
  have hBidRhs :
      evalExpr? config frameId evmKicks (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    exact flapperKickBid_eval_id evmKicks lot bid fillNew idWord
  have hAssignBid :
      assignStorageRef? config frameId evmKicks .storage (bidsF (.var "id") "bid")
          (.int (Int.ofNat bid.toNat)) =
        .ok (frameId, evmBid) := by
    simpa [frameId, localsId, evmBid, flapperKickSourceAfterBid, evmKicks] using
      flapperKickAssignBid evmKicks lot bid fillNew idWord
  have hLotRhs :
      evalExpr? config frameId evmBid (.var "lot") =
        .ok (.int (Int.ofNat lot.toNat)) := by
    exact flapperKickLot_eval_id evmBid lot bid fillNew idWord
  have hAssignLot :
      assignStorageRef? config frameId evmBid .storage (bidsF (.var "id") "lot")
          (.int (Int.ofNat lot.toNat)) =
        .ok (frameId, evmLot) := by
    simpa [frameId, localsId, evmLot, flapperKickSourceAfterLot, evmBid] using
      flapperKickAssignLot evmBid lot bid fillNew idWord
  have hSenderRhs :
      evalExpr? config frameId evmLot sender =
        .ok (.address evmLot.executionEnv.source) := by
    simp [frameId, sender, evalExpr?, envValue, pure]
  have hAssignGuy :
      assignStorageRef? config frameId evmLot .storage (bidsF (.var "id") "guy")
          (.address evmLot.executionEnv.source) =
        .ok (frameId, evmGuy) := by
    simpa [frameId, localsId, evmGuy, flapperKickSourceAfterGuy, evmLot] using
      flapperKickAssignGuy evmLot lot bid fillNew idWord
  have hLetEnd :
      evalExpr? config frameId evmGuy (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat endWord.toNat)) := by
    rw [hend]
    exact flapperKickNewEnd_eval evmGuy localsId
      (by simp [localsId, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals])
  have hwrap' :
      ¬ (flapperKickNewEndWordOfState evmGuy).toNat <
        (flapperKickNowWordOfState evmGuy).toNat := by
    intro hbad
    exact hwrap (by simpa [evmGuy, hend] using hbad)
  have hEndCheck :
      evalExpr? config frameEnd evmGuy (.binary .ge (.var "end_") now48) =
        .ok (.bool true) := by
    simpa [frameEnd, localsEnd, evmGuy, hend] using
      flapperKickEndCheckedGuard_eval_true evmGuy lot bid fillNew idWord hwrap'
  have hEndRhs :
      evalExpr? config frameEnd evmGuy (.var "end_") =
        .ok (.int (Int.ofNat endWord.toNat)) := by
    exact flapperKickEnd_eval evmGuy lot bid fillNew idWord endWord
  have hEndClean : UInt256.land endWord flapperUint48Mask = endWord := by
    rw [hend]
    simpa [flapperKickNewEndWordOfState] using
      flapperUint48Mask_clean_right_file
        (flapperKickTimestampWordOfState evmGuy + flapperKickTauWordOfState evmGuy)
  have hAssignEnd :
      assignStorageRef? config frameEnd evmGuy .storage (bidsF (.var "id") "end")
          (.int (Int.ofNat endWord.toNat)) =
        .ok (frameEnd, evmEnd) := by
    simpa [frameEnd, localsEnd, evmEnd, flapperKickSourceAfterEnd, evmGuy] using
      flapperKickAssignEnd evmGuy lot bid fillNew idWord endWord hEndClean
  have hblock :
      ExecBlock config frame0 evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)),
          .letDecl "fillNew" (some uint256) (add256 (.storage fillRef) (.var "lot")),
          .require (.binary .ge (.var "fillNew") (.storage fillRef)),
          .assign .storage fillRef (.var "fillNew"),
          .require (.binary .le (.storage fillRef) (.storage lidRef)),
          .letDecl "id" (some uint256) (add256 (.storage kicksRef) (.intLit 1)),
          .require (.binary .ge (.var "id") (.storage kicksRef)),
          .assign .storage kicksRef (.var "id"),
          .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
          .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
          .assign .storage (bidsF (.var "id") "guy") sender,
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))),
          .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        (.ok frameEnd evmEnd) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hAuthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hKicksGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetFill) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hFillCheck) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hFillRhs hAssignFill) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hFillLidGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetId) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hIdCheck) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hIdRhs hAssignKicks) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hBidRhs hAssignBid) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hLotRhs hAssignLot) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hSenderRhs hAssignGuy) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetEnd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hEndCheck) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hEndRhs hAssignEnd) ExecBlock.nil
  simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
    locals0, frame0, localsFill, frameFill, localsId, frameId, localsEnd, frameEnd,
    evmFill, evmKicks, evmBid, evmLot, evmGuy, evmEnd] using hblock

theorem flapperKickBodyRevertsAuth (evm : EVM.State) (lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let locals := flapperKickLocals lot bid
  let frame : Frame := { contract := contract, locals := locals }
  have hAuthGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool false) := by
    exact flapperRelyAuthGuard_false evm locals
      (by simp [locals, flapperKickLocals]) hauth
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      locals, frame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hAuthGuard) :
        ExecBlock config frame evm
          (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
            .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
            [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
              .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
            checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
            [ .assign .storage fillRef (.var "fillNew"),
              .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
            checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
            [ .assign .storage kicksRef (.var "id"),
              .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
              .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
              .assign .storage (bidsF (.var "id") "guy") sender ] ++
            checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
            checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, thisAddr, .var "lot"] "_moveRet" ++
            [ .return [.var "id"] ])
          .reverted)

theorem flapperKickBodyRevertsLive (evm : EVM.State) (lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let locals := flapperKickLocals lot bid
  let frame : Frame := { contract := contract, locals := locals }
  have hAuthGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals
      (by simp [locals, flapperKickLocals]) hauth
  have hLiveGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool false) := by
    exact flapperKickLiveGuard_eval_false evm locals
      (by simp [locals, flapperKickLocals]) hlive
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      locals, frame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hAuthGuard) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hLiveGuard) :
        ExecBlock config frame evm
          ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
            checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
            [ .assign .storage fillRef (.var "fillNew"),
              .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
            checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
            [ .assign .storage kicksRef (.var "id"),
              .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
              .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
              .assign .storage (bidsF (.var "id") "guy") sender ] ++
            checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
            checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, thisAddr, .var "lot"] "_moveRet" ++
            [ .return [.var "id"] ])
          .reverted)

theorem flapperKickBodyRevertsKicks (evm : EVM.State) (lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      ¬ (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let locals := flapperKickLocals lot bid
  let frame : Frame := { contract := contract, locals := locals }
  have hAuthGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals
      (by simp [locals, flapperKickLocals]) hauth
  have hLiveGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperKickLiveGuard_eval_true evm locals
      (by simp [locals, flapperKickLocals]) hlive
  have hKicksGuard :
      evalExpr? config frame evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
          .ok (.bool false) := by
    exact flapperKickKicksGuard_eval_false evm locals
      (by simp [locals, flapperKickLocals]) hkicks
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      locals, frame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hAuthGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) <|
            ExecBlock.consRevert (ExecStmt.requireFalse hKicksGuard) :
        ExecBlock config frame evm
          ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
            checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
            [ .assign .storage fillRef (.var "fillNew"),
              .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
            checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
            [ .assign .storage kicksRef (.var "id"),
              .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
              .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
              .assign .storage (bidsF (.var "id") "guy") sender ] ++
            checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
            checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, thisAddr, .var "lot"] "_moveRet" ++
            [ .return [.var "id"] ])
          .reverted)

theorem flapperKickBodyRevertsFillOverflow (evm : EVM.State) (lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hover : UInt256.size ≤ (flapperKickFillWordOfState evm).toNat + lot.toNat) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let locals := flapperKickLocals lot bid
  let frame : Frame := { contract := contract, locals := locals }
  have hAuthGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals
      (by simp [locals, flapperKickLocals]) hauth
  have hLiveGuard :
      evalExpr? config frame evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperKickLiveGuard_eval_true evm locals
      (by simp [locals, flapperKickLocals]) hlive
  have hKicksGuard :
      evalExpr? config frame evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
          .ok (.bool true) := by
    exact flapperKickKicksGuard_eval_true evm locals
      (by simp [locals, flapperKickLocals]) hkicks
  have hLetFill :
      evalExpr? config frame evm (add256 (.storage fillRef) (.var "lot")) =
        .revert := by
    exact flapperKickFillAdd_eval_revert evm lot bid hover
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      locals, frame] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hAuthGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) <|
            ExecBlock.consNormal (ExecStmt.requireTrue hKicksGuard) <|
              ExecBlock.consRevert (ExecStmt.letDeclRevert hLetFill) :
        ExecBlock config frame evm
          ([ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)),
            .letDecl "fillNew" (some uint256) (add256 (.storage fillRef) (.var "lot")) ] ++
            [ .require (.binary .ge (.var "fillNew") (.storage fillRef)),
              .assign .storage fillRef (.var "fillNew"),
              .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
            checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
            [ .assign .storage kicksRef (.var "id"),
              .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
              .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
              .assign .storage (bidsF (.var "id") "guy") sender ] ++
            checkedAdd48Into "end_" now48 (.storage tauRef) ++
            [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
            checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
              [sender, thisAddr, .var "lot"] "_moveRet" ++
            [ .return [.var "id"] ])
          .reverted)

theorem flapperKickPrefixAfterFillOk (evm : EVM.State) (lot bid fillNew : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := flapperKickLocals lot bid } evm
      (nonpayable ++ auth ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
        checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
        [ .assign .storage fillRef (.var "fillNew") ])
      (.ok { contract := contract, locals := flapperKickLocalsFillNew lot bid fillNew }
        (flapperKickSourceAfterFill evm fillNew)) := by
  let locals0 := flapperKickLocals lot bid
  let frame0 : Frame := { contract := contract, locals := locals0 }
  let localsFill := flapperKickLocalsFillNew lot bid fillNew
  let frameFill : Frame := { contract := contract, locals := localsFill }
  let evmFill := flapperKickSourceAfterFill evm fillNew
  have hAuthGuard :
      evalExpr? config frame0 evm
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals0
      (by simp [locals0, flapperKickLocals]) hauth
  have hLiveGuard :
      evalExpr? config frame0 evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) := by
    exact flapperKickLiveGuard_eval_true evm locals0
      (by simp [locals0, flapperKickLocals]) hlive
  have hKicksGuard :
      evalExpr? config frame0 evm
        (.binary .lt (.storage kicksRef) (.intLit maxUint256)) =
          .ok (.bool true) := by
    exact flapperKickKicksGuard_eval_true evm locals0
      (by simp [locals0, flapperKickLocals]) hkicks
  have hLetFill :
      evalExpr? config frame0 evm (add256 (.storage fillRef) (.var "lot")) =
        .ok (.int (Int.ofNat fillNew.toNat)) := by
    rw [hfillNew]
    exact flapperKickFillAdd_eval_ok evm lot bid hfillFit
  have hFillCheck :
      evalExpr? config frameFill evm
        (.binary .ge (.var "fillNew") (.storage fillRef)) =
          .ok (.bool true) := by
    simpa [frameFill, localsFill] using
      flapperKickFillCheckedGuard_eval_true evm lot bid fillNew hfillNew hfillFit
  have hFillRhs :
      evalExpr? config frameFill evm (.var "fillNew") =
        .ok (.int (Int.ofNat fillNew.toNat)) := by
    exact flapperKickFillNew_eval evm lot bid fillNew
  have hAssignFill :
      assignStorageRef? config frameFill evm .storage fillRef
          (.int (Int.ofNat fillNew.toNat)) =
        .ok (frameFill, evmFill) := by
    simpa [frameFill, localsFill, evmFill, flapperKickSourceAfterFill] using
      flapperKickAssignFill evm lot bid fillNew
  have hblock :
      ExecBlock config frame0 evm
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)),
          .letDecl "fillNew" (some uint256) (add256 (.storage fillRef) (.var "lot")),
          .require (.binary .ge (.var "fillNew") (.storage fillRef)),
          .assign .storage fillRef (.var "fillNew") ]
        (.ok frameFill evmFill) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hAuthGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hLiveGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hKicksGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetFill) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hFillCheck) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hFillRhs hAssignFill) ExecBlock.nil
  simpa [nonpayable, auth, checkedAddUintInto, locals0, frame0, localsFill, frameFill,
    evmFill] using hblock

theorem flapperKickBodyRevertsLid (evm : EVM.State) (lot bid fillNew : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size)
    (hlid :
      ¬ (flapperKickFillWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat ≤
        (flapperKickLidWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let localsFill := flapperKickLocalsFillNew lot bid fillNew
  let frameFill : Frame := { contract := contract, locals := localsFill }
  let evmFill := flapperKickSourceAfterFill evm fillNew
  have hpref :
      ExecBlock config
        { contract := contract, locals := flapperKickLocals lot bid } evm
        (nonpayable ++ auth ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
          checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
          [ .assign .storage fillRef (.var "fillNew") ])
        (.ok frameFill evmFill) := by
    simpa [frameFill, localsFill, evmFill] using
      flapperKickPrefixAfterFillOk evm lot bid fillNew hwv hauth hlive hkicks
        hfillNew hfillFit
  have hguard :
      evalExpr? config frameFill evmFill
        (.binary .le (.storage fillRef) (.storage lidRef)) =
          .ok (.bool false) := by
    exact flapperKickFillLidGuard_eval_false evmFill localsFill
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simpa [evmFill] using hlid)
  have htail :
      ExecBlock config frameFill evmFill
        (.require (.binary .le (.storage fillRef) (.storage lidRef)) ::
          checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
          [ .assign .storage kicksRef (.var "id"),
            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
            .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
            .assign .storage (bidsF (.var "id") "guy") sender ] ++
          checkedAdd48Into "end_" now48 (.storage tauRef) ++
          [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, thisAddr, .var "lot"] "_moveRet" ++
          [ .return [.var "id"] ])
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      checkedExternalCallStmts, frameFill, localsFill, evmFill] using
      execBlock_append hpref htail

theorem flapperKickPrefixAfterEndLetOk (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size)
    (hfillLid :
      (flapperKickFillWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat ≤
        (flapperKickLidWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat)
    (hid :
      idWord = flapperKickIdWordOfState (flapperKickSourceAfterFill evm fillNew))
    (hidFit :
      (flapperKickKicksWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat + 1 <
        UInt256.size)
    (hend :
      endWord =
        flapperKickNewEndWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord)) :
    ExecBlock config
      { contract := contract, locals := flapperKickLocals lot bid } evm
      (nonpayable ++ auth ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
        checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
        [ .assign .storage fillRef (.var "fillNew"),
          .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
        checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
        [ .assign .storage kicksRef (.var "id"),
          .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
          .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
          .assign .storage (bidsF (.var "id") "guy") sender,
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))) ])
      (.ok
        { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord }
        (flapperKickSourceAfterGuy evm lot bid fillNew idWord)) := by
  let locals0 := flapperKickLocals lot bid
  let frame0 : Frame := { contract := contract, locals := locals0 }
  let localsFill := flapperKickLocalsFillNew lot bid fillNew
  let frameFill : Frame := { contract := contract, locals := localsFill }
  let evmFill := flapperKickSourceAfterFill evm fillNew
  let localsId := flapperKickLocalsId lot bid fillNew idWord
  let frameId : Frame := { contract := contract, locals := localsId }
  let evmKicks := flapperKickSourceAfterKicks evm fillNew idWord
  let evmBid := flapperKickSourceAfterBid evm bid fillNew idWord
  let evmLot := flapperKickSourceAfterLot evm lot bid fillNew idWord
  let evmGuy := flapperKickSourceAfterGuy evm lot bid fillNew idWord
  let localsEnd := flapperKickLocalsEnd lot bid fillNew idWord endWord
  let frameEnd : Frame := { contract := contract, locals := localsEnd }
  have hprefFill :
      ExecBlock config frame0 evm
        (nonpayable ++ auth ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
          checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
          [ .assign .storage fillRef (.var "fillNew") ])
        (.ok frameFill evmFill) := by
    simpa [frame0, locals0, frameFill, localsFill, evmFill] using
      flapperKickPrefixAfterFillOk evm lot bid fillNew hwv hauth hlive hkicks
        hfillNew hfillFit
  have hFillLidGuard :
      evalExpr? config frameFill evmFill
        (.binary .le (.storage fillRef) (.storage lidRef)) =
          .ok (.bool true) := by
    exact flapperKickFillLidGuard_eval_true evmFill localsFill
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simp [localsFill, flapperKickLocalsFillNew, flapperKickLocals])
      (by simpa [evmFill] using hfillLid)
  have hLetId :
      evalExpr? config frameFill evmFill (add256 (.storage kicksRef) (.intLit 1)) =
        .ok (.int (Int.ofNat idWord.toNat)) := by
    exact flapperKickIdAdd_eval_ok evmFill lot bid fillNew idWord
      (by simpa [evmFill] using hid) (by simpa [evmFill] using hidFit)
  have hIdCheck :
      evalExpr? config frameId evmFill (.binary .ge (.var "id") (.storage kicksRef)) =
        .ok (.bool true) := by
    exact flapperKickIdCheckedGuard_eval_true evmFill lot bid fillNew idWord
      (by simpa [evmFill] using hid) (by simpa [evmFill] using hidFit)
  have hIdRhs :
      evalExpr? config frameId evmFill (.var "id") =
        .ok (.int (Int.ofNat idWord.toNat)) := by
    exact flapperKickId_eval evmFill lot bid fillNew idWord
  have hAssignKicks :
      assignStorageRef? config frameId evmFill .storage kicksRef
          (.int (Int.ofNat idWord.toNat)) =
        .ok (frameId, evmKicks) := by
    simpa [frameId, localsId, evmKicks, flapperKickSourceAfterKicks, evmFill] using
      flapperKickAssignKicks evmFill lot bid fillNew idWord
  have hBidRhs :
      evalExpr? config frameId evmKicks (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    exact flapperKickBid_eval_id evmKicks lot bid fillNew idWord
  have hAssignBid :
      assignStorageRef? config frameId evmKicks .storage (bidsF (.var "id") "bid")
          (.int (Int.ofNat bid.toNat)) =
        .ok (frameId, evmBid) := by
    simpa [frameId, localsId, evmBid, flapperKickSourceAfterBid, evmKicks] using
      flapperKickAssignBid evmKicks lot bid fillNew idWord
  have hLotRhs :
      evalExpr? config frameId evmBid (.var "lot") =
        .ok (.int (Int.ofNat lot.toNat)) := by
    exact flapperKickLot_eval_id evmBid lot bid fillNew idWord
  have hAssignLot :
      assignStorageRef? config frameId evmBid .storage (bidsF (.var "id") "lot")
          (.int (Int.ofNat lot.toNat)) =
        .ok (frameId, evmLot) := by
    simpa [frameId, localsId, evmLot, flapperKickSourceAfterLot, evmBid] using
      flapperKickAssignLot evmBid lot bid fillNew idWord
  have hSenderRhs :
      evalExpr? config frameId evmLot sender =
        .ok (.address evmLot.executionEnv.source) := by
    simp [frameId, sender, evalExpr?, envValue, pure]
  have hAssignGuy :
      assignStorageRef? config frameId evmLot .storage (bidsF (.var "id") "guy")
          (.address evmLot.executionEnv.source) =
        .ok (frameId, evmGuy) := by
    simpa [frameId, localsId, evmGuy, flapperKickSourceAfterGuy, evmLot] using
      flapperKickAssignGuy evmLot lot bid fillNew idWord
  have hLetEnd :
      evalExpr? config frameId evmGuy (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat endWord.toNat)) := by
    rw [hend]
    exact flapperKickNewEnd_eval evmGuy localsId
      (by simp [localsId, flapperKickLocalsId, flapperKickLocalsFillNew, flapperKickLocals])
  have htail :
      ExecBlock config frameFill evmFill
        (.require (.binary .le (.storage fillRef) (.storage lidRef)) ::
          checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
          [ .assign .storage kicksRef (.var "id"),
            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
            .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
            .assign .storage (bidsF (.var "id") "guy") sender,
            .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))) ])
        (.ok frameEnd evmGuy) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hFillLidGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hLetId) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hIdCheck) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hIdRhs hAssignKicks) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hBidRhs hAssignBid) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hLotRhs hAssignLot) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hSenderRhs hAssignGuy) ?_
    exact ExecBlock.consNormal (ExecStmt.letDecl hLetEnd) ExecBlock.nil
  have hblock := execBlock_append hprefFill htail
  simpa [nonpayable, auth, checkedAddUintInto, checkedAdd48Into, locals0, frame0,
    localsFill, frameFill, localsId, frameId, localsEnd, frameEnd, evmFill, evmKicks,
    evmBid, evmLot, evmGuy] using hblock

theorem flapperKickBodyRevertsEndOverflow (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size)
    (hfillLid :
      (flapperKickFillWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat ≤
        (flapperKickLidWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat)
    (hid :
      idWord = flapperKickIdWordOfState (flapperKickSourceAfterFill evm fillNew))
    (hidFit :
      (flapperKickKicksWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat + 1 <
        UInt256.size)
    (hend :
      endWord =
        flapperKickNewEndWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord))
    (hwrap :
      endWord.toNat <
        (flapperKickNowWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord)).toNat) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let evmGuy := flapperKickSourceAfterGuy evm lot bid fillNew idWord
  let localsEnd := flapperKickLocalsEnd lot bid fillNew idWord endWord
  let frameEnd : Frame := { contract := contract, locals := localsEnd }
  have hpref :
      ExecBlock config
        { contract := contract, locals := flapperKickLocals lot bid } evm
        (nonpayable ++ auth ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
          checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
          [ .assign .storage fillRef (.var "fillNew"),
            .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
          checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
          [ .assign .storage kicksRef (.var "id"),
            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
            .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
            .assign .storage (bidsF (.var "id") "guy") sender,
            .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))) ])
        (.ok frameEnd evmGuy) := by
    simpa [frameEnd, localsEnd, evmGuy] using
      flapperKickPrefixAfterEndLetOk evm lot bid fillNew idWord endWord hwv hauth
        hlive hkicks hfillNew hfillFit hfillLid hid hidFit hend
  have hwrap' :
      (flapperKickNewEndWordOfState evmGuy).toNat <
        (flapperKickNowWordOfState evmGuy).toNat := by
    simpa [evmGuy, hend] using hwrap
  have hguard :
      evalExpr? config frameEnd evmGuy (.binary .ge (.var "end_") now48) =
        .ok (.bool false) := by
    simpa [frameEnd, localsEnd, evmGuy, hend] using
      flapperKickEndCheckedGuard_eval_false evmGuy lot bid fillNew idWord hwrap'
  have htail :
      ExecBlock config frameEnd evmGuy
        (.require (.binary .ge (.var "end_") now48) ::
          [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ] ++
          checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, thisAddr, .var "lot"] "_moveRet" ++
          [ .return [.var "id"] ])
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      checkedExternalCallStmts, frameEnd, localsEnd, evmGuy] using
      execBlock_append hpref htail

theorem flapperKickExtCodeSizeWord_eval (evm : EVM.State) (targetWord : UInt256) :
    EVM.Word.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
          (fun acc => acc.code.size)) =
      extCodeSizeWord evm.accountMap targetWord := by
  unfold extCodeSizeWord State.lookupAccount
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find? (AccountAddress.ofNat targetWord.toNat) <;> rfl

theorem flapperKickExtGuard_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none)
    (hcodeSize : extCodeSizeWord evm.accountMap (flapperKickVatWordOfState evm) ≠
      UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let targetWord := flapperKickVatWordOfState evm
  have hreceiver := flapperKickVat_eval evm locals hbase
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperKickExtCodeSizeWord_eval evm targetWord
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

theorem flapperKickExtGuard_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none)
    (hcodeSize : extCodeSizeWord evm.accountMap (flapperKickVatWordOfState evm) =
      UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let targetWord := flapperKickVatWordOfState evm
  have hreceiver := flapperKickVat_eval evm locals hbase
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperKickExtCodeSizeWord_eval evm targetWord
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

theorem flapperKickArgs_eval (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256) :
    evalExprs? config
      { contract := contract, locals := flapperKickLocalsEnd lot bid fillNew idWord endWord } evm
      [sender, thisAddr, .var "lot"] =
      .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
        .int (Int.ofNat lot.toNat)] := by
  have hLotEval := flapperKickLot_eval_end evm lot bid fillNew idWord endWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLotEval
  simp only [evalExprs?, evalExpr?, sender, thisAddr, envValue, EvalResult.bind, bind, pure]
  rw [hLotEval]

theorem flapperKickBodyRevertsNoCode (evm : EVM.State)
    (lot bid fillNew idWord endWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hlive : flapperKickLiveWordOfState evm = UInt256.ofNat 1)
    (hkicks :
      (flapperKickKicksWordOfState evm).toNat <
        (UInt256.lnot (UInt256.ofNat 0)).toNat)
    (hfillNew : fillNew = flapperKickFillNewWordOfState evm lot)
    (hfillFit :
      (flapperKickFillWordOfState evm).toNat + lot.toNat < UInt256.size)
    (hfillLid :
      (flapperKickFillWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat ≤
        (flapperKickLidWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat)
    (hid :
      idWord = flapperKickIdWordOfState (flapperKickSourceAfterFill evm fillNew))
    (hidFit :
      (flapperKickKicksWordOfState (flapperKickSourceAfterFill evm fillNew)).toNat + 1 <
        UInt256.size)
    (hend :
      endWord =
        flapperKickNewEndWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord))
    (hwrap :
      ¬ endWord.toNat <
        (flapperKickNowWordOfState
          (flapperKickSourceAfterGuy evm lot bid fillNew idWord)).toNat)
    (hcodeSize :
      extCodeSizeWord (flapperKickSourceAfterEnd evm lot bid fillNew idWord endWord).accountMap
          (flapperKickVatWordOfState
            (flapperKickSourceAfterEnd evm lot bid fillNew idWord endWord)) =
        UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperKickLocals lot bid)
      kickTransition.body .reverted := by
  let localsEnd := flapperKickLocalsEnd lot bid fillNew idWord endWord
  let frameEnd : Frame := { contract := contract, locals := localsEnd }
  let evmEnd := flapperKickSourceAfterEnd evm lot bid fillNew idWord endWord
  have hpref :
      ExecBlock config
        { contract := contract, locals := flapperKickLocals lot bid } evm
        (nonpayable ++ auth ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .lt (.storage kicksRef) (.intLit maxUint256)) ] ++
          checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
          [ .assign .storage fillRef (.var "fillNew"),
            .require (.binary .le (.storage fillRef) (.storage lidRef)) ] ++
          checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
          [ .assign .storage kicksRef (.var "id"),
            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
            .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
            .assign .storage (bidsF (.var "id") "guy") sender ] ++
          checkedAdd48Into "end_" now48 (.storage tauRef) ++
          [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ])
        (.ok frameEnd evmEnd) := by
    simpa [frameEnd, localsEnd, evmEnd] using
      flapperKickPrefixOk evm lot bid fillNew idWord endWord hwv hauth hlive
        hkicks hfillNew hfillFit hfillLid hid hidFit hend hwrap
  have hguard :
      evalExpr? config frameEnd evmEnd
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    exact flapperKickExtGuard_false evmEnd localsEnd
      (by simp [localsEnd, flapperKickLocalsEnd, flapperKickLocalsId,
        flapperKickLocalsFillNew, flapperKickLocals])
      (by simpa [evmEnd] using hcodeSize)
  have htailExternal :
      ExecBlock config frameEnd evmEnd
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet")
        .reverted := by
    simpa [checkedExternalCallStmts, frameEnd, localsEnd] using
      checkedExternalCallNoCode (cfg := config) (C := contract)
        (evm := evmEnd) (locals := localsEnd) (receiver := .storage vatRef)
        (name := "move") (sendVal := 0)
        (args := [sender, thisAddr, .var "lot"]) (retVar := "_moveRet") hguard
  have htail :
      ExecBlock config frameEnd evmEnd
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, thisAddr, .var "lot"] "_moveRet" ++
          [ .return [.var "id"] ])
        .reverted := by
    exact execBlock_append_term htailExternal (by intro f e h; cases h)
  exact ExecFuncBody.execBlockRevert <| by
    simpa [kickTransition, nonpayable, auth, checkedAddUintInto, checkedAdd48Into,
      checkedExternalCallStmts, frameEnd, localsEnd, evmEnd] using
      execBlock_append hpref htail

theorem flapperKickStorageRead_one_present {owner : AccountAddress}
    {σ : AccountMap} {slot : UInt256}
    (h : storageRead owner σ slot = UInt256.ofNat 1) :
    ∃ account, σ.find? owner = some account := by
  rw [storageRead_eq] at h
  cases hfind : σ.find? owner with
  | none =>
      simp [hfind, Option.option] at h
      have hne : (default : UInt256) ≠ UInt256.ofNat 1 := by decide
      exact False.elim (hne h)
  | some account =>
      exact ⟨account, rfl⟩

theorem flapperKickStorageLoad_eq_of_stateRel
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_world σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      I (cA, σ_world) evm)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      storageRead I.codeOwner σ_world slot := by
  have hmap :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_world σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        Solm.EVM.storageLoad evm I.codeOwner slot := by
    exact storageLoad_accountMapEquiv
      (evm1 := initState cA gh bl σ_world σ₀ (Sat256.ofUInt256 g) A I)
      (evm2 := evm)
      (by simpa [initState] using hState.accounts)
      I.codeOwner slot
  have hread :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_world σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        storageRead I.codeOwner σ_world slot := by
    simp [initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, storageRead_eq]
  have howner : evm.executionEnv.codeOwner = I.codeOwner := by
    rw [hState.env]
  rw [howner]
  exact hmap.symm.trans hread

theorem flapperKickLocalsEnd_vat_none
    (lot bid fillNew idWord endWord : UInt256) :
    (flapperKickLocalsEnd lot bid fillNew idWord endWord).get? "vat" = none := by
  simp [flapperKickLocalsEnd, flapperKickLocalsId, flapperKickLocalsFillNew,
    flapperKickLocals]

set_option maxHeartbeats 1000000 in
theorem flapperKickBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 8))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨796⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hselLit :
      ((⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) == I.calldata.extract 0 4) =
        true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I
    (⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_kick (cd := I.calldata) hselLit
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec := flapperDecode_kick_ok (I := I) hsz68
    let s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let lot := flapperKickLotWord I
    let bid := flapperKickBidWord I
    have hStateInit : CallStateRel s0 I (cA, σ_evm) evmSolm := by
      simpa [s0, evmSolm] using
        (CallStateRel.initState
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
          (A := A) (I := I) hAccounts)
    have hAuthLoadEq :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) =
          storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
      simpa [evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (flapperRelyAuthSlot I)
    have hLiveLoadEq :
        flapperKickLiveWordOfState evmSolm =
          storageRead I.codeOwner σ_evm (UInt256.ofNat 7) := by
      simpa [flapperKickLiveWordOfState, evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 7)
    have hKicksLoadEq :
        flapperKickKicksWordOfState evmSolm = flapperKickKicksWord σ_evm I := by
      simpa [flapperKickKicksWordOfState, flapperKickKicksWord, evmSolm,
        initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 6)
    have hFillLoadEq :
        flapperKickFillWordOfState evmSolm = flapperKickFillWord σ_evm I := by
      simpa [flapperKickFillWordOfState, flapperKickFillWord, evmSolm,
        initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 9)
    have hLidLoadEq :
        flapperKickLidWordOfState evmSolm = flapperKickLidWord σ_evm I := by
      simpa [flapperKickLidWordOfState, flapperKickLidWord, evmSolm,
        initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 8)
    by_cases hauthEvm :
        storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) = UInt256.ofNat 1
    · have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) = UInt256.ofNat 1 := by
        rw [hAuthLoadEq]
        exact hauthEvm
      by_cases hliveEvm :
          storageRead I.codeOwner σ_evm (UInt256.ofNat 7) = UInt256.ofNat 1
      · have hliveSolm : flapperKickLiveWordOfState evmSolm = UInt256.ofNat 1 := by
          rw [hLiveLoadEq]
          exact hliveEvm
        by_cases hkicksEvm :
            (storageRead I.codeOwner σ_evm (UInt256.ofNat 6)).toNat <
              (UInt256.lnot (UInt256.ofNat 0)).toNat
        · have hkicksSolm :
              (flapperKickKicksWordOfState evmSolm).toNat <
                (UInt256.lnot (UInt256.ofNat 0)).toNat := by
            simpa [hKicksLoadEq, flapperKickKicksWord] using hkicksEvm
          by_cases hfillFit :
              (flapperKickFillWordOfState evmSolm).toNat + lot.toNat <
                UInt256.size
          · let fillNew := flapperKickFillNewWord σ_evm I
            let evmFill := flapperKickSourceAfterFill evmSolm fillNew
            have hfillNew :
                fillNew = flapperKickFillNewWordOfState evmSolm lot := by
              simpa [fillNew, flapperKickFillNewWord, flapperKickFillNewWordOfState,
                hFillLoadEq, lot]
            have hfillNoWrapEvm :
                ¬ (flapperKickFillNewWord σ_evm I).toNat <
                  (flapperKickFillWord σ_evm I).toNat := by
              have hfitEvm :
                  (flapperKickFillWord σ_evm I).toNat + lot.toNat < UInt256.size := by
                simpa [hFillLoadEq] using hfillFit
              simpa [flapperKickFillNewWord, lot] using
                flapperKickAddNoWrap_not_lt_left (flapperKickFillWord σ_evm I) lot
                  hfitEvm
            have hStateFill : CallStateRel s0 I
                (cA, flapperKickAfterFillWorld σ_evm I) evmFill := by
              have h := hStateInit.storageStore_codeOwner (UInt256.ofNat 9) fillNew
              simpa [s0, evmSolm, evmFill, flapperKickSourceAfterFill,
                flapperKickAfterFillWorld, fillNew, storageWrite_eq] using h
            have haccEvm :
                ∃ account, σ_evm.find? I.codeOwner = some account :=
              flapperKickStorageRead_one_present hauthEvm
            have hreadFillAfterEvm :
                storageRead I.codeOwner (flapperKickAfterFillWorld σ_evm I)
                    (UInt256.ofNat 9) = fillNew := by
              rcases haccEvm with ⟨account, haccount⟩
              simpa [flapperKickAfterFillWorld, fillNew, storageWrite_eq] using
                (storageRead_storageWrite_same_of_present
                  (owner := I.codeOwner) (σ := σ_evm) (account := account)
                  (slot := UInt256.ofNat 9) (value := fillNew) haccount)
            have hFillAfterEq :
                flapperKickFillWordOfState evmFill = fillNew := by
              have hload :=
                flapperKickStorageLoad_eq_of_stateRel (g := g) hStateFill
                  (UInt256.ofNat 9)
              simpa [flapperKickFillWordOfState, hreadFillAfterEvm] using hload
            have hreadLidAfterEvm :
                storageRead I.codeOwner (flapperKickAfterFillWorld σ_evm I)
                    (UInt256.ofNat 8) =
                  flapperKickLidWord σ_evm I := by
              simpa [flapperKickAfterFillWorld, flapperKickLidWord, storageWrite_eq]
                using
                  (storageRead_storageWrite_ne I.codeOwner σ_evm
                    (readSlot := UInt256.ofNat 8) (writeSlot := UInt256.ofNat 9)
                    (value := flapperKickFillNewWord σ_evm I) (by decide))
            have hLidAfterEq :
                flapperKickLidWordOfState evmFill = flapperKickLidWord σ_evm I := by
              have hload :=
                flapperKickStorageLoad_eq_of_stateRel (g := g) hStateFill
                  (UInt256.ofNat 8)
              simpa [flapperKickLidWordOfState, hreadLidAfterEvm] using hload
            by_cases hlidEvm :
                (flapperKickFillNewWord σ_evm I).toNat ≤
                  (flapperKickLidWord σ_evm I).toNat
            · have hfillLidSolm :
                  (flapperKickFillWordOfState evmFill).toNat ≤
                    (flapperKickLidWordOfState evmFill).toNat := by
                simpa [hFillAfterEq, hLidAfterEq, fillNew] using hlidEvm
              let idWord := flapperKickIdWord σ_evm I
              let evmKicks := flapperKickSourceAfterKicks evmSolm fillNew idWord
              let evmBid := flapperKickSourceAfterBid evmSolm bid fillNew idWord
              let evmLot := flapperKickSourceAfterLot evmSolm lot bid fillNew idWord
              let evmGuy := flapperKickSourceAfterGuy evmSolm lot bid fillNew idWord
              have hreadKicksAfterEvm :
                  storageRead I.codeOwner (flapperKickAfterFillWorld σ_evm I)
                      (UInt256.ofNat 6) =
                    flapperKickKicksWord σ_evm I := by
                simpa [flapperKickAfterFillWorld, flapperKickKicksWord,
                  storageWrite_eq] using
                    (storageRead_storageWrite_ne I.codeOwner σ_evm
                      (readSlot := UInt256.ofNat 6) (writeSlot := UInt256.ofNat 9)
                      (value := flapperKickFillNewWord σ_evm I) (by decide))
              have hKicksAfterEq :
                  flapperKickKicksWordOfState evmFill =
                    flapperKickKicksWord σ_evm I := by
                have hload :=
                  flapperKickStorageLoad_eq_of_stateRel (g := g) hStateFill
                    (UInt256.ofNat 6)
                simpa [flapperKickKicksWordOfState, hreadKicksAfterEvm] using hload
              have hid :
                  idWord = flapperKickIdWordOfState evmFill := by
                simp [idWord, flapperKickIdWord, flapperKickIdWordOfState,
                  hKicksAfterEq]
              have hidFit :
                  (flapperKickKicksWordOfState evmFill).toNat + 1 <
                    UInt256.size := by
                have hmax :
                    (UInt256.lnot (UInt256.ofNat 0)).toNat =
                      UInt256.size - 1 := by
                  native_decide
                have hk :
                    (flapperKickKicksWord σ_evm I).toNat <
                      UInt256.size - 1 := by
                  simpa [flapperKickKicksWord, hmax] using hkicksEvm
                have hsizePos : 0 < UInt256.size := by
                  native_decide
                have hk' :
                    (flapperKickKicksWord σ_evm I).toNat + 1 <
                      UInt256.size := by
                  omega
                simpa [hKicksAfterEq] using hk'
              have hStateKicks : CallStateRel s0 I
                  (cA, flapperKickAfterKicksWorld σ_evm I) evmKicks := by
                have h := hStateFill.storageStore_codeOwner (UInt256.ofNat 6) idWord
                simpa [s0, evmKicks, evmFill, flapperKickSourceAfterKicks,
                  flapperKickAfterKicksWorld, idWord, fillNew, storageWrite_eq] using h
              have hStateBid : CallStateRel s0 I
                  (cA, flapperKickAfterBidWorld σ_evm I) evmBid := by
                have h := hStateKicks.storageStore_codeOwner
                  (flapperKickBaseSlot idWord) bid
                simpa [s0, evmBid, evmKicks, flapperKickSourceAfterBid,
                  flapperKickAfterBidWorld, idWord, bid, storageWrite_eq] using h
              have hStateLot : CallStateRel s0 I
                  (cA, flapperKickAfterLotWorld σ_evm I) evmLot := by
                have h := hStateBid.storageStore_codeOwner
                  (flapperKickBaseSlot idWord + UInt256.ofNat 1) lot
                simpa [s0, evmLot, evmBid, flapperKickSourceAfterLot,
                  flapperKickAfterLotWorld, idWord, lot, storageWrite_eq] using h
              have hPackedLoadEqLot :
                  Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner
                      (flapperKickPackedSlot idWord) =
                    storageRead I.codeOwner (flapperKickAfterLotWorld σ_evm I)
                      (flapperKickPackedSlot idWord) := by
                exact flapperKickStorageLoad_eq_of_stateRel (g := g) hStateLot
                  (flapperKickPackedSlot idWord)
              have hGuyStoreWord :
                  setAddressOffset0Word
                      (Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner
                        (flapperKickPackedSlot idWord))
                      (UInt256.ofNat evmLot.executionEnv.source.val) =
                    flapperKickGuyWord σ_evm I := by
                rw [hPackedLoadEqLot]
                have hsrc : evmLot.executionEnv.source = I.source := by
                  rw [hStateLot.env]
                rw [hsrc]
                simpa [idWord] using (flapperKickGuyWord_eq_setAddress σ_evm I).symm
              have hStateGuy : CallStateRel s0 I
                  (cA, flapperKickAfterGuyWorld σ_evm I) evmGuy := by
                have h := hStateLot.storageStore_codeOwner
                  (flapperKickPackedSlot idWord) (flapperKickGuyWord σ_evm I)
                simpa [s0, evmGuy, evmLot, flapperKickSourceAfterGuy,
                  flapperKickAfterGuyWorld, idWord, hGuyStoreWord,
                  storageWrite_eq] using h
              have hTauLoadEqGuy :
                  Solm.EVM.storageLoad evmGuy evmGuy.executionEnv.codeOwner
                      (UInt256.ofNat 5) =
                    storageRead I.codeOwner (flapperKickAfterGuyWorld σ_evm I)
                      (UInt256.ofNat 5) := by
                exact flapperKickStorageLoad_eq_of_stateRel (g := g) hStateGuy
                  (UInt256.ofNat 5)
              have hTauEqGuy :
                  flapperKickTauWordOfState evmGuy =
                    flapperKickTauWord (flapperKickAfterGuyWorld σ_evm I) I := by
                unfold flapperKickTauWordOfState flapperKickTauWord
                rw [hTauLoadEqGuy]
              have hNowEqGuy :
                  flapperKickNowWordOfState evmGuy = flapperKickNowWord I := by
                simp [flapperKickNowWordOfState, flapperKickTimestampWordOfState,
                  flapperKickNowWord, flapperKickTimestampWord, hStateGuy.env]
              have hNewEndEqGuy :
                  flapperKickNewEndWordOfState evmGuy =
                    flapperKickNewEndWord (flapperKickAfterGuyWorld σ_evm I) I := by
                simp [flapperKickNewEndWordOfState, flapperKickNewEndWord,
                  flapperKickTimestampWordOfState, flapperKickTimestampWord,
                  hStateGuy.env, hTauEqGuy]
              let endWord :=
                flapperKickNewEndWord (flapperKickAfterGuyWorld σ_evm I) I
              have hend :
                  endWord = flapperKickNewEndWordOfState evmGuy := by
                simpa [endWord] using hNewEndEqGuy.symm
              by_cases hwrapEvm :
                  endWord.toNat < (flapperKickNowWord I).toNat
              · have hwrapSolm :
                    endWord.toNat < (flapperKickNowWordOfState evmGuy).toNat := by
                  simpa [hNowEqGuy] using hwrapEvm
                have hbody :
                    ExecTransitionBody config contract evmSolm
                      (flapperKickLocals lot bid) kickTransition.body .reverted := by
                  simpa [evmSolm, lot, bid, fillNew, evmFill, idWord, evmGuy,
                    endWord] using
                    flapperKickBodyRevertsEndOverflow evmSolm lot bid fillNew
                      idWord endWord
                      (by simp only [evmSolm, initState]; exact hwv)
                      hauthSolm hliveSolm hkicksSolm hfillNew hfillFit
                      (by simpa [evmFill] using hfillLidSolm)
                      (by simpa [evmFill] using hid)
                      (by simpa [evmFill] using hidFit)
                      (by simpa [evmGuy] using hend)
                      (by simpa [evmGuy] using hwrapSolm)
                exact (flapperX_kick_end_overflow_revert
                    (g := Sat256.ofUInt256 g) hsize hsz68 hperm hauthEvm
                    hliveEvm hkicksEvm hfillNoWrapEvm hlidEvm
                    (by simpa [endWord] using hwrapEvm) hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hwrapSolm :
                    ¬ endWord.toNat < (flapperKickNowWordOfState evmGuy).toNat := by
                  intro hbad
                  exact hwrapEvm (by simpa [hNowEqGuy] using hbad)
                let evmEnd :=
                  flapperKickSourceAfterEnd evmSolm lot bid fillNew idWord endWord
                have h4407 := flapperX_kick_after_end_ok
                  (g := Sat256.ofUInt256 g) hsize hsz68 hperm hauthEvm
                  hliveEvm hkicksEvm hfillNoWrapEvm hlidEvm
                  (by simpa [endWord] using hwrapEvm) hreach
                have hPackedLoadEqGuy :
                    Solm.EVM.storageLoad evmGuy evmGuy.executionEnv.codeOwner
                        (flapperKickPackedSlot idWord) =
                      storageRead I.codeOwner (flapperKickAfterGuyWorld σ_evm I)
                        (flapperKickPackedSlot idWord) := by
                  exact flapperKickStorageLoad_eq_of_stateRel (g := g) hStateGuy
                    (flapperKickPackedSlot idWord)
                let endStoreWord :=
                  flapperKickPackedEndWord
                    (storageRead I.codeOwner (flapperKickAfterGuyWorld σ_evm I)
                      (flapperKickPackedSlot idWord)) endWord
                have hStateEnd : CallStateRel s0 I
                    (cA, flapperKickAfterEndWorld σ_evm I) evmEnd := by
                  have h := hStateGuy.storageStore_codeOwner
                    (flapperKickPackedSlot idWord) endStoreWord
                  simpa [s0, evmEnd, evmGuy, flapperKickSourceAfterEnd,
                    flapperKickAfterEndWorld, endStoreWord, idWord, endWord,
                    hPackedLoadEqGuy, storageWrite_eq] using h
                have hVatLoadEqEnd :
                    Solm.EVM.storageLoad evmEnd evmEnd.executionEnv.codeOwner
                        (UInt256.ofNat 2) =
                      storageRead I.codeOwner (flapperKickAfterEndWorld σ_evm I)
                        (UInt256.ofNat 2) := by
                  exact flapperKickStorageLoad_eq_of_stateRel (g := g) hStateEnd
                    (UInt256.ofNat 2)
                have hVatWordEq :
                    flapperKickVatWordOfState evmEnd =
                      flapperKickVatWord (flapperKickAfterEndWorld σ_evm I) I := by
                  simp [flapperKickVatWordOfState, flapperKickVatWord, hVatLoadEqEnd]
                by_cases hcodeSize :
                    extCodeSizeWord (flapperKickAfterEndWorld σ_evm I)
                        (flapperKickVatWord (flapperKickAfterEndWorld σ_evm I) I) =
                      UInt256.ofNat 0
                · have hcodeSizeSolm :
                      extCodeSizeWord evmEnd.accountMap
                          (flapperKickVatWordOfState evmEnd) =
                        UInt256.ofNat 0 := by
                    have hmapCode := extCodeSizeWord_accountMapEquiv hStateEnd.accounts
                      (flapperKickVatWord (flapperKickAfterEndWorld σ_evm I) I)
                    exact (by
                      simpa [hVatWordEq] using hmapCode.symm.trans hcodeSize)
                  have hbody :
                      ExecTransitionBody config contract evmSolm
                        (flapperKickLocals lot bid) kickTransition.body .reverted := by
                    simpa [evmSolm, lot, bid, fillNew, evmFill, idWord, evmGuy,
                      evmEnd, endWord] using
                      flapperKickBodyRevertsNoCode evmSolm lot bid fillNew
                        idWord endWord
                        (by simp only [evmSolm, initState]; exact hwv)
                        hauthSolm hliveSolm hkicksSolm hfillNew hfillFit
                        (by simpa [evmFill] using hfillLidSolm)
                        (by simpa [evmFill] using hid)
                        (by simpa [evmFill] using hidFit)
                        (by simpa [evmGuy] using hend)
                        (by simpa [evmGuy] using hwrapSolm)
                        (by simpa [evmEnd] using hcodeSizeSolm)
                  exact (flapperX_kick_no_code_revert
                      (g := Sat256.ofUInt256 g) hcodeSize h4407)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hcodeSizeSolmNe :
                      extCodeSizeWord evmEnd.accountMap
                          (flapperKickVatWordOfState evmEnd) ≠
                        UInt256.ofNat 0 := by
                    intro hzero
                    apply hcodeSize
                    have hmapCode := extCodeSizeWord_accountMapEquiv hStateEnd.accounts
                      (flapperKickVatWord (flapperKickAfterEndWorld σ_evm I) I)
                    have hzeroVat :
                        extCodeSizeWord evmEnd.accountMap
                            (flapperKickVatWord
                              (flapperKickAfterEndWorld σ_evm I) I) =
                          UInt256.ofNat 0 := by
                      simpa [hVatWordEq] using hzero
                    exact hmapCode.trans hzeroVat
                  let localsEnd :=
                    flapperKickLocalsEnd lot bid fillNew idWord endWord
                  let frame0 : Frame :=
                    { contract := contract, locals := flapperKickLocals lot bid }
                  let frameEnd : Frame := { contract := contract, locals := localsEnd }
                  have hguardTrue :
                      evalExpr? config frameEnd evmEnd
                        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
                          .ok (.bool true) := by
                    simpa [frameEnd, localsEnd] using
                      flapperKickExtGuard_true evmEnd localsEnd
                        (by simpa [localsEnd] using
                          flapperKickLocalsEnd_vat_none lot bid fillNew idWord endWord)
                        hcodeSizeSolmNe
                  have hpref :
                      ExecBlock config frame0 evmSolm
                        (nonpayable ++ auth ++
                          [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                            .require (.binary .lt (.storage kicksRef)
                              (.intLit maxUint256)) ] ++
                          checkedAddUintInto "fillNew" (.storage fillRef) (.var "lot") ++
                          [ .assign .storage fillRef (.var "fillNew"),
                            .require (.binary .le (.storage fillRef)
                              (.storage lidRef)) ] ++
                          checkedAddUintInto "id" (.storage kicksRef) (.intLit 1) ++
                          [ .assign .storage kicksRef (.var "id"),
                            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
                            .assign .storage (bidsF (.var "id") "lot") (.var "lot"),
                            .assign .storage (bidsF (.var "id") "guy") sender ] ++
                          checkedAdd48Into "end_" now48 (.storage tauRef) ++
                          [ .assign .storage (bidsF (.var "id") "end")
                            (.var "end_") ])
                        (.ok frameEnd evmEnd) := by
                    simpa [frame0, frameEnd, localsEnd, evmSolm, lot, bid, fillNew,
                      evmFill, idWord, evmGuy, evmEnd, endWord] using
                      flapperKickPrefixOk evmSolm lot bid fillNew idWord endWord
                        (by simp only [evmSolm, initState]; exact hwv)
                        hauthSolm hliveSolm hkicksSolm hfillNew hfillFit
                        (by simpa [evmFill] using hfillLidSolm)
                        (by simpa [evmFill] using hid)
                        (by simpa [evmFill] using hidFit)
                        (by simpa [evmGuy] using hend)
                        (by simpa [evmGuy] using hwrapSolm)
                  have htailExternal :
                      BlockProgress flapperBytecode I (Sat256.ofUInt256 g) s0
                        config frameEnd evmEnd
                        [ .externalCall (.storage vatRef) "move" (.intLit 0)
                            [sender, thisAddr, .var "lot"] "_moveRet",
                          .return [.var "id"] ]
                        (runtimeExit (.abi kickTransition.returnType)) := by
                    obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
                      flapperX_kick_call_boundary (g := Sat256.ofUInt256 g) hperm
                        hcodeSize h4407
                    refine BlockProgress.externalCall
                      (h := rdCall) (hState := hStateEnd)
                      (receiver := .storage vatRef) (eth := .intLit 0)
                      (args := [sender, thisAddr, .var "lot"])
                      (argVals := [.address I.source, .address I.codeOwner,
                        .int (Int.ofNat lot.toNat)])
                      (tgt := AccountAddress.ofNat
                        (flapperKickVatWord (flapperKickAfterEndWorld σ_evm I) I).toNat)
                      (name := "move") (retVar := "_moveRet") (value := 0)
                      (stmts := [ .return [.var "id"] ])
                      ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
                      (by simp only [flapperKickCallRest, List.length_cons,
                        List.length_nil]; omega)
                      (by exact True.intro) ?_ ?_
                    · have hrecv := flapperKickVat_eval evmEnd localsEnd (by
                        simp [localsEnd, flapperKickLocalsEnd, flapperKickLocalsId,
                          flapperKickLocalsFillNew, flapperKickLocals])
                      simpa [frameEnd, localsEnd, hVatWordEq] using hrecv
                    · simp [evalExpr?, pure]
                    · have hargs := flapperKickArgs_eval evmEnd lot bid fillNew
                        idWord endWord
                      have hsrc : evmEnd.executionEnv.source = I.source := by
                        rw [hStateEnd.env]
                      have howner : evmEnd.executionEnv.codeOwner = I.codeOwner := by
                        rw [hStateEnd.env]
                      simpa [frameEnd, localsEnd, hsrc, howner] using hargs
                    · exact wordOfInt_zero.symm
                    · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
                      apply Fin.ext
                      simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
                        AccountAddress.size]
                    · simpa [lot,
                        show (UInt256.ofNat 128).toNat = 128 by decide,
                        show (UInt256.ofNat 100).toNat = 100 by decide] using
                        flapperKickMoveEncode_eq σ_evm I
                    · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
                      have hdecodeOut :
                          config.externalABI.decode? "move" out = some [] := by
                        simp [config, externalABI, decodeVoid?]
                      rw [hdecodeOut]
                      have hsource :
                          ExecBlock config
                            { contract := contract,
                              locals := localsEnd.insert "_moveRet" (collapseReturns []) }
                            evm' [ .return [.var "id"] ]
                            (.returned
                              { contract := contract,
                                locals :=
                                  localsEnd.insert "_moveRet" (collapseReturns []) }
                              evm' (some [.int (Int.ofNat idWord.toNat)])) := by
                        simpa [localsEnd] using
                          (ExecBlock.consReturn
                            (ExecStmt.return
                              (evalExprs?_singleton
                                (flapperKickId_eval_afterMoveRet evm' lot bid
                                  fillNew idWord endWord))) :
                            ExecBlock config
                              { contract := contract,
                                locals :=
                                  (flapperKickLocalsEnd lot bid fillNew idWord
                                      endWord).insert "_moveRet"
                                    (collapseReturns []) }
                              evm' [ .return [.var "id"] ]
                              (.returned
                                { contract := contract,
                                  locals :=
                                    (flapperKickLocalsEnd lot bid fillNew idWord
                                        endWord).insert "_moveRet"
                                      (collapseReturns []) }
                                evm'
                                (some [.int (Int.ofNat idWord.toNat)])))
                      have hret : RDret flapperBytecode (Sat256.ofUInt256 g)
                          s0 world' (UInt256.toByteArray idWord) := by
                        simpa [s0, idWord] using
                          flapperX_kick_call_success
                            (σ := σ_evm) (sel := flapperSelWord I) hperm (h := by
                              simpa [callCursor,
                                show UInt256.ofNat 4461 + ⟨1⟩ =
                                  UInt256.ofNat 4462 by native_decide]
                                using rdSucc)
                      exact BlockProgress.ofRDret (hsource := hsource) hret
                        hState'.created.symm hState'.accounts
                        (by
                          simpa [kickTransition, uint256, uint256Int] using
                            (returnDataEquiv.abi
                              (returnEquiv_of_encode
                                (uint256ReturnEncoding idWord))))
                    · intro out world' k' C' cur rdFail
                      exact flapperX_kick_call_failure
                        (σ := σ_evm) (sel := flapperSelWord I) (h := by
                          simpa [callCursor,
                            show UInt256.ofNat 4461 + ⟨1⟩ = UInt256.ofNat 4462 by
                              native_decide]
                            using rdFail)
                  have htail :
                      BlockProgress flapperBytecode I (Sat256.ofUInt256 g) s0
                        config frameEnd evmEnd
                        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
                          [sender, thisAddr, .var "lot"] "_moveRet" ++
                          [ .return [.var "id"] ])
                        (runtimeExit (.abi kickTransition.returnType)) := by
                    simpa [checkedExternalCallStmts] using
                      BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
                  have hprogress :
                      BlockProgress flapperBytecode I (Sat256.ofUInt256 g) s0
                        config frame0 evmSolm kickTransition.body
                        (runtimeExit (.abi kickTransition.returnType)) := by
                    have hp := BlockProgress.prepend hpref htail
                    simpa [kickTransition, nonpayable, auth, checkedAddUintInto,
                      checkedAdd48Into, checkedExternalCallStmts, frame0, frameEnd,
                      localsEnd] using hp
                  exact hprogress.toRuntimeEquivalenceFor hcode
                    (fun result hfunc => by
                      exact solmExec.intro (flapperSelectorDispatch_kick hselLit)
                        rfl hdec
                        (by simp [evmSolm, initState, Sat256.ofUInt256,
                          Sat256.toUInt256])
                        hfunc)
                    (by intro result endpoint h; exact h)
            · have hfillLidSolm :
                  ¬ (flapperKickFillWordOfState evmFill).toNat ≤
                    (flapperKickLidWordOfState evmFill).toNat := by
                intro hle
                exact hlidEvm (by simpa [hFillAfterEq, hLidAfterEq, fillNew] using hle)
              have hbody :
                  ExecTransitionBody config contract evmSolm
                    (flapperKickLocals lot bid) kickTransition.body .reverted := by
                simpa [evmSolm, lot, bid, fillNew, evmFill] using
                  flapperKickBodyRevertsLid evmSolm lot bid fillNew
                    (by simp only [evmSolm, initState]; exact hwv)
                    hauthSolm hliveSolm hkicksSolm hfillNew hfillFit hfillLidSolm
              exact (flapperX_kick_lid_revert (g := Sat256.ofUInt256 g)
                  hsize hsz68 hperm hauthEvm hliveEvm hkicksEvm hfillNoWrapEvm
                  hlidEvm hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hoverSolm :
                UInt256.size ≤ (flapperKickFillWordOfState evmSolm).toNat + lot.toNat := by
              omega
            have hoverEvm :
                UInt256.size ≤ (flapperKickFillWord σ_evm I).toNat + lot.toNat := by
              have hnot :
                  ¬ (flapperKickFillWord σ_evm I).toNat + lot.toNat <
                    UInt256.size := by
                intro hfit
                exact hfillFit (by simpa [hFillLoadEq] using hfit)
              omega
            have hfillWrapEvm :
                (flapperKickFillNewWord σ_evm I).toNat <
                  (flapperKickFillWord σ_evm I).toNat := by
              simpa [flapperKickFillNewWord, lot] using
                flapperKickAddWrap_lt_left (flapperKickFillWord σ_evm I) lot hoverEvm
            have hbody :
                ExecTransitionBody config contract evmSolm
                  (flapperKickLocals lot bid) kickTransition.body .reverted := by
              simpa [evmSolm, lot, bid] using
                flapperKickBodyRevertsFillOverflow evmSolm lot bid
                  (by simp only [evmSolm, initState]; exact hwv)
                  hauthSolm hliveSolm hkicksSolm hoverSolm
            exact (flapperX_kick_fill_overflow_revert
                (g := Sat256.ofUInt256 g) hsize hsz68 hauthEvm hliveEvm
                hkicksEvm hfillWrapEvm hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hkicksSolm :
              ¬ (flapperKickKicksWordOfState evmSolm).toNat <
                (UInt256.lnot (UInt256.ofNat 0)).toNat := by
            intro hbad
            exact hkicksEvm (by simpa [hKicksLoadEq, flapperKickKicksWord] using hbad)
          have hbody :
              ExecTransitionBody config contract evmSolm (flapperKickLocals lot bid)
                kickTransition.body .reverted := by
            simpa [evmSolm, lot, bid] using
              flapperKickBodyRevertsKicks evmSolm lot bid
                (by simp only [evmSolm, initState]; exact hwv)
                hauthSolm hliveSolm hkicksSolm
          exact (flapperX_kick_kicks_revert (g := Sat256.ofUInt256 g)
              hsize hsz68 hauthEvm hliveEvm hkicksEvm hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hliveSolm :
            flapperKickLiveWordOfState evmSolm ≠ UInt256.ofNat 1 := by
          intro hbad
          exact hliveEvm (by rw [← hLiveLoadEq]; exact hbad)
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperKickLocals lot bid)
              kickTransition.body .reverted := by
          simpa [evmSolm, lot, bid] using
            flapperKickBodyRevertsLive evmSolm lot bid
              (by simp only [evmSolm, initState]; exact hwv) hauthSolm hliveSolm
        exact (flapperX_kick_live_revert (g := Sat256.ofUInt256 g)
            hsize hsz68 hauthEvm hliveEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) ≠ UInt256.ofNat 1 := by
        intro hbad
        exact hauthEvm (by rw [← hAuthLoadEq]; exact hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperKickLocals lot bid)
            kickTransition.body .reverted := by
        simpa [evmSolm, lot, bid] using
          flapperKickBodyRevertsAuth evmSolm lot bid
            (by simp only [evmSolm, initState]; exact hwv) hauthSolm
      exact (flapperX_kick_auth_revert (g := Sat256.ofUInt256 g)
          hsize hsz68 hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := flapperDecode_kick_none_short (I := I) hsz4 hshort
    have hrev := flapperX_kick_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
