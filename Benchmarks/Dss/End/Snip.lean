import Benchmarks.Dss.End.Cage
import Benchmarks.Dss.End.Skim
import Benchmarks.Dss.End.RuntimeBlocks_003
import Benchmarks.Dss.End.RuntimeBlocks_004
import Benchmarks.Dss.End.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `snip(bytes32,uint256)` -/

abbrev endSnipStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))

theorem endDecode_legacyBytes32_uint256_snip_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "id"] [bytes32, uint256]
        I.calldata =
      some (endSnipStore I) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
      calldataWord I.calldata 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, uint256].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, uint256, isDynamicABIType]
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [show decodeABIValues? [bytes32, uint256] (I.calldata.toList.drop 4) 0 0 64 64
        DecodeMode.legacySolc05 =
        some ([endArg0Bytes32Value I, .int (Int.ofNat (endArg1Word I).toNat)], 64) by
    simp only [decodeABIValues?]
    rw [show isDynamicABIType bytes32 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? bytes32 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval0 :
        decodeABIValue? bytes32 (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
          some (endArg0Bytes32Value I, 32) := by
      simp [bytes32, bytes32Width, endArg0Bytes32Value, decodeABIValue?, readBytes?,
        htake4]
    rw [hval0]
    simp only [Nat.reduceAdd, beq_self_eq_true, if_true]
    rw [show isDynamicABIType uint256 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? uint256 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval1 :
        decodeABIValue? uint256 (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
          some (.int (Int.ofNat (endArg1Word I).toNat), 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := uint256) (bytes := I.calldata.toList.drop 4) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256
          (I.calldata.toList.drop 4) 32 =
        some (.int (Int.ofNat (endArg1Word I).toNat), 64)
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := I.calldata.toList.drop 4) (start := 32) htake36]
      rw [hword36]
    rw [hval1]
    simp]
  simp [decodeCalldata.insertValues, endSnipStore, endUIntValue]

theorem endDecode_legacyBytes32_uint256_snip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "id"] [bytes32, uint256]
        I.calldata = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, uint256].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, uint256, isDynamicABIType]
  have hshortArgs : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

abbrev endSnipTagSlot (I : ExecutionEnv) : UInt256 :=
  endSkimTagSlot I

abbrev endSnipTagWorldSlot (I : ExecutionEnv) : UInt256 :=
  endSkimTagWorldSlot I

abbrev endSnipTagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  endSkimTagWord evm I

abbrev endSnipTagWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSkimTagWorldWord σ I

abbrev endSnipDogTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endCageSlotTarget σ I (UInt256.ofNat 3)

abbrev endSnipDogIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  endSkimVatIlksBaseMem I

abbrev endSnipDogIlksCallMem (I : ExecutionEnv) : ByteArray :=
  endSkimVatIlksCallMem I

abbrev endSnipDogIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endSnipDogTarget σ I, ⟨0⟩,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipDogIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endSnipDogTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨128⟩] ++
    endSnipDogIlksCallRest σ I sel

abbrev endSnipDogIlksCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨1818⟩, stack := endSnipDogIlksCallStack σ I sel,
    mem := endSnipDogIlksCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endSnipDogIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨128⟩ : UInt256).toNat)

abbrev endSnipDogIlksReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endSnipDogIlksCallMem I) 128
    (min (⟨128⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endSnipAfterDogIlksAw (aw : UInt256) : UInt256 :=
  M (endSnipDogIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSnipDogIlksClipWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endSnipDogIlksWord1 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endSnipDogIlksWord2 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endSnipDogIlksWord3 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 96).take 32)

abbrev endSnipDogIlksValues (out : ByteArray) : List Value :=
  [.address (AccountAddress.ofNat (endSnipDogIlksClipWord out).toNat),
    endUIntValue (endSnipDogIlksWord1 out),
    endUIntValue (endSnipDogIlksWord2 out),
    endUIntValue (endSnipDogIlksWord3 out)]

abbrev endSnipAfterDogIlksFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSnipStore I).insert "dogIlk" (collapseReturns (endSnipDogIlksValues out)) }

abbrev endSnipAfterDogIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨1858⟩,
    stack := [UInt256.ofNat out.size,
      memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I out),
      ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSnipDogIlksReturnMem I out,
    aw := endSnipAfterDogIlksAw aw,
    rdata := out,
    world := world }

abbrev endSnipClipValue (out : ByteArray) : Value :=
  .address (AccountAddress.ofNat (endSnipDogIlksClipWord out).toNat)

abbrev endSnipAfterClipFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSnipAfterDogIlksFrame I out).locals.insert "clip"
      (endSnipClipValue out) }

abbrev endSnipVatIlksCallMem (I : ExecutionEnv) (outDog : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_1858_taken_memory
    (mem := endSnipDogIlksReturnMem I outDog) (x4 := endArg0Word I)

abbrev endSnipVatIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (outDog : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I, ⟨0⟩,
    endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipVatIlksCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog : ByteArray) (sel : UInt256) : List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨160⟩] ++
    endSnipVatIlksCallRest σ I outDog sel

abbrev endSnipVatIlksCallCursor (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outDog rdata : ByteArray) : Cursor :=
  { pc := ⟨1944⟩, stack := endSnipVatIlksCallStack world.2 I outDog sel,
    mem := endSnipVatIlksCallMem I outDog, aw := aw, rdata := rdata, world := world }

abbrev endSnipVatIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat)

abbrev endSnipVatIlksReturnMem (I : ExecutionEnv) (outDog outVat : ByteArray) :
    ByteArray :=
  outVat.write 0 (endSnipVatIlksCallMem I outDog) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat

abbrev endSnipAfterVatIlksAw (aw : UInt256) : UInt256 :=
  M (endSnipVatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSnipAfterVatIlksFrame (I : ExecutionEnv) (outDog outVat : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat)) }

abbrev endSnipAfterVatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outDog outVat : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨1984⟩,
    stack := [UInt256.ofNat outVat.size,
      memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat),
      ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSnipVatIlksReturnMem I outDog outVat,
    aw := endSnipAfterVatIlksAw aw,
    rdata := outVat,
    world := world }

abbrev endSnipAfterRateFrame (I : ExecutionEnv) (outDog outVat : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterVatIlksFrame I outDog outVat).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat)) }

abbrev endSnipClipTarget (outDog : ByteArray) : UInt256 :=
  UInt256.land (endSnipDogIlksClipWord outDog) solcAddrMask

abbrev endSnipSalesSelectorWord : UInt256 :=
  UInt256.ofNat 3052741367

abbrev endSnipSalesSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft endSnipSalesSelectorWord (UInt256.ofNat 224)

def endSnipSalesPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg1Word I)

def endSnipSalesEncodedCall (I : ExecutionEnv) : ByteArray :=
  salesSelector ++ ⟨(endSnipSalesPayloadBytes I).toArray⟩

abbrev endSnipSalesCallMem (I : ExecutionEnv) (outDog outVat : ByteArray) :
    ByteArray :=
  endRuntimeBlocks.endRuntime_block_1984_taken_memory
    (mem := endSnipVatIlksReturnMem I outDog outVat) (x5 := endArg1Word I)

abbrev endSnipSalesCallRest (I : ExecutionEnv) (outDog outVat : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endSnipSalesSelectorWord, endSnipClipTarget outDog, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
    endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipSalesCallStack (I : ExecutionEnv) (outDog outVat : ByteArray)
    (sel : UInt256) : List UInt256 :=
  [endSnipClipTarget outDog, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨192⟩] ++
    endSnipSalesCallRest I outDog outVat sel

abbrev endSnipSalesCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outDog outVat rdata : ByteArray) :
    Cursor :=
  { pc := ⟨2072⟩, stack := endSnipSalesCallStack I outDog outVat sel,
    mem := endSnipSalesCallMem I outDog outVat, aw := aw, rdata := rdata,
    world := world }

abbrev endSnipSalesCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨192⟩ : UInt256).toNat)

abbrev endSnipSalesReturnMem (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    ByteArray :=
  outSales.write 0 (endSnipSalesCallMem I outDog outVat) 128
    (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat

abbrev endSnipAfterSalesAw (aw : UInt256) : UInt256 :=
  M (endSnipSalesCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSnipSalesWord0 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endSnipSalesTabWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endSnipSalesLotWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endSnipSalesUsrWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 96).take 32)

abbrev endSnipSalesWord4 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 128).take 32)

abbrev endSnipSalesWord5 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 160).take 32)

abbrev endSnipSalesUint96Value (w : UInt256) : Value :=
  .int (Int.ofNat (w.toNat % EVM.twoPow 96))

abbrev endSnipSalesValues (out : ByteArray) : List Value :=
  [endUIntValue (endSnipSalesWord0 out), endUIntValue (endSnipSalesTabWord out),
    endUIntValue (endSnipSalesLotWord out),
    .address (AccountAddress.ofNat (endSnipSalesUsrWord out).toNat),
    endSnipSalesUint96Value (endSnipSalesWord4 out),
    endUIntValue (endSnipSalesWord5 out)]

abbrev endSnipAfterSalesFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales)) }

abbrev endSnipAfterSalesCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outDog outVat outSales : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨2112⟩,
    stack := [UInt256.ofNat outSales.size,
      memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales),
      ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
      endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel],
    mem := endSnipSalesReturnMem I outDog outVat outSales,
    aw := endSnipAfterSalesAw aw,
    rdata := outSales,
    world := world }

abbrev endSnipTabValue (outSales : ByteArray) : Value :=
  endUIntValue (endSnipSalesTabWord outSales)

abbrev endSnipLotValue (outSales : ByteArray) : Value :=
  endUIntValue (endSnipSalesLotWord outSales)

abbrev endSnipUsrValue (outSales : ByteArray) : Value :=
  .address (AccountAddress.ofNat (endSnipSalesUsrWord outSales).toNat)

abbrev endSnipAfterTabFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales) }

abbrev endSnipAfterLotFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales) }

abbrev endSnipAfterUsrFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterLotFrame I outDog outVat outSales).locals.insert "usr"
      (endSnipUsrValue outSales) }

abbrev endSnipSuckSelectorWord : UInt256 :=
  UInt256.ofNat 4065207275

abbrev endSnipSuckSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft endSnipSuckSelectorWord (UInt256.ofNat 224)

def endSnipSuckPayloadBytes (σ : AccountMap) (I : ExecutionEnv)
    (outSales : ByteArray) : List UInt8 :=
  (EVM.Word.toBytesBE (endPackVowTarget σ I) ++
    EVM.Word.toBytesBE (endPackVowTarget σ I)) ++
    EVM.Word.toBytesBE (endSnipSalesTabWord outSales)

def endSnipSuckEncodedCall (σ : AccountMap) (I : ExecutionEnv)
    (outSales : ByteArray) : ByteArray :=
  suckSelector ++ ⟨(endSnipSuckPayloadBytes σ I outSales).toArray⟩

abbrev endSnipSuckMemSel (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    ByteArray :=
  endSnipSuckSelectorEncodedWord.toByteArray.write 0
    (endSnipSalesReturnMem I outDog outVat outSales) 128 32

abbrev endSnipSuckMemVow0 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endPackVowTarget σ I).toByteArray.write 0
    (endSnipSuckMemSel I outDog outVat outSales) 132 32

abbrev endSnipSuckMemVow1 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endPackVowTarget σ I).toByteArray.write 0
    (endSnipSuckMemVow0 σ I outDog outVat outSales) 164 32

abbrev endSnipSuckCallMem (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endSnipSalesTabWord outSales).toByteArray.write 0
    (endSnipSuckMemVow1 σ I outDog outVat outSales)
    196 32

abbrev endSnipSuckCallRest (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨228⟩, endSnipSuckSelectorWord, endPackVatTarget σ I,
    endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
    endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
    endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipSuckCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩] ++
    endSnipSuckCallRest σ I outDog outVat outSales sel

abbrev endSnipSuckCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outDog outVat outSales rdata : ByteArray) :
    Cursor :=
  { pc := ⟨2234⟩, stack := endSnipSuckCallStack world.2 I outDog outVat outSales sel,
    mem := endSnipSuckCallMem world.2 I outDog outVat outSales, aw := aw, rdata := rdata,
    world := world }

abbrev endSnipSuckCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨100⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSnipAfterSuckFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns []) }

abbrev endSnipAfterSuckStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSnipSuckCallRest σ I outDog outVat outSales sel

abbrev endSnipAfterSuckCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outDog outVat outSales out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨2252⟩, stack := endSnipAfterSuckStack σ I outDog outVat outSales sel,
    mem := endSnipSuckCallMem σ I outDog outVat outSales,
    aw := endSnipSuckCallAw aw, rdata := out, world := world }

abbrev endSnipYankSelectorWord : UInt256 :=
  UInt256.ofNat 652224497

abbrev endSnipYankSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (UInt256.ofNat 4294967295) endSnipYankSelectorWord)
    (UInt256.ofNat 224)

def endSnipYankPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg1Word I)

def endSnipYankEncodedCall (I : ExecutionEnv) : ByteArray :=
  yankSelector ++ ⟨(endSnipYankPayloadBytes I).toArray⟩

abbrev endSnipYankMemSel (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  endSnipYankSelectorEncodedWord.toByteArray.write 0
    (endSnipSuckCallMem σ I outDog outVat outSales) 128 32

abbrev endSnipYankCallMem (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  (endArg1Word I).toByteArray.write 0
    (endSnipYankMemSel σ I outDog outVat outSales) 132 32

abbrev endSnipYankCallRest (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨164⟩, endSnipYankSelectorWord, endSnipClipTarget outDog,
    endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
    endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
    endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipYankCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [endSnipClipTarget outDog, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨0⟩] ++
    endSnipYankCallRest σ I outDog outVat outSales sel

abbrev endSnipYankCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (outDog outVat outSales rdata : ByteArray) : Cursor :=
  { pc := ⟨2328⟩, stack := endSnipYankCallStack preσ I outDog outVat outSales sel,
    mem := endSnipYankCallMem preσ I outDog outVat outSales, aw := aw,
    rdata := rdata, world := world }

abbrev endSnipYankCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endSnipAfterYankFrame (I : ExecutionEnv) (outDog outVat outSales : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns []) }

abbrev endSnipAfterYankStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [⟨0⟩] ++ endSnipYankCallRest σ I outDog outVat outSales sel

abbrev endSnipAfterYankCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outDog outVat outSales out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨2346⟩, stack := endSnipAfterYankStack σ I outDog outVat outSales sel,
    mem := endSnipYankCallMem σ I outDog outVat outSales,
    aw := endSnipYankCallAw aw, rdata := out, world := world }

abbrev endSnipArtWord (outVat outSales : ByteArray) : UInt256 :=
  UInt256.div (endSnipSalesTabWord outSales) (endFlowVatIlksRateWord outVat)

abbrev endSnipArtValue (outVat outSales : ByteArray) : Value :=
  endUIntValue (endSnipArtWord outVat outSales)

def endSnipAfterArtFrame (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales) }

abbrev endSnipArtNewWord (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSales : ByteArray) : UInt256 :=
  endGenericAddResult (endFlowArtWord evm I) (endSnipArtWord outVat outSales)

abbrev endSnipArtNewWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outVat outSales : ByteArray) : UInt256 :=
  endGenericAddResult (endFlowArtWorldWord σ I) (endSnipArtWord outVat outSales)

def endSnipAfterArtNewFrame (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSnipAfterArtFrame I outDog outVat outSales).locals.insert "ArtNew"
      (endUIntValue (endSnipArtNewWord evm I outVat outSales)) }

abbrev endSnipArtHashMem (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_2361_memory
    (mem := endSnipYankCallMem σ I outDog outVat outSales) (x10 := endArg0Word I)

abbrev endSnipAddCallStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [endSnipArtWord outVat outSales, endFlowArtWorldWord σ I, ⟨2391⟩,
    endSnipArtWord outVat outSales, endSnipSalesUsrWord outSales,
    endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
    endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
    endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endSnipAfterAddStack (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (sel : UInt256) : List UInt256 :=
  [endSnipArtNewWorldWord σ I outVat outSales, endSnipArtWord outVat outSales,
    endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
    endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
    endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

theorem endExternalEncode_dogIlks (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "dogIlks" [endArg0Bytes32Value I] =
      some (endFlowVatIlksEncodedCall I) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "dogIlks" = "cage")]
  rw [if_neg (by decide : ¬ "dogIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "dogIlks" = "catIlks")]
  rw [if_pos (by decide : "dogIlks" = "dogIlks")]
  exact endEncodeCallWithSelector_vatIlks I hsz36

theorem endSnipDecodeScalarWordsWithMode_legacy_addr_uint256x3_ok {out : ByteArray}
    (h128 : 128 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256, uint256] out.toList 0 =
      some (endSnipDogIlksValues out) := by
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
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
        some (.address (AccountAddress.ofNat (endSnipDogIlksClipWord out).toNat),
          0 + 32) := by
    simpa [addr, abiAddress, endSnipDogIlksClipWord, List.drop_zero] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endUIntValue (endSnipDogIlksWord1 out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipDogIlksWord1, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
        some (endUIntValue (endSnipDogIlksWord2 out), 64 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipDogIlksWord2, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
        some (endUIntValue (endSnipDogIlksWord3 out), 96 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipDogIlksWord3, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96)
  rw [hdec96]

theorem endSnipDecodeScalarWordsWithMode_legacy_addr_uint256x3_none_short
    {out : ByteArray} (hshort : out.size < 128) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256, uint256] out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          some (.address (AccountAddress.ofNat (endSnipDogIlksClipWord out).toNat),
            0 + 32) := by
      simpa [addr, abiAddress, endSnipDogIlksClipWord, List.drop_zero] using
        (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endUIntValue (endSnipDogIlksWord1 out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endSnipDogIlksWord1, endUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind, Nat.reduceAdd]
      by_cases h64 : ((out.toList.drop 64).take 32).length = 32
      · have hdec64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (endUIntValue (endSnipDogIlksWord2 out), 64 + 32) := by
          simpa [uint256, uint256Int, abiUInt256, endSnipDogIlksWord2, endUIntValue] using
            (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) h64)
        rw [hdec64]
        simp only [Option.bind, bind, Nat.reduceAdd]
        have h96 : ¬ ((out.toList.drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have hnone96 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
              none := by
          simpa [uint256, uint256Int, abiUInt256] using
            (decodeScalarWordWithMode_uint256_none_short
              (mode := DecodeMode.legacySolc05) (bytes := out.toList)
              (start := 96) h96)
        rw [hnone96]
      · have hnone64 :
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

theorem endSnipDecodeReturnValues_legacy_dogIlks_ok {out : ByteArray}
    (h128 : 128 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256, uint256] out =
      some (endSnipDogIlksValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256, uint256, uint256] = some 128 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 128)
    (by decide) (by decide)]
  rw [endSnipDecodeScalarWordsWithMode_legacy_addr_uint256x3_ok h128]

theorem endSnipDecodeReturnValues_legacy_dogIlks_none_short {out : ByteArray}
    (hshort : out.size < 128) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [addr, uint256, uint256, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256, uint256, uint256] = some 128 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 128)
    (by decide) (by decide)]
  rw [endSnipDecodeScalarWordsWithMode_legacy_addr_uint256x3_none_short hshort]

theorem endExternalDecode_dogIlks_ok {out : ByteArray} (h128 : 128 ≤ out.size) :
    config.externalABI.decode? "dogIlks" out = some (endSnipDogIlksValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "dogIlks" = "cage")]
  rw [if_neg (by decide : ¬ "dogIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "dogIlks" = "catIlks")]
  rw [if_pos (by decide : "dogIlks" = "dogIlks")]
  exact endSnipDecodeReturnValues_legacy_dogIlks_ok h128

theorem endExternalDecode_dogIlks_none_short {out : ByteArray}
    (hshort : out.size < 128) :
    config.externalABI.decode? "dogIlks" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "dogIlks" = "cage")]
  rw [if_neg (by decide : ¬ "dogIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "dogIlks" = "catIlks")]
  rw [if_pos (by decide : "dogIlks" = "dogIlks")]
  exact endSnipDecodeReturnValues_legacy_dogIlks_none_short hshort

theorem endEncodeUint_snipId (I : ExecutionEnv) :
    encodeABIValue? uint256 (endUIntValue (endArg1Word I)) =
      some (EVM.Word.toBytesBE (endArg1Word I)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (endUIntValue (endArg1Word I))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endArg1Word I))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

theorem endEncodeABIValues_sales_snip (I : ExecutionEnv) :
    encodeABIValues? [uint256] [endUIntValue (endArg1Word I)] =
      some (endSnipSalesPayloadBytes I) := by
  have hhead : abiTupleHeadSize? [uint256] = some 32 := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeUint_snipId I, hdynUint]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endSnipSalesPayloadBytes]

theorem endEncodeCallWithSelector_sales_snip (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? salesSelector [uint256] [endUIntValue (endArg1Word I)] =
      some (endSnipSalesEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_sales_snip I]
  simp [endSnipSalesEncodedCall, endSnipSalesPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_sales_branch (args : List Value) :
    config.externalABI.encode? "sales" args =
      ABI.encodeCallWithSelector? salesSelector [uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "sales" = "cage")]
  rw [if_neg (by decide : ¬ "sales" = "vatIlks")]
  rw [if_neg (by decide : ¬ "sales" = "catIlks")]
  rw [if_neg (by decide : ¬ "sales" = "dogIlks")]
  rw [if_neg (by decide : ¬ "sales" = "spotIlks")]
  rw [if_neg (by decide : ¬ "sales" = "urns")]
  rw [if_neg (by decide : ¬ "sales" = "dai")]
  rw [if_neg (by decide : ¬ "sales" = "debt")]
  rw [if_neg (by decide : ¬ "sales" = "move")]
  rw [if_neg (by decide : ¬ "sales" = "hope")]
  rw [if_neg (by decide : ¬ "sales" = "flux")]
  rw [if_neg (by decide : ¬ "sales" = "grab")]
  rw [if_neg (by decide : ¬ "sales" = "suck")]
  rw [if_neg (by decide : ¬ "sales" = "par")]
  rw [if_neg (by decide : ¬ "sales" = "tell")]
  rw [if_neg (by decide : ¬ "sales" = "bids")]
  rw [if_pos (by decide : "sales" = "sales")]

theorem endExternalEncode_sales_snip (I : ExecutionEnv) :
    config.externalABI.encode? "sales" [endUIntValue (endArg1Word I)] =
      some (endSnipSalesEncodedCall I) := by
  rw [endExternalEncode_sales_branch]
  exact endEncodeCallWithSelector_sales_snip I

theorem endEncodeUint_snipTab (outSales : ByteArray) :
    encodeABIValue? uint256 (endSnipTabValue outSales) =
      some (EVM.Word.toBytesBE (endSnipSalesTabWord outSales)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (endSnipTabValue outSales)
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endSnipSalesTabWord outSales))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

theorem endEncodeABIValues_suck_snip (σ : AccountMap) (I : ExecutionEnv)
    (outSales : ByteArray) :
    encodeABIValues? [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSnipTabValue outSales] =
      some (endSnipSuckPayloadBytes σ I outSales) := by
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
  rw [endEncodeUint_snipTab outSales, hdynUint]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSnipSuckPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_suck_snip (σ : AccountMap) (I : ExecutionEnv)
    (outSales : ByteArray) :
    ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSnipTabValue outSales] =
      some (endSnipSuckEncodedCall σ I outSales) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_suck_snip σ I outSales]
  simp [endSnipSuckEncodedCall, endSnipSuckPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_suck_branch (args : List Value) :
    config.externalABI.encode? "suck" args =
      ABI.encodeCallWithSelector? suckSelector [addr, addr, uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "suck" = "cage")]
  rw [if_neg (by decide : ¬ "suck" = "vatIlks")]
  rw [if_neg (by decide : ¬ "suck" = "catIlks")]
  rw [if_neg (by decide : ¬ "suck" = "dogIlks")]
  rw [if_neg (by decide : ¬ "suck" = "spotIlks")]
  rw [if_neg (by decide : ¬ "suck" = "urns")]
  rw [if_neg (by decide : ¬ "suck" = "dai")]
  rw [if_neg (by decide : ¬ "suck" = "debt")]
  rw [if_neg (by decide : ¬ "suck" = "move")]
  rw [if_neg (by decide : ¬ "suck" = "hope")]
  rw [if_neg (by decide : ¬ "suck" = "flux")]
  rw [if_neg (by decide : ¬ "suck" = "grab")]
  rw [if_pos (by decide : "suck" = "suck")]

theorem endExternalEncode_suck_snip (σ : AccountMap) (I : ExecutionEnv)
    (outSales : ByteArray) :
    config.externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        endSnipTabValue outSales] =
      some (endSnipSuckEncodedCall σ I outSales) := by
  rw [endExternalEncode_suck_branch]
  exact endEncodeCallWithSelector_suck_snip σ I outSales

theorem endExternalDecode_suck (out : ByteArray) :
    config.externalABI.decode? "suck" out = some [] := by
  rfl

theorem endEncodeABIValues_yank_snip (I : ExecutionEnv) :
    encodeABIValues? [uint256] [endUIntValue (endArg1Word I)] =
      some (endSnipYankPayloadBytes I) := by
  simpa [endSnipYankPayloadBytes, endSnipSalesPayloadBytes] using
    endEncodeABIValues_sales_snip I

theorem endEncodeCallWithSelector_yank_snip (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? yankSelector [uint256]
      [endUIntValue (endArg1Word I)] =
      some (endSnipYankEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_yank_snip I]
  simp [endSnipYankEncodedCall, endSnipYankPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_yank_branch (args : List Value) :
    config.externalABI.encode? "yank" args =
      ABI.encodeCallWithSelector? yankSelector [uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "yank" = "cage")]
  rw [if_neg (by decide : ¬ "yank" = "vatIlks")]
  rw [if_neg (by decide : ¬ "yank" = "catIlks")]
  rw [if_neg (by decide : ¬ "yank" = "dogIlks")]
  rw [if_neg (by decide : ¬ "yank" = "spotIlks")]
  rw [if_neg (by decide : ¬ "yank" = "urns")]
  rw [if_neg (by decide : ¬ "yank" = "dai")]
  rw [if_neg (by decide : ¬ "yank" = "debt")]
  rw [if_neg (by decide : ¬ "yank" = "move")]
  rw [if_neg (by decide : ¬ "yank" = "hope")]
  rw [if_neg (by decide : ¬ "yank" = "flux")]
  rw [if_neg (by decide : ¬ "yank" = "grab")]
  rw [if_neg (by decide : ¬ "yank" = "suck")]
  rw [if_neg (by decide : ¬ "yank" = "par")]
  rw [if_neg (by decide : ¬ "yank" = "tell")]
  rw [if_neg (by decide : ¬ "yank" = "bids")]
  rw [if_neg (by decide : ¬ "yank" = "sales")]
  rw [if_neg (by decide : ¬ "yank" = "read")]
  rw [if_pos (by decide : "yank" = "yank")]

theorem endExternalEncode_yank_snip (I : ExecutionEnv) :
    config.externalABI.encode? "yank" [endUIntValue (endArg1Word I)] =
      some (endSnipYankEncodedCall I) := by
  rw [endExternalEncode_yank_branch]
  exact endEncodeCallWithSelector_yank_snip I

theorem endExternalDecode_yank (out : ByteArray) :
    config.externalABI.decode? "yank" out = some [] := by
  rfl

theorem endDecodeScalarWordWithMode_legacy_uint96_ok {bytes : List UInt8}
    {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint96 bytes start =
      some (.int (Int.ofNat
        ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 96)),
        start + 32) := by
  simp only [decodeScalarWordWithMode?, readWord?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  simp [uint96, uint96Int, decodeABIWord?, UInt256.toNat]

theorem endDecodeScalarWordWithMode_legacy_uint96_none_short {bytes : List UInt8}
    {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint96 bytes start = none := by
  simp only [decodeScalarWordWithMode?, readWord?, readBytes?, bind, Option.bind]
  rw [if_neg hshort]

theorem endSnipDecodeScalarWordsWithMode_legacy_sales_ok {out : ByteArray}
    (h192 : 192 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, addr, uint96, uint256] out.toList 0 =
      some (endSnipSalesValues out) := by
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
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (endUIntValue (endSnipSalesWord0 out), 0 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipSalesWord0, endUIntValue,
      List.drop_zero] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endUIntValue (endSnipSalesTabWord out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipSalesTabWord, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
        some (endUIntValue (endSnipSalesLotWord out), 64 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipSalesLotWord, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 96 =
        some (.address (AccountAddress.ofNat (endSnipSalesUsrWord out).toNat), 96 + 32) := by
    simpa [addr, abiAddress, endSnipSalesUsrWord] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 96) htake96)
  rw [hdec96]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint96 out.toList 128 =
        some (endSnipSalesUint96Value (endSnipSalesWord4 out), 128 + 32) := by
    simpa [endSnipSalesUint96Value, endSnipSalesWord4] using
      (endDecodeScalarWordWithMode_legacy_uint96_ok
        (bytes := out.toList) (start := 128) htake128)
  rw [hdec128]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 160 =
        some (endUIntValue (endSnipSalesWord5 out), 160 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endSnipSalesWord5, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 160) htake160)
  rw [hdec160]

theorem endSnipDecodeScalarWordsWithMode_legacy_sales_none_short {out : ByteArray}
    (hshort : out.size < 192) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, addr, uint96, uint256] out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          some (endUIntValue (endSnipSalesWord0 out), 0 + 32) := by
      simpa [uint256, uint256Int, abiUInt256, endSnipSalesWord0, endUIntValue,
        List.drop_zero] using
        (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endUIntValue (endSnipSalesTabWord out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endSnipSalesTabWord, endUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind, Nat.reduceAdd]
      by_cases h64 : ((out.toList.drop 64).take 32).length = 32
      · have hdec64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (endUIntValue (endSnipSalesLotWord out), 64 + 32) := by
          simpa [uint256, uint256Int, abiUInt256, endSnipSalesLotWord, endUIntValue] using
            (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) h64)
        rw [hdec64]
        simp only [Option.bind, bind, Nat.reduceAdd]
        by_cases h96 : ((out.toList.drop 96).take 32).length = 32
        · have hdec96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 96 =
                some (.address (AccountAddress.ofNat (endSnipSalesUsrWord out).toNat),
                  96 + 32) := by
            simpa [addr, abiAddress, endSnipSalesUsrWord] using
              (decodeScalarWord_legacyAddress_ok (bytes := out.toList)
                (start := 96) h96)
          rw [hdec96]
          simp only [Option.bind, bind, Nat.reduceAdd]
          by_cases h128 : ((out.toList.drop 128).take 32).length = 32
          · have hdec128 :
                decodeScalarWordWithMode? DecodeMode.legacySolc05 uint96 out.toList 128 =
                  some (endSnipSalesUint96Value (endSnipSalesWord4 out), 128 + 32) := by
              simpa [endSnipSalesUint96Value, endSnipSalesWord4] using
                (endDecodeScalarWordWithMode_legacy_uint96_ok
                  (bytes := out.toList) (start := 128) h128)
            rw [hdec128]
            simp only [Option.bind, bind, Nat.reduceAdd]
            by_cases h160 : ((out.toList.drop 160).take 32).length = 32
            · have hge : 192 ≤ out.size := by
                rw [List.length_take, List.length_drop, hlen] at h160
                omega
              omega
            · have hnone160 :
                  decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 160 =
                    none := by
                simpa [uint256, uint256Int, abiUInt256] using
                  (decodeScalarWordWithMode_uint256_none_short
                    (mode := DecodeMode.legacySolc05) (bytes := out.toList)
                    (start := 160) h160)
              rw [hnone160]
          · have hnone128 :
                decodeScalarWordWithMode? DecodeMode.legacySolc05 uint96 out.toList 128 =
                  none := by
              exact endDecodeScalarWordWithMode_legacy_uint96_none_short
                (bytes := out.toList) (start := 128) h128
            rw [hnone128]
        · have hnone96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 96 =
                none := by
            simpa [addr, abiAddress] using
              (decodeScalarWord_legacyAddress_none_short
                (bytes := out.toList) (start := 96) h96)
          rw [hnone96]
      · have hnone64 :
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
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          none := by
      simpa [uint256, uint256Int, abiUInt256] using
        (decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (bytes := out.toList)
          (start := 0) h0)
    rw [hnone0]
    rfl

theorem endSnipDecodeReturnValues_legacy_sales_ok {out : ByteArray}
    (h192 : 192 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, addr, uint96, uint256] out =
      some (endSnipSalesValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, uint96, uint256] =
      some 192 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, addr, uint96, uint256])
    (bytes := out.toList) (cursor := 0) (total := 192)
    (by decide) (by decide)]
  rw [endSnipDecodeScalarWordsWithMode_legacy_sales_ok h192]

theorem endSnipDecodeReturnValues_legacy_sales_none_short {out : ByteArray}
    (hshort : out.size < 192) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, addr, uint96, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, addr, uint96, uint256] =
      some 192 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, addr, uint96, uint256])
    (bytes := out.toList) (cursor := 0) (total := 192)
    (by decide) (by decide)]
  rw [endSnipDecodeScalarWordsWithMode_legacy_sales_none_short hshort]

theorem endExternalDecode_sales_ok {out : ByteArray} (h192 : 192 ≤ out.size) :
    config.externalABI.decode? "sales" out = some (endSnipSalesValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "sales" = "cage")]
  rw [if_neg (by decide : ¬ "sales" = "vatIlks")]
  rw [if_neg (by decide : ¬ "sales" = "catIlks")]
  rw [if_neg (by decide : ¬ "sales" = "dogIlks")]
  rw [if_neg (by decide : ¬ "sales" = "spotIlks")]
  rw [if_neg (by decide : ¬ "sales" = "urns")]
  rw [if_neg (by decide : ¬ "sales" = "dai")]
  rw [if_neg (by decide : ¬ "sales" = "debt")]
  rw [if_neg (by decide : ¬ "sales" = "par")]
  rw [if_neg (by decide : ¬ "sales" = "tell")]
  rw [if_neg (by decide : ¬ "sales" = "read")]
  rw [if_neg (by decide : ¬ "sales" = "bids")]
  rw [if_pos (by decide : "sales" = "sales")]
  exact endSnipDecodeReturnValues_legacy_sales_ok h192

theorem endExternalDecode_sales_none_short {out : ByteArray} (hshort : out.size < 192) :
    config.externalABI.decode? "sales" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "sales" = "cage")]
  rw [if_neg (by decide : ¬ "sales" = "vatIlks")]
  rw [if_neg (by decide : ¬ "sales" = "catIlks")]
  rw [if_neg (by decide : ¬ "sales" = "dogIlks")]
  rw [if_neg (by decide : ¬ "sales" = "spotIlks")]
  rw [if_neg (by decide : ¬ "sales" = "urns")]
  rw [if_neg (by decide : ¬ "sales" = "dai")]
  rw [if_neg (by decide : ¬ "sales" = "debt")]
  rw [if_neg (by decide : ¬ "sales" = "par")]
  rw [if_neg (by decide : ¬ "sales" = "tell")]
  rw [if_neg (by decide : ¬ "sales" = "read")]
  rw [if_neg (by decide : ¬ "sales" = "bids")]
  rw [if_pos (by decide : "sales" = "sales")]
  exact endSnipDecodeReturnValues_legacy_sales_none_short hshort

theorem endBytesToWord_drop_take32_eq_extract (returndata : ByteArray) (start : Nat) :
    ABI.bytesToWord ((returndata.toList.drop start).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (returndata.extract start (start + 32))) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (returndata.extract start (start + 32)), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]
  simp

theorem endSnipDogIlksCallMem_size (I : ExecutionEnv) :
    (endSnipDogIlksCallMem I).size = 164 := by
  simpa [endSnipDogIlksCallMem] using endSkimVatIlksCallMem_size I

theorem endSnipDogIlksCallMem_read64 (I : ExecutionEnv) :
    (endSnipDogIlksCallMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  simpa [endSnipDogIlksCallMem] using endSkimVatIlksCallMem_read64 I

theorem endSnipDogIlksCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endSnipDogIlksCallMem I) = ⟨128⟩ := by
  simpa [endSnipDogIlksCallMem] using endSkimVatIlksCallMem_mload64 I

theorem endSnipDogIlksReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h128 : 128 ≤ out.size) :
    (endSnipDogIlksReturnMem I out).size = 256 := by
  have hcopy :
      (min (⟨128⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 128 := by
    rw [callCopyLength_toNat out (⟨128⟩ : UInt256) hout]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    exact Nat.min_eq_left h128
  unfold endSnipDogIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSnipDogIlksCallMem I) 128 128
    (by decide) h128
    (by rw [endSnipDogIlksCallMem_size I]; omega)
    (by rw [endSnipDogIlksCallMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSnipDogIlksCallMem_size I]
  omega

theorem endSnipDogIlksReturnMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h128 : 128 ≤ out.size) :
    (endSnipDogIlksReturnMem I out).readWithPadding 64 32 =
      (endSnipDogIlksCallMem I).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨128⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 128 := by
    rw [callCopyLength_toNat out (⟨128⟩ : UInt256) hout]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    exact Nat.min_eq_left h128
  unfold endSnipDogIlksReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend out (endSnipDogIlksCallMem I) 128 128 64
    (by decide) h128
    (by rw [endSnipDogIlksCallMem_size I]; omega)
    (by omega)

theorem endSnipDogIlksReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h128 : 128 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I out) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipDogIlksReturnMem I out)
    (by rw [endSnipDogIlksReturnMem_size I out hout h128]; omega)
    (by rw [endSnipDogIlksReturnMem_read64 I out hout h128,
        endSnipDogIlksCallMem_read64 I])

theorem endSnipDogIlksReturnMem_read128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h128 : 128 ≤ out.size) :
    (endSnipDogIlksReturnMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  have hcopy :
      (min (⟨128⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 128 := by
    rw [callCopyLength_toNat out (⟨128⟩ : UInt256) hout]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    exact Nat.min_eq_left h128
  unfold endSnipDogIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSnipDogIlksCallMem I) 128 128
    (by decide) h128
    (by rw [endSnipDogIlksCallMem_size I]; omega)
    (by rw [endSnipDogIlksCallMem_size I]; omega)]
  have hpre : ((endSnipDogIlksCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipDogIlksCallMem_size I]
    omega
  have hcopySize : (out.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [hpre]), hpre]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 128 = 32 by omega]

theorem endSnipDogIlksReturnMem_mload128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h128 : 128 ≤ out.size) :
    memLoad (UInt256.ofNat 128) (endSnipDogIlksReturnMem I out) =
      endSnipDogIlksClipWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endSnipDogIlksReturnMem_size I out hout h128]
    omega)]
  rw [endSnipDogIlksReturnMem_read128 I out hout h128]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) =
    ABI.bytesToWord (out.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endSnipVatIlksCallMem_read64 (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endSnipVatIlksCallMem I outDog).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipVatIlksCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_1858_taken_memory]
  rw [endSnipDogIlksReturnMem_mload64 I outDog hout h128]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32)
    132 64
    (by
      have hge := toByteArray_write_size_ge_off_add32_unbounded
        endFlowVatIlksSelectorEncodedWord (endSnipDogIlksReturnMem I outDog) 128
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSnipDogIlksReturnMem I outDog) 128 64
    (by rw [endSnipDogIlksReturnMem_size I outDog hout h128]; omega)
    (by omega)]
  rw [endSnipDogIlksReturnMem_read64 I outDog hout h128,
    endSnipDogIlksCallMem_read64 I]

theorem endSnipVatIlksCallMem_mload64 (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    memLoad (UInt256.ofNat 64) (endSnipVatIlksCallMem I outDog) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipVatIlksCallMem I outDog)
    (by
      unfold endSnipVatIlksCallMem
      dsimp [endRuntimeBlocks.endRuntime_block_1858_taken_memory]
      rw [endSnipDogIlksReturnMem_mload64 I outDog hout h128]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
      have hge := toByteArray_write_size_ge_off_add32_unbounded
        (endArg0Word I)
        ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0
          (endSnipDogIlksReturnMem I outDog) 128 32)
        132
      omega)
    (endSnipVatIlksCallMem_read64 I outDog hout h128)

theorem endSnipVatIlksCallMem_eq_full (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    endSnipVatIlksCallMem I outDog =
      (endArg0Word I).toByteArray.write 0
        (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
          (endSnipDogIlksReturnMem I outDog) 128 32)
        132 32 := by
  unfold endSnipVatIlksCallMem endFlowVatIlksSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_1858_taken_memory]
  rw [endSnipDogIlksReturnMem_mload64 I outDog hout h128]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]

theorem endSnipVatIlksMemSel_size_ge160 (I : ExecutionEnv) (outDog : ByteArray) :
    160 ≤ (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endFlowVatIlksSelectorEncodedWord (endSnipDogIlksReturnMem I outDog) 128

theorem endSnipVatIlksCallMem_size_ge164 (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    164 ≤ (endSnipVatIlksCallMem I outDog).size := by
  rw [endSnipVatIlksCallMem_eq_full I outDog hout h128]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32)
    132

theorem endSnipVatIlksCallMem_readSelector (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endSnipVatIlksCallMem I outDog).readWithPadding 128 4 = ilksSelector := by
  rw [endSnipVatIlksCallMem_eq_full I outDog hout h128]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have hge := endSnipVatIlksMemSel_size_ge160 I outDog; omega) (by omega)
    (by have hge := endSnipVatIlksMemSel_size_ge160 I outDog; omega) (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSnipDogIlksReturnMem I outDog) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFlowVatIlksSelectorEncodedWord_prefix]

theorem endSnipVatIlksCallMem_readIlk (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endSnipVatIlksCallMem I outDog).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSnipVatIlksCallMem_eq_full I outDog hout h128]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32)
    132

theorem endSnipVatIlksCallMem_readCallData (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endSnipVatIlksCallMem I outDog).readWithPadding 128 36 =
      endFlowVatIlksEncodedCall I := by
  have hsize := endSnipVatIlksCallMem_size_ge164 I outDog hout h128
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSnipVatIlksCallMem I outDog) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSnipVatIlksCallMem_readSelector I outDog hout h128,
    endSnipVatIlksCallMem_readIlk I outDog hout h128]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFlowVatIlksEncodedCall, endFlowVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

theorem endSnipVatIlksMemSel_size (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32).size = 256 := by
  exact toByteArray_write32_size_of_le (endSnipDogIlksReturnMem I outDog)
    endFlowVatIlksSelectorEncodedWord 128 256 256
    (endSnipDogIlksReturnMem_size I outDog hout h128)
    (by rw [endSnipDogIlksReturnMem_size I outDog hout h128]; omega)
    (by omega)

theorem endSnipVatIlksCallMem_size (I : ExecutionEnv) (outDog : ByteArray)
    (hout : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    (endSnipVatIlksCallMem I outDog).size = 256 := by
  rw [endSnipVatIlksCallMem_eq_full I outDog hout h128]
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSnipDogIlksReturnMem I outDog) 128 32)
    (endArg0Word I) 132 256 256
    (endSnipVatIlksMemSel_size I outDog hout h128)
    (by rw [endSnipVatIlksMemSel_size I outDog hout h128]; omega)
    (by omega)

theorem endSnipVatIlksReturnMem_size (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipVatIlksReturnMem I outDog outVat).size = 288 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSnipVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outVat (endSnipVatIlksCallMem I outDog) 128 160
    (by decide) h160
    (by rw [endSnipVatIlksCallMem_size I outDog houtDog h128]; omega)
    (by rw [endSnipVatIlksCallMem_size I outDog houtDog h128]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSnipVatIlksCallMem_size I outDog houtDog h128]
  omega

theorem endSnipVatIlksReturnMem_read64 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipVatIlksReturnMem I outDog outVat).readWithPadding 64 32 =
      (endSnipVatIlksCallMem I outDog).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSnipVatIlksReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend outVat (endSnipVatIlksCallMem I outDog) 128 160 64
    (by decide) h160
    (by rw [endSnipVatIlksCallMem_size I outDog houtDog h128]; omega)
    (by omega)

theorem endSnipVatIlksReturnMem_mload64 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipVatIlksReturnMem I outDog outVat)
    (by rw [endSnipVatIlksReturnMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by rw [endSnipVatIlksReturnMem_read64 I outDog outVat houtDog h128 houtVat h160,
      endSnipVatIlksCallMem_read64 I outDog houtDog h128])

theorem endSnipVatIlksReturnMem_read160 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipVatIlksReturnMem I outDog outVat).readWithPadding 160 32 =
      outVat.extract 32 64 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat = 160 := by
    rw [callCopyLength_toNat outVat (⟨160⟩ : UInt256) houtVat]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSnipVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outVat (endSnipVatIlksCallMem I outDog) 128 160
    (by decide) h160
    (by rw [endSnipVatIlksCallMem_size I outDog houtDog h128]; omega)
    (by rw [endSnipVatIlksCallMem_size I outDog houtDog h128]; omega)]
  have hpre : ((endSnipVatIlksCallMem I outDog).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipVatIlksCallMem_size I outDog houtDog h128]
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

theorem endSnipVatIlksReturnMem_mload160 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 160) (endSnipVatIlksReturnMem I outDog outVat) =
      endFlowVatIlksRateWord outVat := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSnipVatIlksReturnMem_size I outDog outVat houtDog h128 houtVat h160]
    omega)]
  rw [endSnipVatIlksReturnMem_read160 I outDog outVat houtDog h128 houtVat h160]
  change UInt256.ofNat (fromByteArrayBigEndian (outVat.extract 32 64)) =
    ABI.bytesToWord ((outVat.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

theorem endSnipSalesSelectorEncodedWord_prefix :
    (endSnipSalesSelectorEncodedWord.toByteArray).extract 0 4 = salesSelector := by
  native_decide

theorem endSnipSalesCallMem_eq_full (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    endSnipSalesCallMem I outDog outVat =
      (endArg1Word I).toByteArray.write 0
        (endSnipSalesSelectorEncodedWord.toByteArray.write 0
          (endSnipVatIlksReturnMem I outDog outVat) 128 32)
        132 32 := by
  unfold endSnipSalesCallMem endSnipSalesSelectorEncodedWord endSnipSalesSelectorWord
  dsimp [endRuntimeBlocks.endRuntime_block_1984_taken_memory]
  rw [endSnipVatIlksReturnMem_mload64 I outDog outVat houtDog h128 houtVat h160]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]

theorem endSnipSalesMemSel_size (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesSelectorEncodedWord.toByteArray.write 0
      (endSnipVatIlksReturnMem I outDog outVat) 128 32).size = 288 := by
  exact toByteArray_write32_size_of_le (endSnipVatIlksReturnMem I outDog outVat)
    endSnipSalesSelectorEncodedWord 128 288 288
    (endSnipVatIlksReturnMem_size I outDog outVat houtDog h128 houtVat h160)
    (by rw [endSnipVatIlksReturnMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)

theorem endSnipSalesCallMem_size (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesCallMem I outDog outVat).size = 288 := by
  rw [endSnipSalesCallMem_eq_full I outDog outVat houtDog h128 houtVat h160]
  exact toByteArray_write32_size_of_le
    (endSnipSalesSelectorEncodedWord.toByteArray.write 0
      (endSnipVatIlksReturnMem I outDog outVat) 128 32)
    (endArg1Word I) 132 288 288
    (endSnipSalesMemSel_size I outDog outVat houtDog h128 houtVat h160)
    (by rw [endSnipSalesMemSel_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)

theorem endSnipSalesCallMem_read64 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesCallMem I outDog outVat).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSnipSalesCallMem_eq_full I outDog outVat houtDog h128 houtVat h160]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1Word I)
    (endSnipSalesSelectorEncodedWord.toByteArray.write 0
      (endSnipVatIlksReturnMem I outDog outVat) 128 32)
    132 64
    (by rw [endSnipSalesMemSel_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSnipSalesSelectorEncodedWord (endSnipVatIlksReturnMem I outDog outVat) 128 64
    (by rw [endSnipVatIlksReturnMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)]
  rw [endSnipVatIlksReturnMem_read64 I outDog outVat houtDog h128 houtVat h160,
    endSnipVatIlksCallMem_read64 I outDog houtDog h128]

theorem endSnipSalesCallMem_mload64 (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    memLoad (UInt256.ofNat 64) (endSnipSalesCallMem I outDog outVat) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipSalesCallMem I outDog outVat)
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (endSnipSalesCallMem_read64 I outDog outVat houtDog h128 houtVat h160)

theorem endSnipSalesCallMem_readSelector (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesCallMem I outDog outVat).readWithPadding 128 4 = salesSelector := by
  rw [endSnipSalesCallMem_eq_full I outDog outVat houtDog h128 houtVat h160]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endSnipSalesMemSel_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)
    (by rw [endSnipSalesMemSel_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSnipSalesSelectorEncodedWord (endSnipVatIlksReturnMem I outDog outVat) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSnipSalesSelectorEncodedWord_prefix]

theorem endSnipSalesCallMem_readId (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesCallMem I outDog outVat).readWithPadding 132 32 =
      (endArg1Word I).toByteArray := by
  rw [endSnipSalesCallMem_eq_full I outDog outVat houtDog h128 houtVat h160]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg1Word I)
    (endSnipSalesSelectorEncodedWord.toByteArray.write 0
      (endSnipVatIlksReturnMem I outDog outVat) 128 32)
    132

theorem endSnipSalesCallMem_readCallData (I : ExecutionEnv) (outDog outVat : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    (endSnipSalesCallMem I outDog outVat).readWithPadding 128 36 =
      endSnipSalesEncodedCall I := by
  have hsize : 164 ≤ (endSnipSalesCallMem I outDog outVat).size := by
    rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]
    omega
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSnipSalesCallMem I outDog outVat) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSnipSalesCallMem_readSelector I outDog outVat houtDog h128 houtVat h160,
    endSnipSalesCallMem_readId I outDog outVat houtDog h128 houtVat h160]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSnipSalesEncodedCall, endSnipSalesPayloadBytes, toByteArray_eq_toBytesBE]

theorem endSnipSalesReturnMem_size (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSalesReturnMem I outDog outVat outSales).size = 320 := by
  have hcopy :
      (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat = 192 := by
    rw [callCopyLength_toNat outSales (⟨192⟩ : UInt256) houtSales]
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by native_decide]
    exact Nat.min_eq_left h192
  unfold endSnipSalesReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outSales (endSnipSalesCallMem I outDog outVat) 128 192
    (by decide) h192
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]
  omega

theorem endSnipSalesReturnMem_read64 (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSalesReturnMem I outDog outVat outSales).readWithPadding 64 32 =
      (endSnipSalesCallMem I outDog outVat).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat = 192 := by
    rw [callCopyLength_toNat outSales (⟨192⟩ : UInt256) houtSales]
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by native_decide]
    exact Nat.min_eq_left h192
  unfold endSnipSalesReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend outSales (endSnipSalesCallMem I outDog outVat) 128 192 64
    (by decide) h192
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by omega)

theorem endSnipSalesReturnMem_mload64 (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipSalesReturnMem I outDog outVat outSales)
    (by
      rw [endSnipSalesReturnMem_size I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by
      rw [endSnipSalesReturnMem_read64 I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192,
        endSnipSalesCallMem_read64 I outDog outVat houtDog h128 houtVat h160])

theorem endSnipSalesReturnMem_read160 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSalesReturnMem I outDog outVat outSales).readWithPadding 160 32 =
      outSales.extract 32 64 := by
  have hcopy :
      (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat = 192 := by
    rw [callCopyLength_toNat outSales (⟨192⟩ : UInt256) houtSales]
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by native_decide]
    exact Nat.min_eq_left h192
  unfold endSnipSalesReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outSales (endSnipSalesCallMem I outDog outVat) 128 192
    (by decide) h192
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)]
  have hpre : ((endSnipSalesCallMem I outDog outVat).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]
    omega
  have hcopySize : (outSales.extract 0 192).size = 192 := by
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
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 192 = 64 by omega]

theorem endSnipSalesReturnMem_read192 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSalesReturnMem I outDog outVat outSales).readWithPadding 192 32 =
      outSales.extract 64 96 := by
  have hcopy :
      (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat = 192 := by
    rw [callCopyLength_toNat outSales (⟨192⟩ : UInt256) houtSales]
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by native_decide]
    exact Nat.min_eq_left h192
  unfold endSnipSalesReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outSales (endSnipSalesCallMem I outDog outVat) 128 192
    (by decide) h192
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)]
  have hpre : ((endSnipSalesCallMem I outDog outVat).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]
    omega
  have hcopySize : (outSales.extract 0 192).size = 192 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 192 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 192 - 128 = 64 by omega, show 192 + 32 - 128 = 96 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 64 = 64 by omega, show min (0 + 96) 192 = 96 by omega]

theorem endSnipSalesReturnMem_read224 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSalesReturnMem I outDog outVat outSales).readWithPadding 224 32 =
      outSales.extract 96 128 := by
  have hcopy :
      (min (⟨192⟩ : UInt256) (UInt256.ofNat outSales.size)).toNat = 192 := by
    rw [callCopyLength_toNat outSales (⟨192⟩ : UInt256) houtSales]
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by native_decide]
    exact Nat.min_eq_left h192
  unfold endSnipSalesReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend outSales (endSnipSalesCallMem I outDog outVat) 128 192
    (by decide) h192
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)
    (by rw [endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]; omega)]
  have hpre : ((endSnipSalesCallMem I outDog outVat).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCallMem_size I outDog outVat houtDog h128 houtVat h160]
    omega
  have hcopySize : (outSales.extract 0 192).size = 192 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 224 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 224 - 128 = 96 by omega, show 224 + 32 - 128 = 128 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 96 = 96 by omega, show min (0 + 128) 192 = 128 by omega]

theorem endSnipSalesReturnMem_mload160 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 160) (endSnipSalesReturnMem I outDog outVat outSales) =
      endSnipSalesTabWord outSales := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSnipSalesReturnMem_size I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega)]
  rw [endSnipSalesReturnMem_read160 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  change UInt256.ofNat (fromByteArrayBigEndian (outSales.extract 32 64)) =
    ABI.bytesToWord ((outSales.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

theorem endSnipSalesReturnMem_mload192 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 192) (endSnipSalesReturnMem I outDog outVat outSales) =
      endSnipSalesLotWord outSales := by
  unfold memLoad
  rw [show (UInt256.ofNat 192).toNat = 192 from by native_decide]
  rw [if_neg (by
    rw [endSnipSalesReturnMem_size I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega)]
  rw [endSnipSalesReturnMem_read192 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  change UInt256.ofNat (fromByteArrayBigEndian (outSales.extract 64 96)) =
    ABI.bytesToWord ((outSales.toList.drop 64).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outSales 64]

theorem endSnipSalesReturnMem_mload224 (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 224) (endSnipSalesReturnMem I outDog outVat outSales) =
      endSnipSalesUsrWord outSales := by
  unfold memLoad
  rw [show (UInt256.ofNat 224).toNat = 224 from by native_decide]
  rw [if_neg (by
    rw [endSnipSalesReturnMem_size I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega)]
  rw [endSnipSalesReturnMem_read224 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  change UInt256.ofNat (fromByteArrayBigEndian (outSales.extract 96 128)) =
    ABI.bytesToWord ((outSales.toList.drop 96).take 32)
  rw [← endBytesToWord_drop_take32_eq_extract outSales 96]

theorem endSnipSuckSelectorEncodedWord_prefix :
    (endSnipSuckSelectorEncodedWord.toByteArray).extract 0 4 = suckSelector := by
  native_decide

theorem endSnipSuckMemSel_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckMemSel I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipSalesReturnMem I outDog outVat outSales)
    endSnipSuckSelectorEncodedWord 128 320 320
    (endSnipSalesReturnMem_size I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipSalesReturnMem_size I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipSuckMemVow0_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckMemVow0 σ I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipSuckMemSel I outDog outVat outSales) (endPackVowTarget σ I)
    132 320 320
    (endSnipSuckMemSel_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipSuckMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipSuckMemVow1_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckMemVow1 σ I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipSuckMemVow0 σ I outDog outVat outSales) (endPackVowTarget σ I)
    164 320 320
    (endSnipSuckMemVow0_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipSuckMemVow0_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipSuckCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipSuckMemVow1 σ I outDog outVat outSales)
    (endSnipSalesTabWord outSales) 196 320 320
    (endSnipSuckMemVow1_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipSuckCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesTabWord outSales)
    (endSnipSuckMemVow1 σ I outDog outVat outSales) 196 64
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSnipSuckMemVow0 σ I outDog outVat outSales) 164 64
    (by
      rw [endSnipSuckMemVow0_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSnipSuckMemSel I outDog outVat outSales) 132 64
    (by
      rw [endSnipSuckMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSnipSuckSelectorEncodedWord
    (endSnipSalesReturnMem I outDog outVat outSales) 128 64
    (by
      rw [endSnipSalesReturnMem_size I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [endSnipSalesReturnMem_read64 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192,
    endSnipSalesCallMem_read64 I outDog outVat houtDog h128 houtVat h160]

theorem endSnipSuckCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 64) (endSnipSuckCallMem σ I outDog outVat outSales) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipSuckCallMem σ I outDog outVat outSales)
    (by
      rw [endSnipSuckCallMem_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (endSnipSuckCallMem_read64 σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)

theorem endSnipSuckCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 128 4 =
      suckSelector := by
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by
      rw [endSnipSuckMemVow0_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)
    (by
      rw [endSnipSuckMemVow0_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSnipSuckMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)
    (by
      rw [endSnipSuckMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by decide) (by decide)]
  change ((endSnipSuckSelectorEncodedWord.toByteArray.write 0
      (endSnipSalesReturnMem I outDog outVat outSales) 128 32).readWithPadding
      128 4) = suckSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSnipSuckSelectorEncodedWord (endSnipSalesReturnMem I outDog outVat outSales) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSnipSuckSelectorEncodedWord_prefix]

theorem endSnipSuckCallMem_readVow0 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 132 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesTabWord outSales)
    (endSnipSuckMemVow1 σ I outDog outVat outSales) 196 132
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget σ I)
    (endSnipSuckMemVow0 σ I outDog outVat outSales) 164 132
    (by
      rw [endSnipSuckMemVow0_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  change ((endPackVowTarget σ I).toByteArray.write 0
      (endSnipSuckMemSel I outDog outVat outSales) 132 32).readWithPadding 132 32 =
    (endPackVowTarget σ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget σ I)
    (endSnipSuckMemSel I outDog outVat outSales) 132

theorem endSnipSuckCallMem_readVow1 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 164 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [toByteArray_write_read_below_of_gap_unbounded (endSnipSalesTabWord outSales)
    (endSnipSuckMemVow1 σ I outDog outVat outSales) 196 164
    (by
      rw [endSnipSuckMemVow1_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  change ((endPackVowTarget σ I).toByteArray.write 0
      (endSnipSuckMemVow0 σ I outDog outVat outSales) 164 32).readWithPadding 164 32 =
    (endPackVowTarget σ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget σ I)
    (endSnipSuckMemVow0 σ I outDog outVat outSales) 164

theorem endSnipSuckCallMem_readTab (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 196 32 =
      (endSnipSalesTabWord outSales).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endSnipSalesTabWord outSales)
    (endSnipSuckMemVow1 σ I outDog outVat outSales) 196

theorem endSnipSuckCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipSuckCallMem σ I outDog outVat outSales).readWithPadding 128 100 =
      endSnipSuckEncodedCall σ I outSales := by
  have hsize : 228 ≤ (endSnipSuckCallMem σ I outDog outVat outSales).size := by
    rw [endSnipSuckCallMem_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  rw [show 100 = 4 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipSuckCallMem σ I outDog outVat outSales) 128 4 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipSuckCallMem σ I outDog outVat outSales) 132 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipSuckCallMem σ I outDog outVat outSales) 164 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [endSnipSuckCallMem_readSelector σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipSuckCallMem_readVow0 σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipSuckCallMem_readVow1 σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipSuckCallMem_readTab σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_eq_toBytesBE (endPackVowTarget σ I)]
  rw [toByteArray_eq_toBytesBE (endSnipSalesTabWord outSales)]
  simp only [endSnipSuckEncodedCall, endSnipSuckPayloadBytes]
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem endSnipYankSelectorEncodedWord_prefix :
    (endSnipYankSelectorEncodedWord.toByteArray).extract 0 4 = yankSelector := by
  native_decide

theorem endSnipYankMemSel_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankMemSel σ I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipSuckCallMem σ I outDog outVat outSales)
    endSnipYankSelectorEncodedWord 128 320 320
    (endSnipSuckCallMem_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipSuckCallMem_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipYankCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankCallMem σ I outDog outVat outSales).size = 320 := by
  exact toByteArray_write32_size_of_le
    (endSnipYankMemSel σ I outDog outVat outSales) (endArg1Word I) 132 320 320
    (endSnipYankMemSel_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)
    (by
      rw [endSnipYankMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (by omega)

theorem endSnipYankCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankCallMem σ I outDog outVat outSales).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1Word I) (endSnipYankMemSel σ I outDog outVat outSales) 132 64
    (by
      rw [endSnipYankMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSnipYankSelectorEncodedWord
    (endSnipSuckCallMem σ I outDog outVat outSales) 128 64
    (by
      rw [endSnipSuckCallMem_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)]
  exact endSnipSuckCallMem_read64 σ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192

theorem endSnipYankCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    memLoad (UInt256.ofNat 64) (endSnipYankCallMem σ I outDog outVat outSales) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSnipYankCallMem σ I outDog outVat outSales)
    (by
      rw [endSnipYankCallMem_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega)
    (endSnipYankCallMem_read64 σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192)

theorem endSnipYankCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankCallMem σ I outDog outVat outSales).readWithPadding 128 4 =
      yankSelector := by
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by
      rw [endSnipYankMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by omega)
    (by
      rw [endSnipYankMemSel_size σ I outDog outVat outSales
        houtDog h128 houtVat h160 houtSales h192]
      omega) (by decide) (by decide)]
  change ((endSnipYankSelectorEncodedWord.toByteArray.write 0
      (endSnipSuckCallMem σ I outDog outVat outSales) 128 32).readWithPadding
      128 4) = yankSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSnipYankSelectorEncodedWord (endSnipSuckCallMem σ I outDog outVat outSales)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSnipYankSelectorEncodedWord_prefix]

theorem endSnipYankCallMem_readId (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankCallMem σ I outDog outVat outSales).readWithPadding 132 32 =
      (endArg1Word I).toByteArray := by
  exact toByteArray_write_read_back_of_gap_unbounded (endArg1Word I)
    (endSnipYankMemSel σ I outDog outVat outSales) 132

theorem endSnipYankCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    (endSnipYankCallMem σ I outDog outVat outSales).readWithPadding 128 36 =
      endSnipYankEncodedCall I := by
  have hsize : 164 ≤ (endSnipYankCallMem σ I outDog outVat outSales).size := by
    rw [endSnipYankCallMem_size σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
    omega
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSnipYankCallMem σ I outDog outVat outSales) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSnipYankCallMem_readSelector σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192,
    endSnipYankCallMem_readId σ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  rw [toByteArray_eq_toBytesBE (endArg1Word I)]
  simp only [endSnipYankEncodedCall, endSnipYankPayloadBytes]

theorem endSnipTagWord_init_eq {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz68 : 68 ≤ I.calldata.size) :
    endSnipTagWord (initState cA gh bl σ σ₀ g A I) I =
      endSnipTagWorldWord σ I := by
  exact endSkimTagWord_init_eq (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hsz68

theorem endSnipStore_get_tag_none (I : ExecutionEnv) :
    (endSnipStore I).get? "tag" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))).get? "tag") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "tag") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "tag")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endSnipStore_get_ilk (I : ExecutionEnv) :
    (endSnipStore I).get? "ilk" = some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "ilk") (endUIntValue (endArg1Word I)) (by decide)]
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endSnipStore_getElem_ilk (I : ExecutionEnv) :
    (endSnipStore I)["ilk"] = endArg0Bytes32Value I := by
  have hopt : (endSnipStore I)["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSnipStore_get_ilk I
  have hpos := getElem?_pos (endSnipStore I) "ilk" (by
    simp [endSnipStore, Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSnipStore_get_id (I : ExecutionEnv) :
    (endSnipStore I).get? "id" = some (endUIntValue (endArg1Word I)) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))).get? "id") = some (endUIntValue (endArg1Word I))
  exact store_get_self ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    "id" (endUIntValue (endArg1Word I))

theorem endSnipStore_getElem_id (I : ExecutionEnv) :
    (endSnipStore I)["id"] = endUIntValue (endArg1Word I) := by
  have hopt : (endSnipStore I)["id"]? = some (endUIntValue (endArg1Word I)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSnipStore_get_id I
  have hpos := getElem?_pos (endSnipStore I) "id" (by
    simp [endSnipStore, Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSnipStore_get_dog_none (I : ExecutionEnv) :
    (endSnipStore I).get? "dog" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
    (endUIntValue (endArg1Word I))).get? "dog") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "dog") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "dog")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalDogAddress_snip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.storage dogRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := endSnipStore I) (evm := evm) (slot := dogRef)
    (er := { base := "dog", steps := [] }) (wordSlot := UInt256.ofNat 3)
    (by simpa [dogRef] using endSnipStore_get_dog_none I)
    (by simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind])
    (by decide)
    (by
      rw [show (UInt256.ofNat 3) = (⟨3⟩ : UInt256) from by native_decide]
      exact endConfig_storage_dog)

theorem endEvalDogCodeGuard_snip_false (evm : EVM.State) (I : ExecutionEnv)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := endSnipStore I) (evm := evm) (receiver := .storage dogRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      solcAddrMask)
    (endEvalDogAddress_snip evm I) hnocode

theorem endEvalDogCodeGuard_snip_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := endSnipStore I) (evm := evm) (receiver := .storage dogRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      solcAddrMask)
    (endEvalDogAddress_snip evm I) hcode

theorem endEvalSnipDogIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endSnipStore I } evm
      [.var "ilk"] = .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endSnipStore_getElem_ilk]

theorem endEvalSnipDogIlkClip (evm : EVM.State) (I : ExecutionEnv)
    (outDog : ByteArray) :
    evalExpr? config (endSnipAfterDogIlksFrame I outDog) evm
      (.tupleGet (.var "dogIlk") 0) =
      .ok (endSnipClipValue outDog) := by
  simp [evalExpr?, endSnipAfterDogIlksFrame, collapseReturns, tupleGetValue?,
    endSnipDogIlksValues, endSnipClipValue, EvalResult.ofOption, EvalResult.bind, bind]

theorem endLetSnipClip (evm : EVM.State) (I : ExecutionEnv) (outDog : ByteArray) :
    ExecStmt config (endSnipAfterDogIlksFrame I outDog) evm
      (.letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0))
      (.ok (endSnipAfterClipFrame I outDog) evm) := by
  simpa [endSnipAfterClipFrame] using
    ExecStmt.letDecl (endEvalSnipDogIlkClip evm I outDog)

theorem endSnipAfterClipFrame_get_vat_none (I : ExecutionEnv) (outDog : ByteArray) :
    (endSnipAfterClipFrame I outDog).locals.get? "vat" = none := by
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "vat") = none
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "vat") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "vat") = none
  rw [store_get_ne (endSnipStore I) (k := "dogIlk") (a := "vat")
    (collapseReturns (endSnipDogIlksValues outDog)) (by decide)]
  simp [endSnipStore]

theorem endEvalVatAddress_snipAfterClip (evm : EVM.State) (I : ExecutionEnv)
    (outDog : ByteArray) :
    evalExpr? config (endSnipAfterClipFrame I outDog) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSnipAfterClipFrame I outDog).locals) (evm := evm) (slot := vatRef)
    (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSnipAfterClipFrame_get_vat_none I outDog)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVatCodeGuard_snipAfterClip_false (evm : EVM.State) (I : ExecutionEnv)
    (outDog : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSnipAfterClipFrame I outDog) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSnipAfterClipFrame I outDog).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_snipAfterClip evm I outDog) hnocode

theorem endEvalVatCodeGuard_snipAfterClip_true (evm : EVM.State) (I : ExecutionEnv)
    (outDog : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterClipFrame I outDog) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSnipAfterClipFrame I outDog).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
      solcAddrMask)
    (endEvalVatAddress_snipAfterClip evm I outDog) hcode

theorem endSnipAfterClipFrame_get_ilk (I : ExecutionEnv) (outDog : ByteArray) :
    (endSnipAfterClipFrame I outDog).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "ilk") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipStore I) (k := "dogIlk") (a := "ilk")
    (collapseReturns (endSnipDogIlksValues outDog)) (by decide)]
  exact endSnipStore_get_ilk I

theorem endSnipAfterClipFrame_getElem_ilk (I : ExecutionEnv) (outDog : ByteArray) :
    (endSnipAfterClipFrame I outDog).locals["ilk"] = endArg0Bytes32Value I := by
  have hopt :
      (endSnipAfterClipFrame I outDog).locals["ilk"]? =
        some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSnipAfterClipFrame_get_ilk I outDog
  have hpos := getElem?_pos (endSnipAfterClipFrame I outDog).locals "ilk" (by
    simp [endSnipAfterClipFrame, endSnipAfterDogIlksFrame, endSnipStore,
      Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalSnipVatIlksArgsAfterClip (evm : EVM.State) (I : ExecutionEnv)
    (outDog : ByteArray) :
    evalExprs? config (endSnipAfterClipFrame I outDog) evm [.var "ilk"] =
      .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endSnipAfterClipFrame_getElem_ilk I outDog]

theorem endEvalSnipRateFromVatIlk (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    evalExpr? config (endSnipAfterVatIlksFrame I outDog outVat) evm
      (.tupleGet (.var "vatIlk") 1) =
      .ok (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  simp [evalExpr?, endSnipAfterVatIlksFrame, collapseReturns, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind, endUIntValue]

theorem endLetSnipRate (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    ExecStmt config (endSnipAfterVatIlksFrame I outDog outVat) evm
      (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok (endSnipAfterRateFrame I outDog outVat) evm) := by
  simpa [endSnipAfterRateFrame] using
    ExecStmt.letDecl (endEvalSnipRateFromVatIlk evm I outDog outVat)

theorem endSnipAfterRateFrame_get_clip (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    (endSnipAfterRateFrame I outDog outVat).locals.get? "clip" =
      some (endSnipClipValue outDog) := by
  change ((((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "clip") =
    some (endSnipClipValue outDog)
  rw [store_get_ne ((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "clip")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "clip") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact store_get_self (endSnipAfterDogIlksFrame I outDog).locals "clip"
    (endSnipClipValue outDog)

theorem endSnipAfterRateFrame_get_id (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    (endSnipAfterRateFrame I outDog outVat).locals.get? "id" =
      some (endUIntValue (endArg1Word I)) := by
  change ((((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne ((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "id")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "id") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "id") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipStore I) (k := "dogIlk") (a := "id")
    (collapseReturns (endSnipDogIlksValues outDog)) (by decide)]
  exact endSnipStore_get_id I

theorem endSnipClipAddress_eq_mask (outDog : ByteArray) :
    AccountAddress.ofNat (endSnipDogIlksClipWord outDog).toNat =
      AccountAddress.ofNat (endSnipClipTarget outDog).toNat := by
  apply Fin.ext
  unfold AccountAddress.ofNat endSnipClipTarget
  change (endSnipDogIlksClipWord outDog).toNat % AccountAddress.size =
    (UInt256.land (endSnipDogIlksClipWord outDog) solcAddrMask).toNat % AccountAddress.size
  rw [u256_land_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (by norm_num [UInt256.size]))]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))]

theorem endEvalClipAddress_snipAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    evalExpr? config (endSnipAfterRateFrame I outDog outVat) evm (.var "clip") =
      .ok (endSnipClipValue outDog) := by
  simp [evalExpr?, EvalResult.ofOption]
  have hget := endSnipAfterRateFrame_get_clip I outDog outVat
  have hmem : "clip" ∈ (endSnipAfterRateFrame I outDog outVat).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSnipAfterRateFrame I outDog outVat).locals["clip"]? =
        some (endSnipClipValue outDog) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSnipAfterRateFrame I outDog outVat).locals "clip" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalClipAddress_snipAfterRate_masked (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    evalExpr? config (endSnipAfterRateFrame I outDog outVat) evm (.var "clip") =
      .ok (.address (AccountAddress.ofNat (endSnipClipTarget outDog).toNat)) := by
  rw [endEvalClipAddress_snipAfterRate evm I outDog outVat]
  simp [endSnipClipValue, endSnipClipAddress_eq_mask outDog]

theorem endEvalClipCodeGuard_snipAfterRate_false (evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) = ⟨0⟩) :
    evalExpr? config (endSnipAfterRateFrame I outDog outVat) evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSnipAfterRateFrame I outDog outVat).locals) (evm := evm)
    (receiver := .var "clip") (target := endSnipClipTarget outDog)
    (endEvalClipAddress_snipAfterRate_masked evm I outDog outVat) hnocode

theorem endEvalClipCodeGuard_snipAfterRate_true (evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterRateFrame I outDog outVat) evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSnipAfterRateFrame I outDog outVat).locals) (evm := evm)
    (receiver := .var "clip") (target := endSnipClipTarget outDog)
    (endEvalClipAddress_snipAfterRate_masked evm I outDog outVat) hcode

theorem endEvalSnipSalesArgsAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    evalExprs? config (endSnipAfterRateFrame I outDog outVat) evm [.var "id"] =
      .ok [endUIntValue (endArg1Word I)] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hget := endSnipAfterRateFrame_get_id I outDog outVat
  have hmem : "id" ∈ (endSnipAfterRateFrame I outDog outVat).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSnipAfterRateFrame I outDog outVat).locals["id"]? =
        some (endUIntValue (endArg1Word I)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSnipAfterRateFrame I outDog outVat).locals "id" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalSnipTabFromClipSale (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterSalesFrame I outDog outVat outSales) evm
      (.tupleGet (.var "clipSale") 1) =
      .ok (endSnipTabValue outSales) := by
  simp [evalExpr?, endSnipAfterSalesFrame, collapseReturns, tupleGetValue?,
    endSnipSalesValues, endSnipTabValue, EvalResult.ofOption, EvalResult.bind, bind,
    endUIntValue]

theorem endLetSnipTab (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    ExecStmt config (endSnipAfterSalesFrame I outDog outVat outSales) evm
      (.letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1))
      (.ok (endSnipAfterTabFrame I outDog outVat outSales) evm) := by
  simpa [endSnipAfterTabFrame] using
    ExecStmt.letDecl (endEvalSnipTabFromClipSale evm I outDog outVat outSales)

theorem endSnipAfterTabFrame_get_clipSale (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterTabFrame I outDog outVat outSales).locals.get? "clipSale" =
      some (collapseReturns (endSnipSalesValues outSales)) := by
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "clipSale") =
    some (collapseReturns (endSnipSalesValues outSales))
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "clipSale") (endSnipTabValue outSales) (by decide)]
  exact store_get_self (endSnipAfterRateFrame I outDog outVat).locals
    "clipSale" (collapseReturns (endSnipSalesValues outSales))

theorem endEvalSnipClipSaleAfterTab (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterTabFrame I outDog outVat outSales) evm
      (.var "clipSale") =
      .ok (collapseReturns (endSnipSalesValues outSales)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSnipAfterTabFrame_get_clipSale I outDog outVat outSales

theorem endEvalSnipLotFromClipSale (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterTabFrame I outDog outVat outSales) evm
      (.tupleGet (.var "clipSale") 2) =
      .ok (endSnipLotValue outSales) := by
  rw [evalExpr?]
  rw [endEvalSnipClipSaleAfterTab evm I outDog outVat outSales]
  simp [tupleGetValue?, collapseReturns, endSnipSalesValues, endSnipLotValue,
    EvalResult.bind, bind, endUIntValue]

theorem endLetSnipLot (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    ExecStmt config (endSnipAfterTabFrame I outDog outVat outSales) evm
      (.letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2))
      (.ok (endSnipAfterLotFrame I outDog outVat outSales) evm) := by
  simpa [endSnipAfterLotFrame] using
    ExecStmt.letDecl (endEvalSnipLotFromClipSale evm I outDog outVat outSales)

theorem endSnipAfterLotFrame_get_clipSale (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterLotFrame I outDog outVat outSales).locals.get? "clipSale" =
      some (collapseReturns (endSnipSalesValues outSales)) := by
  change (((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).get? "clipSale") =
    some (collapseReturns (endSnipSalesValues outSales))
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "clipSale") (endSnipLotValue outSales) (by decide)]
  exact endSnipAfterTabFrame_get_clipSale I outDog outVat outSales

theorem endEvalSnipClipSaleAfterLot (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterLotFrame I outDog outVat outSales) evm
      (.var "clipSale") =
      .ok (collapseReturns (endSnipSalesValues outSales)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSnipAfterLotFrame_get_clipSale I outDog outVat outSales

theorem endEvalSnipUsrFromClipSale (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterLotFrame I outDog outVat outSales) evm
      (.tupleGet (.var "clipSale") 3) =
      .ok (endSnipUsrValue outSales) := by
  rw [evalExpr?]
  rw [endEvalSnipClipSaleAfterLot evm I outDog outVat outSales]
  simp [tupleGetValue?, collapseReturns, endSnipSalesValues, endSnipUsrValue,
    EvalResult.bind, bind]

theorem endLetSnipUsr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    ExecStmt config (endSnipAfterLotFrame I outDog outVat outSales) evm
      (.letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3))
      (.ok (endSnipAfterUsrFrame I outDog outVat outSales) evm) := by
  simpa [endSnipAfterUsrFrame] using
    ExecStmt.letDecl (endEvalSnipUsrFromClipSale evm I outDog outVat outSales)

theorem endSnipAfterClipFrame_get_vow_none (I : ExecutionEnv) (outDog : ByteArray) :
    (endSnipAfterClipFrame I outDog).locals.get? "vow" = none := by
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "vow") = none
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "vow") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "vow") = none
  rw [store_get_ne (endSnipStore I) (k := "dogIlk") (a := "vow")
    (collapseReturns (endSnipDogIlksValues outDog)) (by decide)]
  simp [endSnipStore]

theorem endSnipAfterUsrFrame_get_vat_none (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterUsrFrame I outDog outVat outSales).locals.get? "vat" = none := by
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "vat") = none
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "vat")
    (endSnipUsrValue outSales) (by decide)]
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "vat") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "vat") = none
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "vat") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "vat") = none
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "vat") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  change ((((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "vat") = none
  rw [store_get_ne ((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "vat")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "vat") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact endSnipAfterClipFrame_get_vat_none I outDog

theorem endSnipAfterUsrFrame_get_vow_none (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterUsrFrame I outDog outVat outSales).locals.get? "vow" = none := by
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "vow") = none
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "vow")
    (endSnipUsrValue outSales) (by decide)]
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "vow") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "vow") = none
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "vow") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "vow") = none
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "vow") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  change ((((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "vow") = none
  rw [store_get_ne ((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "vow")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "vow") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  exact endSnipAfterClipFrame_get_vow_none I outDog

theorem endSnipAfterUsrFrame_get_tab (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterUsrFrame I outDog outVat outSales).locals.get? "tab" =
      some (endSnipTabValue outSales) := by
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "tab") = some (endSnipTabValue outSales)
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "tab")
    (endSnipUsrValue outSales) (by decide)]
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "tab") (endSnipLotValue outSales) (by decide)]
  exact store_get_self (endSnipAfterSalesFrame I outDog outVat outSales).locals
    "tab" (endSnipTabValue outSales)

theorem endEvalSnipTabAfterUsr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterUsrFrame I outDog outVat outSales) evm (.var "tab") =
      .ok (endSnipTabValue outSales) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSnipAfterUsrFrame_get_tab I outDog outVat outSales

theorem endEvalVatAddress_snipAfterUsr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterUsrFrame I outDog outVat outSales) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSnipAfterUsrFrame I outDog outVat outSales).locals) (evm := evm)
    (slot := vatRef) (er := { base := "vat", steps := [] }) (wordSlot := UInt256.ofNat 1)
    (endSnipAfterUsrFrame_get_vat_none I outDog outVat outSales)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVowAddress_snipAfterUsr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterUsrFrame I outDog outVat outSales) evm vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSnipAfterUsrFrame I outDog outVat outSales).locals) (evm := evm)
    (slot := vowRef) (er := { base := "vow", steps := [] }) (wordSlot := UInt256.ofNat 4)
    (endSnipAfterUsrFrame_get_vow_none I outDog outVat outSales)
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vow)

theorem endEvalVatCodeGuard_snipAfterUsr_false (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSnipAfterUsrFrame I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSnipAfterUsrFrame I outDog outVat outSales).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask)
    (endEvalVatAddress_snipAfterUsr evm I outDog outVat outSales) hnocode

theorem endEvalVatCodeGuard_snipAfterUsr_true (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterUsrFrame I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSnipAfterUsrFrame I outDog outVat outSales).locals) (evm := evm)
    (receiver := .storage vatRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask)
    (endEvalVatAddress_snipAfterUsr evm I outDog outVat outSales) hcode

theorem endEvalSnipSuckArgsAfterUsr (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExprs? config (endSnipAfterUsrFrame I outDog outVat outSales) evm
      [vowAddr, vowAddr, .var "tab"] =
      .ok [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask).toNat),
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask).toNat),
        endSnipTabValue outSales] := by
  simp [evalExprs?, EvalResult.bind, bind, pure,
    endEvalVowAddress_snipAfterUsr evm I outDog outVat outSales,
    endEvalSnipTabAfterUsr evm I outDog outVat outSales]

theorem endSnipAfterSuckFrame_get_clip (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterSuckFrame I outDog outVat outSales).locals.get? "clip" =
      some (endSnipClipValue outDog) := by
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "clip") = some (endSnipClipValue outDog)
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "clip") (collapseReturns []) (by decide)]
  change (((endSnipAfterLotFrame I outDog outVat outSales).locals.insert "usr"
      (endSnipUsrValue outSales)).get? "clip") = some (endSnipClipValue outDog)
  rw [store_get_ne (endSnipAfterLotFrame I outDog outVat outSales).locals
    (k := "usr") (a := "clip") (endSnipUsrValue outSales) (by decide)]
  change (((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).get? "clip") = some (endSnipClipValue outDog)
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "clip") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "clip") = some (endSnipClipValue outDog)
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "clip") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "clip") =
    some (endSnipClipValue outDog)
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "clip") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  exact endSnipAfterRateFrame_get_clip I outDog outVat

theorem endSnipAfterSuckFrame_get_id (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterSuckFrame I outDog outVat outSales).locals.get? "id" =
      some (endUIntValue (endArg1Word I)) := by
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "id") (collapseReturns []) (by decide)]
  change (((endSnipAfterLotFrame I outDog outVat outSales).locals.insert "usr"
      (endSnipUsrValue outSales)).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterLotFrame I outDog outVat outSales).locals
    (k := "usr") (a := "id") (endSnipUsrValue outSales) (by decide)]
  change (((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "id") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "id") = some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "id") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "id") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "id") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  exact endSnipAfterRateFrame_get_id I outDog outVat

theorem endEvalClipAddress_snipAfterSuck (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterSuckFrame I outDog outVat outSales) evm
      (.var "clip") =
      .ok (endSnipClipValue outDog) := by
  simp [evalExpr?, EvalResult.ofOption]
  have hget := endSnipAfterSuckFrame_get_clip I outDog outVat outSales
  have hmem : "clip" ∈ (endSnipAfterSuckFrame I outDog outVat outSales).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSnipAfterSuckFrame I outDog outVat outSales).locals["clip"]? =
        some (endSnipClipValue outDog) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSnipAfterSuckFrame I outDog outVat outSales).locals
    "clip" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalClipAddress_snipAfterSuck_masked (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterSuckFrame I outDog outVat outSales) evm
      (.var "clip") =
      .ok (.address (AccountAddress.ofNat (endSnipClipTarget outDog).toNat)) := by
  rw [endEvalClipAddress_snipAfterSuck evm I outDog outVat outSales]
  simp [endSnipClipValue, endSnipClipAddress_eq_mask outDog]

theorem endEvalClipCodeGuard_snipAfterSuck_false (evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) = ⟨0⟩) :
    evalExpr? config (endSnipAfterSuckFrame I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endSnipAfterSuckFrame I outDog outVat outSales).locals) (evm := evm)
    (receiver := .var "clip") (target := endSnipClipTarget outDog)
    (endEvalClipAddress_snipAfterSuck_masked evm I outDog outVat outSales) hnocode

theorem endEvalClipCodeGuard_snipAfterSuck_true (evm : EVM.State)
    (I : ExecutionEnv) (outDog outVat outSales : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterSuckFrame I outDog outVat outSales) evm
      (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endSnipAfterSuckFrame I outDog outVat outSales).locals) (evm := evm)
    (receiver := .var "clip") (target := endSnipClipTarget outDog)
    (endEvalClipAddress_snipAfterSuck_masked evm I outDog outVat outSales) hcode

theorem endEvalSnipYankArgsAfterSuck (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExprs? config (endSnipAfterSuckFrame I outDog outVat outSales) evm
      [.var "id"] =
      .ok [endUIntValue (endArg1Word I)] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  have hget := endSnipAfterSuckFrame_get_id I outDog outVat outSales
  have hmem : "id" ∈ (endSnipAfterSuckFrame I outDog outVat outSales).locals := by
    rw [Std.HashMap.mem_iff_isSome_getElem?]
    rw [← Std.HashMap.get?_eq_getElem?, hget]
    rfl
  have hopt :
      (endSnipAfterSuckFrame I outDog outVat outSales).locals["id"]? =
        some (endUIntValue (endArg1Word I)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSnipAfterSuckFrame I outDog outVat outSales).locals
    "id" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSnipAfterRateFrame_get_rate (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    (endSnipAfterRateFrame I outDog outVat).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  exact store_get_self (endSnipAfterVatIlksFrame I outDog outVat).locals "rate"
    (endUIntValue (endFlowVatIlksRateWord outVat))

theorem endSnipAfterRateFrame_get_ilk (I : ExecutionEnv)
    (outDog outVat : ByteArray) :
    (endSnipAfterRateFrame I outDog outVat).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne ((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outVat))) (k := "rate") (a := "ilk")
    (endUIntValue (endFlowVatIlksRateWord outVat)) (by decide)]
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "ilk") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "ilk") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipStore I) (k := "dogIlk") (a := "ilk")
    (collapseReturns (endSnipDogIlksValues outDog)) (by decide)]
  exact endSnipStore_get_ilk I

theorem endSnipAfterYankFrame_get_tab (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterYankFrame I outDog outVat outSales).locals.get? "tab" =
      some (endSnipTabValue outSales) := by
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "tab") = some (endSnipTabValue outSales)
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "tab") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "tab") = some (endSnipTabValue outSales)
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "tab") (collapseReturns []) (by decide)]
  exact endSnipAfterUsrFrame_get_tab I outDog outVat outSales

theorem endSnipAfterYankFrame_get_rate (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterYankFrame I outDog outVat outSales).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "rate") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "rate") (collapseReturns []) (by decide)]
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "rate") = some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "rate")
    (endSnipUsrValue outSales) (by decide)]
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "rate") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "rate") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "rate") =
    some (endUIntValue (endFlowVatIlksRateWord outVat))
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "rate") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  exact endSnipAfterRateFrame_get_rate I outDog outVat

theorem endSnipAfterYankFrame_get_ilk (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterYankFrame I outDog outVat outSales).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "ilk") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "ilk") (collapseReturns []) (by decide)]
  change ((((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).insert "usr" (endSnipUsrValue outSales)).get?
      "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
    (endSnipLotValue outSales)) (k := "usr") (a := "ilk")
    (endSnipUsrValue outSales) (by decide)]
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "ilk") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "ilk") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "ilk") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  exact endSnipAfterRateFrame_get_ilk I outDog outVat

theorem endEvalSnipTabAfterYank (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterYankFrame I outDog outVat outSales) evm (.var "tab") =
      .ok (endSnipTabValue outSales) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSnipAfterYankFrame_get_tab I outDog outVat outSales

theorem endEvalSnipRateAfterYank (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterYankFrame I outDog outVat outSales) evm (.var "rate") =
      .ok (endUIntValue (endFlowVatIlksRateWord outVat)) := by
  simpa [evalExpr?, EvalResult.ofOption] using
    endSnipAfterYankFrame_get_rate I outDog outVat outSales

theorem endEvalSnipArt (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩) :
    evalExpr? config (endSnipAfterYankFrame I outDog outVat outSales) evm
      (.binary .div (.var "tab") (.var "rate")) =
      .ok (endSnipArtValue outVat outSales) := by
  have hrateNatNe : (endFlowVatIlksRateWord outVat).toNat ≠ 0 := by
    intro hzero
    exact hrate (uint256_toNat_eq_zero hzero)
  have hrateIntNe : Int.ofNat (endFlowVatIlksRateWord outVat).toNat ≠ 0 := by
    intro hzero
    exact hrateNatNe (Int.ofNat_eq_zero.mp hzero)
  have hres :
      (endSnipArtWord outVat outSales).toNat =
        (endSnipSalesTabWord outSales).toNat / (endFlowVatIlksRateWord outVat).toNat := by
    unfold endSnipArtWord
    rw [udiv_toNat]
  have hdiv :
      Int.ofNat (endSnipSalesTabWord outSales).toNat /
          Int.ofNat (endFlowVatIlksRateWord outVat).toNat =
        Int.ofNat (endSnipArtWord outVat outSales).toNat := by
    rw [hres]
    change (((endSnipSalesTabWord outSales).toNat : Nat) : Int) /
        (((endFlowVatIlksRateWord outVat).toNat : Nat) : Int) =
      ((((endSnipSalesTabWord outSales).toNat /
        (endFlowVatIlksRateWord outVat).toNat : Nat) : Int))
    rw [← Int.natCast_div]
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipTabAfterYank evm I outDog outVat outSales]
  simp only [bind]
  rw [endEvalSnipRateAfterYank evm I outDog outVat outSales]
  change evalBinaryOp? BinaryOp.div (endSnipTabValue outSales)
      (endUIntValue (endFlowVatIlksRateWord outVat)) =
    EvalResult.ok (endSnipArtValue outVat outSales)
  change
    (if Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 then
        EvalResult.revert
      else
        EvalResult.ok (Value.int
          (Int.ofNat (endSnipSalesTabWord outSales).toNat /
            Int.ofNat (endFlowVatIlksRateWord outVat).toNat))) =
      EvalResult.ok (Value.int (Int.ofNat (endSnipArtWord outVat outSales).toNat))
  rw [if_neg hrateIntNe, hdiv]

theorem endEvalSnipArt_revert (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩) :
    evalExpr? config (endSnipAfterYankFrame I outDog outVat outSales) evm
      (.binary .div (.var "tab") (.var "rate")) = .revert := by
  have hrateInt : Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 := by
    rw [hrate]
    decide
  have hrateNat : (endFlowVatIlksRateWord outVat).toNat = 0 := by
    rw [hrate]
    decide
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSnipTabAfterYank evm I outDog outVat outSales]
  simp only [bind]
  rw [endEvalSnipRateAfterYank evm I outDog outVat outSales]
  change evalBinaryOp? BinaryOp.div (endSnipTabValue outSales)
      (endUIntValue (endFlowVatIlksRateWord outVat)) =
    EvalResult.revert
  change
    (if Int.ofNat (endFlowVatIlksRateWord outVat).toNat = 0 then
        EvalResult.revert
      else
        EvalResult.ok (Value.int
          (Int.ofNat (endSnipSalesTabWord outSales).toNat /
            Int.ofNat (endFlowVatIlksRateWord outVat).toNat))) =
      EvalResult.revert
  rw [if_pos hrateInt]

theorem endLetSnipArt (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat ≠ ⟨0⟩) :
    ExecStmt config (endSnipAfterYankFrame I outDog outVat outSales) evm
      (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      (.ok (endSnipAfterArtFrame I outDog outVat outSales) evm) := by
  simpa [endSnipAfterArtFrame] using
    ExecStmt.letDecl (endEvalSnipArt evm I outDog outVat outSales hrate)

theorem endLetSnipArtRevert (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (hrate : endFlowVatIlksRateWord outVat = ⟨0⟩) :
    ExecStmt config (endSnipAfterYankFrame I outDog outVat outSales) evm
      (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      .reverted :=
  ExecStmt.letDeclRevert (endEvalSnipArt_revert evm I outDog outVat outSales hrate)

theorem endSnipAfterArtFrame_get_art (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtFrame I outDog outVat outSales).locals.get? "art" =
      some (endSnipArtValue outVat outSales) := by
  exact store_get_self (endSnipAfterYankFrame I outDog outVat outSales).locals "art"
    (endSnipArtValue outVat outSales)

theorem endSnipAfterArtFrame_get_ilk (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtFrame I outDog outVat outSales).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "ilk") (endSnipArtValue outVat outSales) (by decide)]
  exact endSnipAfterYankFrame_get_ilk I outDog outVat outSales

theorem endSnipAfterArtFrame_get_Art_none (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    (endSnipAfterArtFrame I outDog outVat outSales).locals.get? "Art" = none := by
  change (((endSnipAfterYankFrame I outDog outVat outSales).locals.insert "art"
      (endSnipArtValue outVat outSales)).get? "Art") = none
  rw [store_get_ne (endSnipAfterYankFrame I outDog outVat outSales).locals
    (k := "art") (a := "Art") (endSnipArtValue outVat outSales) (by decide)]
  change (((endSnipAfterSuckFrame I outDog outVat outSales).locals.insert "_yank"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSnipAfterSuckFrame I outDog outVat outSales).locals
    (k := "_yank") (a := "Art") (collapseReturns []) (by decide)]
  change (((endSnipAfterUsrFrame I outDog outVat outSales).locals.insert "_suck"
      (collapseReturns [])).get? "Art") = none
  rw [store_get_ne (endSnipAfterUsrFrame I outDog outVat outSales).locals
    (k := "_suck") (a := "Art") (collapseReturns []) (by decide)]
  change (((endSnipAfterLotFrame I outDog outVat outSales).locals.insert "usr"
      (endSnipUsrValue outSales)).get? "Art") = none
  rw [store_get_ne (endSnipAfterLotFrame I outDog outVat outSales).locals
    (k := "usr") (a := "Art") (endSnipUsrValue outSales) (by decide)]
  change (((endSnipAfterTabFrame I outDog outVat outSales).locals.insert "lot"
      (endSnipLotValue outSales)).get? "Art") = none
  rw [store_get_ne (endSnipAfterTabFrame I outDog outVat outSales).locals
    (k := "lot") (a := "Art") (endSnipLotValue outSales) (by decide)]
  change (((endSnipAfterSalesFrame I outDog outVat outSales).locals.insert "tab"
      (endSnipTabValue outSales)).get? "Art") = none
  rw [store_get_ne (endSnipAfterSalesFrame I outDog outVat outSales).locals
    (k := "tab") (a := "Art") (endSnipTabValue outSales) (by decide)]
  change (((endSnipAfterRateFrame I outDog outVat).locals.insert "clipSale"
      (collapseReturns (endSnipSalesValues outSales))).get? "Art") = none
  rw [store_get_ne (endSnipAfterRateFrame I outDog outVat).locals
    (k := "clipSale") (a := "Art") (collapseReturns (endSnipSalesValues outSales))
    (by decide)]
  change (((endSnipAfterVatIlksFrame I outDog outVat).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outVat))).get? "Art") = none
  rw [store_get_ne (endSnipAfterVatIlksFrame I outDog outVat).locals
    (k := "rate") (a := "Art") (endUIntValue (endFlowVatIlksRateWord outVat))
    (by decide)]
  change (((endSnipAfterClipFrame I outDog).locals.insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outVat))).get? "Art") = none
  rw [store_get_ne (endSnipAfterClipFrame I outDog).locals
    (k := "vatIlk") (a := "Art") (collapseReturns (endFlowVatIlksValues outVat))
    (by decide)]
  change (((endSnipAfterDogIlksFrame I outDog).locals.insert "clip"
      (endSnipClipValue outDog)).get? "Art") = none
  rw [store_get_ne (endSnipAfterDogIlksFrame I outDog).locals
    (k := "clip") (a := "Art") (endSnipClipValue outDog) (by decide)]
  change (((endSnipStore I).insert "dogIlk"
      (collapseReturns (endSnipDogIlksValues outDog))).get? "Art") = none
  rw [store_get_ne (endSnipStore I)
    (k := "dogIlk") (a := "Art") (collapseReturns (endSnipDogIlksValues outDog))
    (by decide)]
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "id"
      (endUIntValue (endArg1Word I))).get? "Art") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "id") (a := "Art") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "Art")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalSnipArtVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtFrame I outDog outVat outSales) evm
      (.var "art") = .ok (endSnipArtValue outVat outSales) := by
  rw [evalExpr?]
  rw [endSnipAfterArtFrame_get_art I outDog outVat outSales]
  rfl

theorem endEvalSnipIlkVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) :
    evalExpr? config (endSnipAfterArtFrame I outDog outVat outSales) evm
      (.var "ilk") = .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSnipAfterArtFrame_get_ilk I outDog outVat outSales]
  rfl

theorem endEvalArtStorage_of_arg0 (evm : EVM.State) (I : ExecutionEnv)
    (frame : Frame)
    (hcontract : frame.contract = contract)
    (hbase : frame.locals.get? "Art" = none)
    (hilk : evalExpr? config frame evm (.var "ilk") = .ok (endArg0Bytes32Value I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config frame evm (.storage (ArtRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowArtWord evm I)) := by
  have hdrop := endFlowArg0Drop32 I hsz36
  have hkey :
      valueToKey? (endArg0Bytes32Value I) = some (endArg0Bytes32Key I) := by
    simp [endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?, bytes32Width,
      hdrop]
  rw [evalExpr_storage_scalar
    (er := { base := "Art", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (ArtSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := hbase)
    (her := by
      rw [evalStorageRef]
      simp only [ArtRef, evalStorageRefSteps, evalStorageRefStep, hilk, hkey,
        EvalResult.bind, EvalResult.ofOption, bind, pure, List.nil_append])
    (hty := by
      rw [hcontract]
      simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_Art (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endFlowArtWord]

theorem endEvalSnipAddArgs (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endSnipAfterArtFrame I outDog outVat outSales) evm
      [.storage (ArtRef (.var "ilk")), .var "art"] =
      .ok [endUIntValue (endFlowArtWord evm I), endSnipArtValue outVat outSales] := by
  let frame : Frame := endSnipAfterArtFrame I outDog outVat outSales
  have hsz36 : 36 ≤ I.calldata.size := by omega
  have hcontract : frame.contract = contract := by
    dsimp [frame]
    rfl
  have hbase : frame.locals.get? "Art" = none := by
    dsimp [frame]
    exact endSnipAfterArtFrame_get_Art_none I outDog outVat outSales
  have hilk : evalExpr? config frame evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
    dsimp [frame]
    exact endEvalSnipIlkVarAfterArt evm I outDog outVat outSales
  have hArtStorage : evalExpr? config frame evm (.storage (ArtRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowArtWord evm I)) :=
    endEvalArtStorage_of_arg0 evm I frame hcontract hbase hilk hsz36
  change evalExprs? config frame evm [.storage (ArtRef (.var "ilk")), .var "art"] =
    .ok [endUIntValue (endFlowArtWord evm I), endSnipArtValue outVat outSales]
  rw [evalExprs?]
  rw [hArtStorage]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSnipArtVarAfterArt evm I outDog outVat outSales]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endBindParams_add_snip_Art_art (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSales : ByteArray) :
    bindParams? addFunction.params
      [endUIntValue (endFlowArtWord evm I), endSnipArtValue outVat outSales] =
      some (endGenericMulStore (endFlowArtWord evm I)
        (endSnipArtWord outVat outSales)) := by
  simp [bindParams?, addFunction, endGenericMulStore, endSnipArtValue, endUIntValue]

theorem endSnipInternalAddOk (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endFlowArtWord evm I).toNat +
        (endSnipArtWord outVat outSales).toNat < UInt256.size) :
    ExecStmt config (endSnipAfterArtFrame I outDog outVat outSales) evm
      (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      (.ok (endSnipAfterArtNewFrame evm I outDog outVat outSales) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSnipAfterArtNewFrame,
    endSnipArtNewWord, endGenericAddResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSnipAfterArtFrame I outDog outVat outSales)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "ArtNew")
      (args := [.storage (ArtRef (.var "ilk")), .var "art"])
      (argVals := [endUIntValue (endFlowArtWord evm I), endSnipArtValue outVat outSales])
      (callee := addFunction)
      (locals := endGenericMulStore (endFlowArtWord evm I)
        (endSnipArtWord outVat outSales))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericAddZStore (endFlowArtWord evm I)
            (endSnipArtWord outVat outSales) })
      (value := some [endUIntValue (endSnipArtNewWord evm I outVat outSales)])
      (endEvalSnipAddArgs evm I outDog outVat outSales hsz68)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_snip_Art_art evm I outVat outSales)
      (by
        simpa [endSnipArtNewWord, endGenericAddResult] using
          endGenericAddFunctionOk evm (endFlowArtWord evm I)
            (endSnipArtWord outVat outSales) hfit)

theorem endSnipInternalAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endFlowArtWord evm I).toNat +
        (endSnipArtWord outVat outSales).toNat) :
    ExecStmt config (endSnipAfterArtFrame I outDog outVat outSales) evm
      (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSnipAfterArtFrame I outDog outVat outSales)
    (evm := evm) (name := "add") (retVar := "ArtNew")
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (argVals := [endUIntValue (endFlowArtWord evm I), endSnipArtValue outVat outSales])
    (callee := addFunction)
    (locals := endGenericMulStore (endFlowArtWord evm I) (endSnipArtWord outVat outSales))
    (endEvalSnipAddArgs evm I outDog outVat outSales hsz68)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_snip_Art_art evm I outVat outSales)
    (endGenericAddFunctionRevert evm (endFlowArtWord evm I)
      (endSnipArtWord outVat outSales) hover)

theorem endEvalTag_snip (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.storage (tagRef (.var "ilk"))) =
      .ok (endUIntValue (endSnipTagWord evm I)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [evalExpr_storage_scalar
    (er := { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (tagSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := endSnipStore_get_tag_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, tagRef,
        endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen,
        endSnipStore_getElem_ilk I])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_tag (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endSnipTagWord, endSnipTagSlot]

theorem endEvalTagGuard_snip_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_snip evm I hsz68, htag]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalTagGuard_snip_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_snip evm I hsz68]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : ¬ (endSnipTagWord evm I).toNat = 0 := by
    intro hzero
    exact htag (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endSnipBodyTagFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSnipStore I) snipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [snipTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalTagGuard_snip_false evm I hsz68 htag)))

theorem endSnipBodyDogNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord evm I ≠ ⟨0⟩)
    (hdogNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSnipStore I) snipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [snipTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_snip_true evm I hsz68 htag)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalDogCodeGuard_snip_false evm I hdogNoCode)))

theorem endSnipBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord evm I ≠ ⟨0⟩)
    (hdogCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSnipStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endSnipStore I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_snip_true evm I hsz68 htag)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDogCodeGuard_snip_true evm I hdogCode)) <|
      ExecBlock.nil)

theorem endX_snip_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd618 := endRuntimeBlocks.endRuntime_block_600_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_618
    (R := endRuntimeBlocks.endRuntime_block_600_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_600_fallthrough_stack])
    (by simpa using rd618)

theorem endX_snip_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1649⟩
      [endArg1Word I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd622 := endRuntimeBlocks.endRuntime_block_600_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd1649 := endRuntimeBlocks.endRuntime_block_622
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_600_taken_stack] using rd622)
  have hoff4 : (UInt256.ofNat 4).toNat = 4 := by native_decide
  have hoff36 : ((UInt256.ofNat 32) + (UInt256.ofNat 4)).toNat = 36 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_622_stack, endArg1Word, endArg0Word, calldataWord,
      hoff4, hoff36] using rd1649⟩

theorem endX_snip_tag_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSnipTagWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_snip_to_body (g := g) hsz68 hsize hreach
  have hcond :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) =
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSnipTagWorldWord σ I = ⟨0⟩
    exact htag
  obtain ⟨_, _, rd1669⟩ := endRuntimeBlocks.endRuntime_block_1649_fallthrough
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcond (by simpa using rdBody)
  exact endRuntimeBlocks.endRuntime_block_1669
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_1649_fallthrough_memory] using rd1669)

theorem endX_snip_dog_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSnipTagWorldWord σ I ≠ ⟨0⟩)
    (hdogNoCode : extCodeSizeWord σ (endSnipDogTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_snip_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSnipTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw1739, k1739, C1739, rd1739⟩ :=
    endRuntimeBlocks.endRuntime_block_1649_taken_packed
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondTag (by jump_dest) (by simpa using rdBody)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 3))))) =
        UInt256.ofNat 0 := by
    rw [hmaskGenerated, u256_land_comm solcAddrMask
      (storageRead I.codeOwner σ (UInt256.ofNat 3))]
    change UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endSnipDogTarget σ I))) =
      UInt256.ofNat 0
    rw [hdogNoCode]
    native_decide
  obtain ⟨_, _, _, rd1812⟩ :=
    endRuntimeBlocks.endRuntime_block_1739_fallthrough_packed
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by simpa using rd1739)
  exact endRuntimeBlocks.endRuntime_block_1812
    (R := endRuntimeBlocks.endRuntime_block_1739_fallthrough_stack
      (ee := I) (mem := endRuntimeBlocks.endRuntime_block_1649_taken_memory
        (mem := solcFreePtrMem) (x1 := endArg0Word I))
      (σ := σ) (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1739_fallthrough_stack])
    rd1812

set_option maxHeartbeats 12000000 in
theorem endX_snip_to_dog_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSnipTagWorldWord σ I ≠ ⟨0⟩)
    (hdogCode : extCodeSizeWord σ (endSnipDogTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1818⟩
      (endSnipDogIlksCallStack σ I sel) (endSnipDogIlksCallMem I) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_snip_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSnipTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw1739, k1739, C1739, rd1739⟩ :=
    endRuntimeBlocks.endRuntime_block_1649_taken_packed
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondTag (by jump_dest) (by simpa using rdBody)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 3))))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner σ (UInt256.ofNat 3))) ≠ UInt256.ofNat 0 := by
      rw [hmaskGenerated, u256_land_comm solcAddrMask
        (storageRead I.codeOwner σ (UInt256.ofNat 3))]
      simpa [endSnipDogTarget, endCageSlotTarget] using hdogCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw1816, k1816, C1816, rd1816⟩ :=
    endRuntimeBlocks.endRuntime_block_1739_taken_packed
      (mem := endSnipDogIlksBaseMem I)
      (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSnipDogIlksBaseMem, endSkimVatIlksBaseMem] using rd1739)
  have hbase : memLoad (UInt256.ofNat 64) (endSnipDogIlksBaseMem I) = ⟨128⟩ := by
    simpa [endSnipDogIlksBaseMem] using endSkimVatIlksBaseMem_mload64 I
  have hcall :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_1739_taken_memory
          (mem := endSnipDogIlksBaseMem I) (x1 := endArg0Word I)) = ⟨128⟩ := by
    simpa [endSnipDogIlksBaseMem, endSnipDogIlksCallMem, endSkimVatIlksBaseMem,
      endSkimVatIlksCallMem, endRuntimeBlocks.endRuntime_block_1739_taken_memory,
      endRuntimeBlocks.endRuntime_block_6795_taken_memory] using
      endSkimVatIlksCallMem_mload64 I
  have hcallAfterBase :
      memLoad (UInt256.ofNat 64)
        ((endArg0Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write
            0 (endSnipDogIlksBaseMem I) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_1739_taken_memory, hbase] using hcall
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_1739_taken_stack (ee := I)
          (mem := endSnipDogIlksBaseMem I) (σ := σ)
          (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord σ (endSnipDogTarget σ I)) ::
          endSnipDogIlksCallStack σ I sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_1739_taken_stack,
      endSnipDogIlksCallStack, endSnipDogIlksCallRest, endFlowVatIlksSelectorWord,
      endSnipDogTarget, endCageSlotTarget]
    rw [hbase, hcallAfterBase, hlen, hend, hmaskGenerated]
    rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 3))]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 128 = (⟨128⟩ : UInt256) from by native_decide]
  have rd1816' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1816⟩
        (UInt256.isZero (extCodeSizeWord σ (endSnipDogTarget σ I)) ::
          endSnipDogIlksCallStack σ I sel)
        (endSnipDogIlksCallMem I) aw1816 ByteArray.empty (cA, σ) k1816 C1816 := by
    simpa [hstackTaken, endSnipDogIlksCallMem, endSnipDogIlksBaseMem,
      endSkimVatIlksCallMem, endSkimVatIlksBaseMem,
      endRuntimeBlocks.endRuntime_block_1739_taken_memory,
      endRuntimeBlocks.endRuntime_block_6795_taken_memory] using rd1816
  have rd1818 := endRuntimeBlocks.endRuntime_block_1816
    (x0 := UInt256.isZero (extCodeSizeWord σ (endSnipDogTarget σ I)))
    (R := endSnipDogIlksCallStack σ I sel)
    (by simp [endSnipDogIlksCallStack, endSnipDogIlksCallRest]) rd1816'
  exact ⟨aw1816, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1816_stack] using rd1818⟩

set_option maxHeartbeats 12000000 in
theorem endSnipDogIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipDogIlksCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endSnipStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"] "dogIlk" ]
      (sequenceExit ⟨1858⟩
        (fun cur frame e =>
          frame = endSnipAfterDogIlksFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          128 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I cur.rdata),
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSnipDogIlksReturnMem I cur.rdata ∧
          cur.aw = endSnipAfterDogIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨1818⟩ = some (.GAS, .none); decide)
    (by simp [endSnipDogIlksCallStack, endSnipDogIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endSnipDogTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨1819⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSnipDogIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 3)
    rw [h.env] at hload
    rw [endEvalDogAddress_snip]
    rw [h.env]
    rw [show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from by native_decide]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 3))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endSnipDogTarget σ I).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSnipDogIlksArgs evm I
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endSnipDogTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endSnipDogTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_dogIlks I (by omega : 36 ≤ I.calldata.size)]
    change some (endFlowVatIlksEncodedCall I) =
      some ((endSnipDogIlksCallMem I).readWithPadding 128 36)
    rw [show endSnipDogIlksCallMem I = endSkimVatIlksCallMem I from rfl]
    rw [endSkimVatIlksCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h128 : 128 ≤ out.size
    · rw [endExternalDecode_dogIlks_ok h128]
      intro rd hrel
      have rd1820 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1820⟩
            ((⟨1⟩ : UInt256) :: endSnipDogIlksCallRest σ I sel)
            (endSnipDogIlksReturnMem I out) (endSnipDogIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipDogIlksCallStack, endSnipDogIlksCallRest,
          endSnipDogIlksCallAw, endSnipDogIlksReturnMem] using rd
      have rd1836 := endRuntimeBlocks.endRuntime_block_1820_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipDogIlksCallRest σ I sel)
        (by simp [endSnipDogIlksCallRest]) (by native_decide) (by jump_dest) rd1820
      have rd1836' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1836⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endSnipDogTarget σ I,
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipDogIlksReturnMem I out) (endSnipDogIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_1820_taken_stack,
          endSnipDogIlksCallRest] using rd1836
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 128) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide,
          ulit_toNat' out.size hout]
        exact h128
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 128)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd1858 := endRuntimeBlocks.endRuntime_block_1836_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endSnipDogTarget σ I)
        (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd1836'
      refine ⟨.ok (endSnipAfterDogIlksFrame I out) evm',
        Endpoint.reached (endSnipAfterDogIlksCursor I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSnipAfterDogIlksCursor, endSnipAfterDogIlksAw,
            endRuntimeBlocks.endRuntime_block_1836_taken_stack] using rd1858⟩
      · exact ⟨rfl, rfl, hrel, hout, h128, rfl, rfl, rfl⟩
    · have hshort : out.size < 128 := by omega
      rw [endExternalDecode_dogIlks_none_short hshort]
      intro rd
      have rd1820 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1820⟩
            ((⟨1⟩ : UInt256) :: endSnipDogIlksCallRest σ I sel)
            (endSnipDogIlksReturnMem I out) (endSnipDogIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipDogIlksCallStack, endSnipDogIlksCallRest,
          endSnipDogIlksCallAw, endSnipDogIlksReturnMem] using rd
      have rd1836 := endRuntimeBlocks.endRuntime_block_1820_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipDogIlksCallRest σ I sel)
        (by simp [endSnipDogIlksCallRest]) (by native_decide) (by jump_dest) rd1820
      have rd1836' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1836⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endSnipDogTarget σ I,
              ⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipDogIlksReturnMem I out) (endSnipDogIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_1820_taken_stack,
          endSnipDogIlksCallRest] using rd1836
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 128) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 128)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd1854 := endRuntimeBlocks.endRuntime_block_1836_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endSnipDogTarget σ I)
        (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd1836'
      exact endRuntimeBlocks.endRuntime_block_1854
        (R := endRuntimeBlocks.endRuntime_block_1836_fallthrough_stack
          (mem := endSnipDogIlksReturnMem I out) (rdata := out)
          (R := [⟨0⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_1836_fallthrough_stack])
        rd1854
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd1820 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1820⟩
          ((⟨0⟩ : UInt256) :: endSnipDogIlksCallRest σ I sel)
          (endSnipDogIlksReturnMem I out) (endSnipDogIlksCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSnipDogIlksCallStack, endSnipDogIlksCallRest,
        endSnipDogIlksCallAw, endSnipDogIlksReturnMem] using rd
    have rd1827 := endRuntimeBlocks.endRuntime_block_1820_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSnipDogIlksCallRest σ I sel)
      (by simp [endSnipDogIlksCallRest]) (by native_decide) rd1820
    exact endRuntimeBlocks.endRuntime_block_1827
      (R := endRuntimeBlocks.endRuntime_block_1820_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSnipDogIlksCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_1820_fallthrough_stack,
        endSnipDogIlksCallRest])
      rd1827

theorem endX_snip_vat_no_code_after_dog {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      (endSnipAfterDogIlksCursor I sel aw outDog world).stack
      (endSnipDogIlksReturnMem I outDog) (endSnipAfterDogIlksAw aw) outDog
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
  obtain ⟨aw1938, k1938, C1938, rd1938⟩ :=
    endRuntimeBlocks.endRuntime_block_1858_fallthrough_packed
      (x0 := UInt256.ofNat outDog.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1Word I) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hcondCode
      (by simpa [endSnipAfterDogIlksCursor] using rd)
  exact endRuntimeBlocks.endRuntime_block_1938
    (R := endRuntimeBlocks.endRuntime_block_1858_fallthrough_stack (ee := I)
      (mem := endSnipDogIlksReturnMem I outDog) (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog))
      (x3 := endArg1Word I) (x4 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1858_fallthrough_stack])
    rd1938

set_option maxHeartbeats 12000000 in
theorem endX_snip_after_dog_to_vat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1858⟩
      (endSnipAfterDogIlksCursor I sel aw outDog world).stack
      (endSnipDogIlksReturnMem I outDog) (endSnipAfterDogIlksAw aw) outDog
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1944⟩
      (endSnipVatIlksCallStack world.2 I outDog sel) (endSnipVatIlksCallMem I outDog)
      aw' outDog world k' C' := by
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
  obtain ⟨aw1942, k1942, C1942, rd1942⟩ :=
    endRuntimeBlocks.endRuntime_block_1858_taken_packed
      (x0 := UInt256.ofNat outDog.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1Word I) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSnipAfterDogIlksCursor] using rd)
  have hret64 := endSnipDogIlksReturnMem_mload64 I outDog houtDog h128
  have hclip := endSnipDogIlksReturnMem_mload128 I outDog houtDog h128
  have hclipLit :
      memLoad (⟨128⟩ : UInt256) (endSnipDogIlksReturnMem I outDog) =
        endSnipDogIlksClipWord outDog := by
    simpa [show UInt256.ofNat 128 = (⟨128⟩ : UInt256) from by native_decide] using hclip
  have hcall64 := endSnipVatIlksCallMem_mload64 I outDog houtDog h128
  have hcall64Generated :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_1858_taken_memory
          (mem := endSnipDogIlksReturnMem I outDog) (x4 := endArg0Word I)) =
        ⟨128⟩ := by
    simpa [endSnipVatIlksCallMem] using hcall64
  have hcallAfterRet :
      memLoad (UInt256.ofNat 64)
        ((endArg0Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write
            0 (endSnipDogIlksReturnMem I outDog) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_1858_taken_memory, hret64] using
      hcall64Generated
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_1858_taken_stack (ee := I)
          (mem := endSnipDogIlksReturnMem I outDog) (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64) (endSnipDogIlksReturnMem I outDog))
          (x3 := endArg1Word I) (x4 := endArg0Word I) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSnipVatIlksCallStack world.2 I outDog sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_1858_taken_stack,
      endSnipVatIlksCallStack, endSnipVatIlksCallRest, endFlowVatIlksSelectorWord,
      endPackVatTarget]
    rw [hret64, hcallAfterRet, hclipLit, hlen, hend, hmaskGenerated]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 160 = (⟨160⟩ : UInt256) from by native_decide]
  have rd1942' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1942⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSnipVatIlksCallStack world.2 I outDog sel)
        (endSnipVatIlksCallMem I outDog) aw1942 outDog world k1942 C1942 := by
    simpa [hstackTaken, endSnipVatIlksCallMem] using rd1942
  have rd1944 := endRuntimeBlocks.endRuntime_block_1942
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSnipVatIlksCallStack world.2 I outDog sel)
    (by simp [endSnipVatIlksCallStack, endSnipVatIlksCallRest]) rd1942'
  exact ⟨aw1942, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1942_stack] using rd1944⟩

set_option maxHeartbeats 12000000 in
theorem endSnipVatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipVatIlksCallCursor world I sel aw outDog rdata)
      k C (endSnipAfterClipFrame I outDog) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
      (sequenceExit ⟨1984⟩
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
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨1944⟩ = some (.GAS, .none); decide)
    (by simp [endSnipVatIlksCallStack, endSnipVatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨1945⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSnipVatIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_snipAfterClip evm I outDog]
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
    exact endEvalSnipVatIlksArgsAfterClip evm I outDog
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
      some ((endSnipVatIlksCallMem I outDog).readWithPadding 128 36)
    rw [endSnipVatIlksCallMem_readCallData I outDog houtDog h128]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h160 : 160 ≤ out.size
    · rw [endExternalDecode_vatIlks_ok h160]
      intro rd hrel
      have rd1946 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
            ((⟨1⟩ : UInt256) :: endSnipVatIlksCallRest world.2 I outDog sel)
            (endSnipVatIlksReturnMem I outDog out) (endSnipVatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipVatIlksCallStack, endSnipVatIlksCallRest,
          endSnipVatIlksCallAw, endSnipVatIlksReturnMem] using rd
      have rd1962 := endRuntimeBlocks.endRuntime_block_1946_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipVatIlksCallRest world.2 I outDog sel)
        (by simp [endSnipVatIlksCallRest]) (by native_decide) (by jump_dest) rd1946
      have rd1962' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1962⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipVatIlksReturnMem I outDog out) (endSnipVatIlksCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_1946_taken_stack,
          endSnipVatIlksCallRest] using rd1962
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
      have rd1984 := endRuntimeBlocks.endRuntime_block_1962_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd1962'
      refine ⟨.ok (endSnipAfterVatIlksFrame I outDog out) evm',
        Endpoint.reached (endSnipAfterVatIlksCursor I sel aw outDog out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSnipAfterVatIlksCursor, endSnipAfterVatIlksAw,
            endRuntimeBlocks.endRuntime_block_1962_taken_stack] using rd1984⟩
      · exact ⟨rfl, rfl, hrel, hout, h160, rfl, rfl, rfl⟩
    · have hshort : out.size < 160 := by omega
      rw [endExternalDecode_vatIlks_none_short hshort]
      intro rd
      have rd1946 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
            ((⟨1⟩ : UInt256) :: endSnipVatIlksCallRest world.2 I outDog sel)
            (endSnipVatIlksReturnMem I outDog out) (endSnipVatIlksCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipVatIlksCallStack, endSnipVatIlksCallRest,
          endSnipVatIlksCallAw, endSnipVatIlksReturnMem] using rd
      have rd1962 := endRuntimeBlocks.endRuntime_block_1946_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipVatIlksCallRest world.2 I outDog sel)
        (by simp [endSnipVatIlksCallRest]) (by native_decide) (by jump_dest) rd1946
      have rd1962' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1962⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipVatIlksReturnMem I outDog out) (endSnipVatIlksCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_1946_taken_stack,
          endSnipVatIlksCallRest] using rd1962
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
      have rd1980 := endRuntimeBlocks.endRuntime_block_1962_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd1962'
      exact endRuntimeBlocks.endRuntime_block_1980
        (R := endRuntimeBlocks.endRuntime_block_1962_fallthrough_stack
          (mem := endSnipVatIlksReturnMem I outDog out) (rdata := out)
          (R := [⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_1962_fallthrough_stack])
        rd1980
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd1946 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1946⟩
          ((⟨0⟩ : UInt256) :: endSnipVatIlksCallRest world.2 I outDog sel)
          (endSnipVatIlksReturnMem I outDog out) (endSnipVatIlksCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSnipVatIlksCallStack, endSnipVatIlksCallRest,
        endSnipVatIlksCallAw, endSnipVatIlksReturnMem] using rd
    have rd1953 := endRuntimeBlocks.endRuntime_block_1946_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSnipVatIlksCallRest world.2 I outDog sel)
      (by simp [endSnipVatIlksCallRest]) (by native_decide) rd1946
    exact endRuntimeBlocks.endRuntime_block_1953
      (R := endRuntimeBlocks.endRuntime_block_1946_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSnipVatIlksCallRest world.2 I outDog sel))
      (by simp [endRuntimeBlocks.endRuntime_block_1946_fallthrough_stack,
        endSnipVatIlksCallRest])
      rd1953

theorem endX_snip_clip_no_code_after_vat {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hclipNoCode : extCodeSizeWord world.2 (endSnipClipTarget outDog) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1984⟩
      (endSnipAfterVatIlksCursor I sel aw outDog outVat world).stack
      (endSnipVatIlksReturnMem I outDog outVat) (endSnipAfterVatIlksAw aw) outVat
      world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (endSnipDogIlksClipWord outDog)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endSnipClipTarget outDog := by
    rw [hmaskGenerated]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (endSnipDogIlksClipWord outDog)
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    rw [htarget, hclipNoCode]
    native_decide
  obtain ⟨aw2066, k2066, C2066, rd2066⟩ :=
    endRuntimeBlocks.endRuntime_block_1984_fallthrough_packed
      (x0 := UInt256.ofNat outVat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSnipDogIlksClipWord outDog)
      (x4 := endSnipDogIlksClipWord outDog) (x5 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcondCode
      (by simpa [endSnipAfterVatIlksCursor] using rd)
  exact endRuntimeBlocks.endRuntime_block_2066
    (R := endRuntimeBlocks.endRuntime_block_1984_fallthrough_stack
      (mem := endSnipVatIlksReturnMem I outDog outVat) (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat))
      (x3 := endSnipDogIlksClipWord outDog) (x4 := endSnipDogIlksClipWord outDog)
      (x5 := endArg1Word I) (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1984_fallthrough_stack])
    rd2066

set_option maxHeartbeats 12000000 in
theorem endX_snip_after_vat_to_sales_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (hclipCode : extCodeSizeWord world.2 (endSnipClipTarget outDog) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1984⟩
      (endSnipAfterVatIlksCursor I sel aw outDog outVat world).stack
      (endSnipVatIlksReturnMem I outDog outVat) (endSnipAfterVatIlksAw aw) outVat
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2072⟩
      (endSnipSalesCallStack I outDog outVat sel) (endSnipSalesCallMem I outDog outVat)
      aw' outVat world k' C' := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (endSnipDogIlksClipWord outDog)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endSnipClipTarget outDog := by
    rw [hmaskGenerated]
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (endSnipDogIlksClipWord outDog)
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠
        UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord world.2
            (UInt256.land (endSnipDogIlksClipWord outDog)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [htarget]
      exact hclipCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw2070, k2070, C2070, rd2070⟩ :=
    endRuntimeBlocks.endRuntime_block_1984_taken_packed
      (x0 := UInt256.ofNat outVat.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSnipDogIlksClipWord outDog)
      (x4 := endSnipDogIlksClipWord outDog) (x5 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSnipAfterVatIlksCursor] using rd)
  have hret64 := endSnipVatIlksReturnMem_mload64 I outDog outVat houtDog h128 houtVat h160
  have hrate := endSnipVatIlksReturnMem_mload160 I outDog outVat houtDog h128 houtVat h160
  have hcall64 := endSnipSalesCallMem_mload64 I outDog outVat houtDog h128 houtVat h160
  have hcall64Generated :
      memLoad (UInt256.ofNat 64)
        (endRuntimeBlocks.endRuntime_block_1984_taken_memory
          (mem := endSnipVatIlksReturnMem I outDog outVat) (x5 := endArg1Word I)) =
        ⟨128⟩ := by
    simpa [endSnipSalesCallMem] using hcall64
  have hcallAfterRet :
      memLoad (UInt256.ofNat 64)
        ((endArg1Word I).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 3052741367) (UInt256.ofNat 224)).toByteArray.write
            0 (endSnipVatIlksReturnMem I outDog outVat) (⟨128⟩ : UInt256).toNat 32)
          ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat 32) = ⟨128⟩ := by
    simpa [endRuntimeBlocks.endRuntime_block_1984_taken_memory, hret64] using
      hcall64Generated
  have hrateAt128 :
      memLoad ((UInt256.ofNat 32) + (⟨128⟩ : UInt256))
        (endSnipVatIlksReturnMem I outDog outVat) =
      endFlowVatIlksRateWord outVat := by
    simpa [show (UInt256.ofNat 32) + (⟨128⟩ : UInt256) =
        UInt256.ofNat 160 from by native_decide] using hrate
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_1984_taken_stack
          (mem := endSnipVatIlksReturnMem I outDog outVat) (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog outVat))
          (x3 := endSnipDogIlksClipWord outDog) (x4 := endSnipDogIlksClipWord outDog)
          (x5 := endArg1Word I) (R := [endArg0Word I, ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)) ::
          endSnipSalesCallStack I outDog outVat sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_1984_taken_stack, endSnipSalesCallStack,
      endSnipSalesCallRest, endSnipClipTarget, endSnipSalesSelectorWord]
    rw [htarget, hret64, hcallAfterRet, hrateAt128, hlen, hend]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 192 = (⟨192⟩ : UInt256) from by native_decide]
  have rd2070' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2070⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)) ::
          endSnipSalesCallStack I outDog outVat sel)
        (endSnipSalesCallMem I outDog outVat) aw2070 outVat world k2070 C2070 := by
    simpa [hstackTaken, endSnipSalesCallMem] using rd2070
  have rd2072 := endRuntimeBlocks.endRuntime_block_2070
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)))
    (R := endSnipSalesCallStack I outDog outVat sel)
    (by simp [endSnipSalesCallStack, endSnipSalesCallRest]) rd2070'
  exact ⟨aw2070, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_2070_stack] using rd2072⟩

set_option maxHeartbeats 12000000 in
theorem endSnipSalesExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipSalesCallCursor world I sel aw outDog outVat rdata)
      k C (endSnipAfterRateFrame I outDog outVat) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
          (perm := false) ]
      (sequenceExit ⟨2112⟩
        (fun cur frame e =>
          frame = endSnipAfterSalesFrame I outDog outVat cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          192 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endSnipSalesReturnMem I outDog outVat cur.rdata),
              ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSnipSalesReturnMem I outDog outVat cur.rdata ∧
          cur.aw = endSnipAfterSalesAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨2072⟩ = some (.GAS, .none); decide)
    (by simp [endSnipSalesCallCursor, endSnipSalesCallStack, endSnipSalesCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endSnipClipTarget outDog).toNat)
    (argVals := [endUIntValue (endArg1Word I)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨2073⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endSnipSalesCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro _
    exact endEvalClipAddress_snipAfterRate_masked evm I outDog outVat
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSnipSalesArgsAfterRate evm I outDog outVat
  · intro _
    apply Fin.ext
    show (endSnipClipTarget outDog).toNat % EVM.addressModulus % AccountAddress.size =
      (endSnipClipTarget outDog).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_sales_snip I]
    change some (endSnipSalesEncodedCall I) =
      some ((endSnipSalesCallMem I outDog outVat).readWithPadding 128 36)
    rw [endSnipSalesCallMem_readCallData I outDog outVat houtDog h128 houtVat h160]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h192 : 192 ≤ out.size
    · rw [endExternalDecode_sales_ok h192]
      intro rd hrel
      have rd2074 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2074⟩
            ((⟨1⟩ : UInt256) :: endSnipSalesCallRest I outDog outVat sel)
            (endSnipSalesReturnMem I outDog outVat out) (endSnipSalesCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipSalesCallCursor, endSnipSalesCallStack,
          endSnipSalesCallRest, endSnipSalesCallAw, endSnipSalesReturnMem] using rd
      have rd2090 := endRuntimeBlocks.endRuntime_block_2074_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipSalesCallRest I outDog outVat sel)
        (by simp [endSnipSalesCallRest]) (by native_decide) (by jump_dest) rd2074
      have rd2090' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2090⟩
            [⟨0⟩, ⟨164⟩, endSnipSalesSelectorWord, endSnipClipTarget outDog,
              ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipSalesReturnMem I outDog outVat out) (endSnipSalesCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_2074_taken_stack,
          endSnipSalesCallRest] using rd2090
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 192) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 192).toNat = 192 from by native_decide,
          ulit_toNat' out.size hout]
        exact h192
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 192)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd2112 := endRuntimeBlocks.endRuntime_block_2090_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endSnipSalesSelectorWord) (x3 := endSnipClipTarget outDog)
        (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd2090'
      refine ⟨.ok (endSnipAfterSalesFrame I outDog outVat out) evm',
        Endpoint.reached (endSnipAfterSalesCursor I sel aw outDog outVat out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSnipAfterSalesCursor, endSnipAfterSalesAw,
            endRuntimeBlocks.endRuntime_block_2090_taken_stack] using rd2112⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h192, rfl, rfl, rfl⟩
    · have hshort : out.size < 192 := by omega
      rw [endExternalDecode_sales_none_short hshort]
      intro rd
      have rd2074 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2074⟩
            ((⟨1⟩ : UInt256) :: endSnipSalesCallRest I outDog outVat sel)
            (endSnipSalesReturnMem I outDog outVat out) (endSnipSalesCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSnipSalesCallCursor, endSnipSalesCallStack,
          endSnipSalesCallRest, endSnipSalesCallAw, endSnipSalesReturnMem] using rd
      have rd2090 := endRuntimeBlocks.endRuntime_block_2074_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSnipSalesCallRest I outDog outVat sel)
        (by simp [endSnipSalesCallRest]) (by native_decide) (by jump_dest) rd2074
      have rd2090' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2090⟩
            [⟨0⟩, ⟨164⟩, endSnipSalesSelectorWord, endSnipClipTarget outDog,
              ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
              endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
              endArg1Word I, endArg0Word I, ⟨562⟩, sel]
            (endSnipSalesReturnMem I outDog outVat out) (endSnipSalesCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_2074_taken_stack,
          endSnipSalesCallRest] using rd2090
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 192) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 192).toNat = 192 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 192)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd2108 := endRuntimeBlocks.endRuntime_block_2090_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endSnipSalesSelectorWord) (x3 := endSnipClipTarget outDog)
        (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd2090'
      exact endRuntimeBlocks.endRuntime_block_2108
        (R := endRuntimeBlocks.endRuntime_block_2090_fallthrough_stack
          (mem := endSnipSalesReturnMem I outDog outVat out) (rdata := out)
          (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
            endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_2090_fallthrough_stack])
        rd2108
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd2074 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2074⟩
          ((⟨0⟩ : UInt256) :: endSnipSalesCallRest I outDog outVat sel)
          (endSnipSalesReturnMem I outDog outVat out) (endSnipSalesCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSnipSalesCallCursor, endSnipSalesCallStack,
        endSnipSalesCallRest, endSnipSalesCallAw, endSnipSalesReturnMem] using rd
    have rd2081 := endRuntimeBlocks.endRuntime_block_2074_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSnipSalesCallRest I outDog outVat sel)
      (by simp [endSnipSalesCallRest]) (by native_decide) rd2074
    exact endRuntimeBlocks.endRuntime_block_2081
      (R := endRuntimeBlocks.endRuntime_block_2074_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSnipSalesCallRest I outDog outVat sel))
      (by simp [endRuntimeBlocks.endRuntime_block_2074_fallthrough_stack,
        endSnipSalesCallRest])
      rd2081

abbrev endSnipAfterSalesRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outDog : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ outVat awSales,
      frame = endSnipAfterSalesFrame I outDog outVat cur.rdata ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      cur.rdata.size < UInt256.size ∧
      192 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat cur.rdata),
          ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endSnipSalesReturnMem I outDog outVat cur.rdata ∧
      cur.aw = endSnipAfterSalesAw awSales

set_option maxHeartbeats 12000000 in
theorem endSnipAfterVatIlksToSalesRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
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
      ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false))
      (sequenceExit ⟨2112⟩
        (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, houtVat, h160, hstack, hmem, haw⟩
  cases hframe
  have rd1984 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1984⟩
        [UInt256.ofNat cur0.rdata.size,
          memLoad (UInt256.ofNat 64) (endSnipVatIlksReturnMem I outDog cur0.rdata),
          ⟨0⟩, endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipVatIlksReturnMem I outDog cur0.rdata) (endSnipAfterVatIlksAw aw)
        cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsourceRate :
      ExecBlock config (endSnipAfterVatIlksFrame I outDog cur0.rdata) evm
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok (endSnipAfterRateFrame I outDog cur0.rdata) evm) :=
    ExecBlock.consNormal (endLetSnipRate evm I outDog cur0.rdata) ExecBlock.nil
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) =
        extCodeSizeWord cur0.world.2 (endSnipClipTarget outDog) :=
    (extCodeSizeWord_accountMapEquiv hrel.accounts (endSnipClipTarget outDog)).symm
  by_cases hclipNoCode :
      extCodeSizeWord cur0.world.2 (endSnipClipTarget outDog) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) = ⟨0⟩ := by
      rw [hsrcCodeEq, hclipNoCode]
    have hsourceChecked :
        ExecBlock config (endSnipAfterRateFrame I outDog cur0.rdata) evm
          (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false))
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalClipCodeGuard_snipAfterRate_false evm I outDog cur0.rdata hsrcNoCode)))
    have hsourceFull :
        ExecBlock config (endSnipAfterVatIlksFrame I outDog cur0.rdata) evm
          ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
            checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
              "clipSale" (perm := false))
          .reverted :=
      Reasoning.Theory.execBlock_append hsourceRate hsourceChecked
    have hrev := endX_snip_clip_no_code_after_vat
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outDog := outDog)
      (outVat := cur0.rdata) (k := k) (C := C) (world := cur0.world)
      hclipNoCode rd1984
    exact ⟨.reverted, .reverted, hsourceFull, hrev, by
      simp [sequenceExit, runtimeExit, functionResult]⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endSnipClipTarget outDog) ≠ ⟨0⟩ := by
      intro hzero
      exact hclipNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSnipAfterRateFrame I outDog cur0.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) ]
          (.ok (endSnipAfterRateFrame I outDog cur0.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalClipCodeGuard_snipAfterRate_true evm I outDog cur0.rdata hsrcCode))
        ExecBlock.nil
    obtain ⟨aw2072, k2072, C2072, rd2072⟩ :=
      endX_snip_after_vat_to_sales_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outDog := outDog)
        (outVat := cur0.rdata) (k := k) (C := C) (world := cur0.world)
        houtDog h128 houtVat h160 hclipNoCode rd1984
    have htailExact :=
      (endSnipSalesExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw2072) (outDog := outDog)
        (outVat := cur0.rdata) (rdata := cur0.rdata) (k := k2072) (C := C2072)
        (evm := evm) (world := cur0.world)
        houtDog h128 houtVat h160)
        (by simpa [endSnipSalesCallCursor] using rd2072) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterRateFrame I outDog cur0.rdata) evm
          [ .externalCall (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
              (perm := false) ]
          (sequenceExit ⟨2112⟩
            (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with
                ⟨hpcQ, hframeQ, hrelQ, _hstatic, houtSales, h192, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, cur0.rdata, aw2072, hframeQ, hrelQ, houtVat, h160,
                houtSales, h192, hstackQ, hmemQ, hawQ⟩
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
          (endSnipAfterRateFrame I outDog cur0.rdata) evm
          (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false))
          (sequenceExit ⟨2112⟩
            (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa using BlockProgress.prepend hsourceRate hcheckedProgress

theorem endSnipSuckCallMem_generated (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    endRuntimeBlocks.endRuntime_block_2112_memory (ee := I)
        (mem := endSnipSalesReturnMem I outDog outVat outSales) (σ := σ)
        (x1 := memLoad (UInt256.ofNat 64)
          (endSnipSalesReturnMem I outDog outVat outSales)) =
      endSnipSuckCallMem σ I outDog outVat outSales := by
  have hfree := endSnipSalesReturnMem_mload64 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have htab := endSnipSalesReturnMem_mload160 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endRuntimeBlocks.endRuntime_block_2112_memory
  rw [hfree]
  rw [show (⟨128⟩ : UInt256) + UInt256.ofNat 32 = UInt256.ofNat 160
      from by native_decide]
  rw [htab]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide,
    show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [hmask]

theorem endX_snip_vat_no_code_after_sales {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat outSales k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2112⟩
      (endSnipAfterSalesCursor I sel aw outDog outVat outSales world).stack
      (endSnipSalesReturnMem I outDog outVat outSales) (endSnipAfterSalesAw aw)
      outSales world k C) :
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
  have hfree := endSnipSalesReturnMem_mload64 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have htab := endSnipSalesReturnMem_mload160 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hlot := endSnipSalesReturnMem_mload192 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have husr := endSnipSalesReturnMem_mload224 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have htabAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesTabWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 32 =
        UInt256.ofNat 160 from by native_decide] using htab
  have hlotAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 64)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesLotWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 64 =
        UInt256.ofNat 192 from by native_decide] using hlot
  have husrAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 96)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesUsrWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 96 =
        UInt256.ofNat 224 from by native_decide] using husr
  have hmemGen := endSnipSuckCallMem_generated world.2 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hcall64 := endSnipSuckCallMem_mload64 world.2 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hstack2112 :
      endRuntimeBlocks.endRuntime_block_2112_stack
          (ee := I) (mem := endSnipSalesReturnMem I outDog outVat outSales)
          (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64)
            (endSnipSalesReturnMem I outDog outVat outSales))
          (x2 := (⟨0⟩ : UInt256))
          (R := [endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
            endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [endSnipSalesUsrWord outSales,
          storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
          ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
          endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_2112_stack]
    change
      [memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 96)
          (endSnipSalesReturnMem I outDog outVat outSales),
        storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_2112_memory
            (ee := I) (mem := endSnipSalesReturnMem I outDog outVat outSales)
            (σ := world.2)
            (x1 := memLoad (UInt256.ofNat 64)
              (endSnipSalesReturnMem I outDog outVat outSales))),
        memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales),
        ⟨0⟩,
        memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 64)
          (endSnipSalesReturnMem I outDog outVat outSales),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 32)
          (endSnipSalesReturnMem I outDog outVat outSales),
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [endSnipSalesUsrWord outSales,
        storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
        ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, husrAt, hlotAt, htabAt]
  obtain ⟨aw2191, k2191, C2191, rd2191⟩ :=
    endRuntimeBlocks.endRuntime_block_2112_packed
      (x0 := UInt256.ofNat outSales.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endSnipSalesReturnMem I outDog outVat outSales))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256)) (x4 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSnipAfterSalesCursor] using rd)
  have rd2191' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2191⟩
        [endSnipSalesUsrWord outSales,
          storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
          ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
          endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipSuckCallMem world.2 I outDog outVat outSales) aw2191 outSales
        world k2191 C2191 := by
    simpa [hstack2112, hmemGen] using rd2191
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask))) =
        UInt256.ofNat 0 := by
    rw [hvatTarget, hvatNoCode]
    native_decide
  obtain ⟨aw2228, k2228, C2228, rd2228⟩ :=
    endRuntimeBlocks.endRuntime_block_2191_fallthrough_packed
      (x0 := endSnipSalesUsrWord outSales)
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1)) (x2 := addrMask)
      (x3 := (⟨128⟩ : UInt256)) (x4 := (⟨128⟩ : UInt256))
      (x5 := (⟨0⟩ : UInt256))
      (R := [endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond rd2191'
  exact endRuntimeBlocks.endRuntime_block_2228
    (R := endRuntimeBlocks.endRuntime_block_2191_fallthrough_stack (σ := world.2)
      (x0 := endSnipSalesUsrWord outSales)
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1)) (x2 := addrMask)
      (x3 := (⟨128⟩ : UInt256)) (x4 := (⟨128⟩ : UInt256))
      (R := [endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_2191_fallthrough_stack])
    rd2228

theorem endX_snip_after_sales_to_suck_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat outSales k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2112⟩
      (endSnipAfterSalesCursor I sel aw outDog outVat outSales world).stack
      (endSnipSalesReturnMem I outDog outVat outSales) (endSnipAfterSalesAw aw)
      outSales world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2234⟩
      (endSnipSuckCallStack world.2 I outDog outVat outSales sel)
      (endSnipSuckCallMem world.2 I outDog outVat outSales) aw' outSales world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hvatTarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) addrMask =
        endPackVatTarget world.2 I := by
    rw [hmask]
    simp [endPackVatTarget, u256_land_comm]
  have hfree := endSnipSalesReturnMem_mload64 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have htab := endSnipSalesReturnMem_mload160 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hlot := endSnipSalesReturnMem_mload192 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have husr := endSnipSalesReturnMem_mload224 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have htabAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesTabWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 32 =
        UInt256.ofNat 160 from by native_decide] using htab
  have hlotAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 64)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesLotWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 64 =
        UInt256.ofNat 192 from by native_decide] using hlot
  have husrAt :
      memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 96)
          (endSnipSalesReturnMem I outDog outVat outSales) =
        endSnipSalesUsrWord outSales := by
    simpa [show (⟨128⟩ : UInt256) + UInt256.ofNat 96 =
        UInt256.ofNat 224 from by native_decide] using husr
  have hmemGen := endSnipSuckCallMem_generated world.2 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hcall64 := endSnipSuckCallMem_mload64 world.2 I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hstack2112 :
      endRuntimeBlocks.endRuntime_block_2112_stack
          (ee := I) (mem := endSnipSalesReturnMem I outDog outVat outSales)
          (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64)
            (endSnipSalesReturnMem I outDog outVat outSales))
          (x2 := (⟨0⟩ : UInt256))
          (R := [endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
            endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel]) =
        [endSnipSalesUsrWord outSales,
          storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
          ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
          endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel] := by
    dsimp [endRuntimeBlocks.endRuntime_block_2112_stack]
    change
      [memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 96)
          (endSnipSalesReturnMem I outDog outVat outSales),
        storageRead I.codeOwner world.2 (UInt256.ofNat 1),
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_2112_memory
            (ee := I) (mem := endSnipSalesReturnMem I outDog outVat outSales)
            (σ := world.2)
            (x1 := memLoad (UInt256.ofNat 64)
              (endSnipSalesReturnMem I outDog outVat outSales))),
        memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales),
        ⟨0⟩,
        memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 64)
          (endSnipSalesReturnMem I outDog outVat outSales),
        memLoad
          (memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat outSales) +
            UInt256.ofNat 32)
          (endSnipSalesReturnMem I outDog outVat outSales),
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      [endSnipSalesUsrWord outSales,
        storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
        ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
    rw [hmemGen, hcall64, hfree, husrAt, hlotAt, htabAt]
  obtain ⟨aw2191, k2191, C2191, rd2191⟩ :=
    endRuntimeBlocks.endRuntime_block_2112_packed
      (x0 := UInt256.ofNat outSales.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endSnipSalesReturnMem I outDog outVat outSales))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256)) (x4 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by simpa [endSnipAfterSalesCursor] using rd)
  have rd2191' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2191⟩
        [endSnipSalesUsrWord outSales,
          storageRead I.codeOwner world.2 (UInt256.ofNat 1), addrMask,
          ⟨128⟩, ⟨128⟩, ⟨0⟩, endSnipSalesLotWord outSales,
          endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipSuckCallMem world.2 I outDog outVat outSales) aw2191 outSales
        world k2191 C2191 := by
    simpa [hstack2112, hmemGen] using rd2191
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
  obtain ⟨aw2232, k2232, C2232, rd2232⟩ :=
    endRuntimeBlocks.endRuntime_block_2191_taken_packed
      (x0 := endSnipSalesUsrWord outSales)
      (x1 := storageRead I.codeOwner world.2 (UInt256.ofNat 1)) (x2 := addrMask)
      (x3 := (⟨128⟩ : UInt256)) (x4 := (⟨128⟩ : UInt256))
      (x5 := (⟨0⟩ : UInt256))
      (R := [endSnipSalesLotWord outSales, endSnipSalesTabWord outSales,
        endFlowVatIlksRateWord outVat, endSnipDogIlksClipWord outDog,
        endSnipDogIlksClipWord outDog, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd2191'
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 100 = ⟨100⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 100 = ⟨228⟩ := by
    native_decide
  have rd2232' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2232⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSnipSuckCallStack world.2 I outDog outVat outSales sel)
        (endSnipSuckCallMem world.2 I outDog outVat outSales) aw2232 outSales
        world k2232 C2232 := by
    simpa [endRuntimeBlocks.endRuntime_block_2191_taken_stack, endSnipSuckCallStack,
      endSnipSuckCallRest, hvatTarget, hlen, hend, endSnipSuckSelectorWord]
      using rd2232
  have rd2234 := endRuntimeBlocks.endRuntime_block_2232
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
    (R := endSnipSuckCallStack world.2 I outDog outVat outSales sel)
    (by simp [endSnipSuckCallStack, endSnipSuckCallRest]) rd2232'
  exact ⟨aw2232, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_2232_stack] using rd2234⟩

set_option maxHeartbeats 12000000 in
theorem endSnipSuckExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outDog outVat outSales k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipSuckCallCursor world I sel aw outDog outVat outSales rdata)
      k C (endSnipAfterUsrFrame I outDog outVat outSales) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ]
      (sequenceExit ⟨2252⟩
        (fun cur frame e =>
          frame = endSnipAfterSuckFrame I outDog outVat outSales ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSnipAfterSuckStack world.2 I outDog outVat outSales sel ∧
          cur.mem = endSnipSuckCallMem world.2 I outDog outVat outSales ∧
          cur.aw = endSnipSuckCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨2234⟩ = some (.GAS, .none); decide)
    (by simp [endSnipSuckCallCursor, endSnipSuckCallStack, endSnipSuckCallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      endSnipTabValue outSales])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨2235⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSnipSuckCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_snipAfterUsr evm I outDog outVat outSales]
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
    rw [endEvalSnipSuckArgsAfterUsr evm I outDog outVat outSales]
    rw [h.env]
    change EvalResult.ok
      [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        endSnipTabValue outSales] =
      EvalResult.ok
        [.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          endSnipTabValue outSales]
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
    rw [endExternalEncode_suck_snip world.2 I outSales]
    change some (endSnipSuckEncodedCall world.2 I outSales) =
      some ((endSnipSuckCallMem world.2 I outDog outVat outSales).readWithPadding 128 100)
    rw [endSnipSuckCallMem_readCallData world.2 I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_suck out]
    intro rd hrel
    have rd2236 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2236⟩
          ((⟨1⟩ : UInt256) :: endSnipSuckCallRest world.2 I outDog outVat outSales sel)
          (endSnipSuckCallMem world.2 I outDog outVat outSales)
          (endSnipSuckCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipSuckCallCursor,
        endSnipSuckCallStack, endSnipSuckCallRest, endSnipSuckCallAw] using rd
    have rd2252 := endRuntimeBlocks.endRuntime_block_2236_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSnipSuckCallRest world.2 I outDog outVat outSales sel)
      (by simp [endSnipSuckCallRest]) (by native_decide) (by jump_dest) rd2236
    refine ⟨.ok (endSnipAfterSuckFrame I outDog outVat outSales) evm',
      Endpoint.reached (endSnipAfterSuckCursor world.2 I sel aw outDog outVat outSales out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSnipAfterSuckCursor, endSnipAfterSuckStack, endSnipSuckCallAw,
          endRuntimeBlocks.endRuntime_block_2236_taken_stack] using rd2252⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd2236 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2236⟩
          ((⟨0⟩ : UInt256) :: endSnipSuckCallRest world.2 I outDog outVat outSales sel)
          (endSnipSuckCallMem world.2 I outDog outVat outSales)
          (endSnipSuckCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipSuckCallCursor,
        endSnipSuckCallStack, endSnipSuckCallRest, endSnipSuckCallAw] using rd
    have rd2243 := endRuntimeBlocks.endRuntime_block_2236_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSnipSuckCallRest world.2 I outDog outVat outSales sel)
      (by simp [endSnipSuckCallRest]) (by native_decide) rd2236
    exact endRuntimeBlocks.endRuntime_block_2243
      (R := endRuntimeBlocks.endRuntime_block_2236_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSnipSuckCallRest world.2 I outDog outVat outSales sel))
      (by simp [endRuntimeBlocks.endRuntime_block_2236_fallthrough_stack,
        endSnipSuckCallRest])
      rd2243

abbrev endSnipAfterSuckRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outDog : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preσ outVat outSales awSuck,
      frame = endSnipAfterSuckFrame I outDog outVat outSales ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outSales.size < UInt256.size ∧
      192 ≤ outSales.size ∧
      cur.stack = endSnipAfterSuckStack preσ I outDog outVat outSales sel ∧
      cur.mem = endSnipSuckCallMem preσ I outDog outVat outSales ∧
      cur.aw = endSnipSuckCallAw awSuck

set_option maxHeartbeats 12000000 in
theorem endSnipAfterSalesToSuckRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outDog : ByteArray}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨2112⟩
      (endSnipAfterSalesRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
      ([ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
      (sequenceExit ⟨2252⟩
        (endSnipAfterSuckRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
        (runtimeExit (.abi []))) := by
  intro cur0 k C frame evm hpc rd hP
  rcases hP with
    ⟨outVat, awSales, hframe, hrel, houtVat, h160, houtSales, h192,
      hstack, hmem, haw⟩
  cases hframe
  have rd2112 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2112⟩
        [UInt256.ofNat cur0.rdata.size,
          memLoad (UInt256.ofNat 64) (endSnipSalesReturnMem I outDog outVat cur0.rdata),
          ⟨0⟩, ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outVat,
          endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endSnipSalesReturnMem I outDog outVat cur0.rdata) (endSnipAfterSalesAw awSales)
        cur0.rdata cur0.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsourceLets :
      ExecBlock config (endSnipAfterSalesFrame I outDog outVat cur0.rdata) evm
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ]
        (.ok (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm) :=
    ExecBlock.consNormal (endLetSnipTab evm I outDog outVat cur0.rdata)
      (ExecBlock.consNormal (endLetSnipLot evm I outDog outVat cur0.rdata)
        (ExecBlock.consNormal (endLetSnipUsr evm I outDog outVat cur0.rdata)
          ExecBlock.nil))
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
        ExecBlock config (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_snipAfterUsr_false evm I outDog outVat
              cur0.rdata hsrcNoCode)))
    have hsourceFull :
        ExecBlock config (endSnipAfterSalesFrame I outDog outVat cur0.rdata) evm
          ([ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
              .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
              .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
            checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
              [vowAddr, vowAddr, .var "tab"] "_suck")
          .reverted :=
      Reasoning.Theory.execBlock_append hsourceLets hsourceChecked
    have hrev := endX_snip_vat_no_code_after_sales
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := awSales) (outDog := outDog)
      (outVat := outVat) (outSales := cur0.rdata) (k := k) (C := C)
      (world := cur0.world)
      houtDog h128 houtVat h160 houtSales h192 hvatNoCode rd2112
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
        ExecBlock config (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_snipAfterUsr_true evm I outDog outVat cur0.rdata
            hsrcCode))
        ExecBlock.nil
    obtain ⟨aw2234, k2234, C2234, rd2234⟩ :=
      endX_snip_after_sales_to_suck_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awSales) (outDog := outDog)
        (outVat := outVat) (outSales := cur0.rdata) (k := k) (C := C)
        (world := cur0.world)
        houtDog h128 houtVat h160 houtSales h192 hvatNoCode rd2112
    have htailExact :=
      (endSnipSuckExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw2234) (rdata := cur0.rdata)
        (outDog := outDog) (outVat := outVat) (outSales := cur0.rdata)
        (k := k2234) (C := C2234) (evm := evm) (world := cur0.world)
        hperm houtDog h128 houtVat h160 houtSales h192)
        (by simpa [endSnipSuckCallCursor] using rd2234) hrel
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm
          [ .externalCall (.storage vatRef) "suck" (.intLit 0)
              [vowAddr, vowAddr, .var "tab"] "_suck" ]
          (sequenceExit ⟨2252⟩
            (endSnipAfterSuckRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      rcases htailExact with ⟨result, endpoint, hb, hr, hQ⟩
      refine ⟨result, endpoint, hb, hr, ?_⟩
      cases result with
      | ok frameOut evmOut =>
          cases endpoint with
          | reached curOut =>
              simp only [sequenceExit, fallthrough] at hQ ⊢
              rcases hQ with ⟨hpcQ, hframeQ, hrelQ, hstackQ, hmemQ, hawQ⟩
              exact ⟨hpcQ, cur0.world.2, outVat, cur0.rdata, aw2234,
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
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSnipAfterUsrFrame I outDog outVat cur0.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck")
          (sequenceExit ⟨2252⟩
            (endSnipAfterSuckRel (initState cA gh bl σ σ₀ g A I) I sel outDog)
            (runtimeExit (.abi []))) := by
      simpa [checkedExternalCallStmts] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa using BlockProgress.prepend hsourceLets hcheckedProgress

theorem endSnipYankCallMem_generated (σ : AccountMap) (I : ExecutionEnv)
    (outDog outVat outSales : ByteArray)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    endRuntimeBlocks.endRuntime_block_2252_taken_memory
        (mem := endSnipSuckCallMem σ I outDog outVat outSales)
        (x10 := endArg1Word I) =
      endSnipYankCallMem σ I outDog outVat outSales := by
  unfold endRuntimeBlocks.endRuntime_block_2252_taken_memory
  unfold endSnipYankCallMem endSnipYankMemSel
  rw [endSnipSuckCallMem_mload64 σ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show (UInt256.ofNat 4 + (⟨128⟩ : UInt256)).toNat = 132 from by native_decide]

theorem endX_snip_clip_no_code_after_suck {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat outSales out k C}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hclipNoCode : extCodeSizeWord world.2 (endSnipClipTarget outDog) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2252⟩
      (endSnipAfterSuckStack preσ I outDog outVat outSales sel)
      (endSnipSuckCallMem preσ I outDog outVat outSales) aw out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hclipTarget :
      UInt256.land addrMask (endSnipDogIlksClipWord outDog) =
        endSnipClipTarget outDog := by
    rw [hmask]
    rw [u256_land_comm solcAddrMask (endSnipDogIlksClipWord outDog)]
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land addrMask (endSnipDogIlksClipWord outDog)))) =
        UInt256.ofNat 0 := by
    rw [hclipTarget, hclipNoCode]
    native_decide
  obtain ⟨aw2322, k2322, C2322, rd2322⟩ :=
    endRuntimeBlocks.endRuntime_block_2252_fallthrough_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endSnipSuckSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endSnipSalesUsrWord outSales)
      (x5 := endSnipSalesLotWord outSales)
      (x6 := endSnipSalesTabWord outSales)
      (x7 := endFlowVatIlksRateWord outVat)
      (x8 := endSnipDogIlksClipWord outDog)
      (x9 := endSnipDogIlksClipWord outDog)
      (x10 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond
      (by simpa [endSnipAfterSuckStack, endSnipSuckCallRest] using rd)
  exact endRuntimeBlocks.endRuntime_block_2322
    (R := endRuntimeBlocks.endRuntime_block_2252_fallthrough_stack
      (mem := endSnipSuckCallMem preσ I outDog outVat outSales) (σ := world.2)
      (x4 := endSnipSalesUsrWord outSales)
      (x5 := endSnipSalesLotWord outSales)
      (x6 := endSnipSalesTabWord outSales)
      (x7 := endFlowVatIlksRateWord outVat)
      (x8 := endSnipDogIlksClipWord outDog)
      (x9 := endSnipDogIlksClipWord outDog)
      (x10 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_2252_fallthrough_stack])
    rd2322

theorem endX_snip_after_suck_to_yank_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outDog outVat outSales out k C}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size)
    (hclipCode : extCodeSizeWord world.2 (endSnipClipTarget outDog) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2252⟩
      (endSnipAfterSuckStack preσ I outDog outVat outSales sel)
      (endSnipSuckCallMem preσ I outDog outVat outSales) aw out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2328⟩
      (endSnipYankCallStack preσ I outDog outVat outSales sel)
      (endSnipYankCallMem preσ I outDog outVat outSales) aw' out world k' C' := by
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  have hmask : addrMask = solcAddrMask := by
    native_decide
  have hclipTarget :
      UInt256.land addrMask (endSnipDogIlksClipWord outDog) =
        endSnipClipTarget outDog := by
    rw [hmask]
    rw [u256_land_comm solcAddrMask (endSnipDogIlksClipWord outDog)]
  have hsuck64 := endSnipSuckCallMem_mload64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hmemGen := endSnipYankCallMem_generated preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hyank64 := endSnipYankCallMem_mload64 preσ I outDog outVat outSales
    houtDog h128 houtVat h160 houtSales h192
  have hlen :
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
              (UInt256.land addrMask (endSnipDogIlksClipWord outDog)))) ≠
        UInt256.ofNat 0 := by
    rw [hclipTarget]
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hclipCode]
    native_decide
  obtain ⟨aw2326, k2326, C2326, rd2326⟩ :=
    endRuntimeBlocks.endRuntime_block_2252_taken_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endSnipSuckSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endSnipSalesUsrWord outSales)
      (x5 := endSnipSalesLotWord outSales)
      (x6 := endSnipSalesTabWord outSales)
      (x7 := endFlowVatIlksRateWord outVat)
      (x8 := endSnipDogIlksClipWord outDog)
      (x9 := endSnipDogIlksClipWord outDog)
      (x10 := endArg1Word I)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest)
      (by simpa [endSnipAfterSuckStack, endSnipSuckCallRest] using rd)
  have hstack2252 :
      endRuntimeBlocks.endRuntime_block_2252_taken_stack
          (mem := endSnipSuckCallMem preσ I outDog outVat outSales) (σ := world.2)
          (x4 := endSnipSalesUsrWord outSales)
          (x5 := endSnipSalesLotWord outSales)
          (x6 := endSnipSalesTabWord outSales)
          (x7 := endFlowVatIlksRateWord outVat)
          (x8 := endSnipDogIlksClipWord outDog)
          (x9 := endSnipDogIlksClipWord outDog)
          (x10 := endArg1Word I)
          (R := [endArg0Word I, ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)) ::
          endSnipYankCallStack preσ I outDog outVat outSales sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_2252_taken_stack]
    change
      [UInt256.isZero (extCodeSizeWord world.2
          (UInt256.land addrMask (endSnipDogIlksClipWord outDog))),
        UInt256.land addrMask (endSnipDogIlksClipWord outDog), (⟨0⟩ : UInt256),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_2252_taken_memory
            (mem := endSnipSuckCallMem preσ I outDog outVat outSales)
            (x10 := endArg1Word I)),
        UInt256.sub
          (UInt256.ofNat 32 +
            (UInt256.ofNat 4 +
              memLoad (UInt256.ofNat 64)
                (endSnipSuckCallMem preσ I outDog outVat outSales)))
          (memLoad (UInt256.ofNat 64)
            (endRuntimeBlocks.endRuntime_block_2252_taken_memory
              (mem := endSnipSuckCallMem preσ I outDog outVat outSales)
              (x10 := endArg1Word I))),
        memLoad (UInt256.ofNat 64)
          (endRuntimeBlocks.endRuntime_block_2252_taken_memory
            (mem := endSnipSuckCallMem preσ I outDog outVat outSales)
            (x10 := endArg1Word I)),
        (⟨0⟩ : UInt256),
        UInt256.ofNat 32 +
          (UInt256.ofNat 4 +
            memLoad (UInt256.ofNat 64)
              (endSnipSuckCallMem preσ I outDog outVat outSales)),
        UInt256.ofNat 652224497,
        UInt256.land addrMask (endSnipDogIlksClipWord outDog),
        endSnipSalesUsrWord outSales, endSnipSalesLotWord outSales,
        endSnipSalesTabWord outSales, endFlowVatIlksRateWord outVat,
        endSnipDogIlksClipWord outDog, endSnipDogIlksClipWord outDog,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel] =
      UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)) ::
        endSnipYankCallStack preσ I outDog outVat outSales sel
    rw [hclipTarget, hmemGen, hsuck64, hyank64, hlen, hend]
    rfl
  have rd2326' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2326⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)) ::
          endSnipYankCallStack preσ I outDog outVat outSales sel)
        (endSnipYankCallMem preσ I outDog outVat outSales) aw2326 out world
        k2326 C2326 := by
    simpa [hstack2252, hmemGen] using rd2326
  have rd2328 := endRuntimeBlocks.endRuntime_block_2326
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endSnipClipTarget outDog)))
    (R := endSnipYankCallStack preσ I outDog outVat outSales sel)
    (by simp [endSnipYankCallStack, endSnipYankCallRest]) rd2326'
  exact ⟨aw2326, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_2326_stack] using rd2328⟩

set_option maxHeartbeats 12000000 in
theorem endSnipYankExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata outDog outVat outSales k C evm}
    {preσ : AccountMap}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtDog : outDog.size < UInt256.size) (h128 : 128 ≤ outDog.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtSales : outSales.size < UInt256.size) (h192 : 192 ≤ outSales.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSnipYankCallCursor world preσ I sel aw outDog outVat outSales rdata)
      k C (endSnipAfterSuckFrame I outDog outVat outSales) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ]
      (sequenceExit ⟨2346⟩
        (fun cur frame e =>
          frame = endSnipAfterYankFrame I outDog outVat outSales ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack = endSnipAfterYankStack preσ I outDog outVat outSales sel ∧
          cur.mem = endSnipYankCallMem preσ I outDog outVat outSales ∧
          cur.aw = endSnipYankCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨2328⟩ = some (.GAS, .none); decide)
    (by simp [endSnipYankCallCursor, endSnipYankCallStack, endSnipYankCallRest])
    ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endSnipClipTarget outDog).toNat)
    (argVals := [endUIntValue (endArg1Word I)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨2329⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSnipYankCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro _
    rw [endEvalClipAddress_snipAfterSuck_masked evm I outDog outVat outSales]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSnipYankArgsAfterSuck evm I outDog outVat outSales
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endSnipClipTarget outDog).toNat % EVM.addressModulus % AccountAddress.size =
      (endSnipClipTarget outDog).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_yank_snip I]
    change some (endSnipYankEncodedCall I) =
      some ((endSnipYankCallMem preσ I outDog outVat outSales).readWithPadding 128 36)
    rw [endSnipYankCallMem_readCallData preσ I outDog outVat outSales
      houtDog h128 houtVat h160 houtSales h192]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_yank out]
    intro rd hrel
    have rd2330 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2330⟩
          ((⟨1⟩ : UInt256) :: endSnipYankCallRest preσ I outDog outVat outSales sel)
          (endSnipYankCallMem preσ I outDog outVat outSales)
          (endSnipYankCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipYankCallCursor,
        endSnipYankCallStack, endSnipYankCallRest, endSnipYankCallAw] using rd
    have rd2346 := endRuntimeBlocks.endRuntime_block_2330_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSnipYankCallRest preσ I outDog outVat outSales sel)
      (by simp [endSnipYankCallRest]) (by native_decide) (by jump_dest) rd2330
    refine ⟨.ok (endSnipAfterYankFrame I outDog outVat outSales) evm',
      Endpoint.reached (endSnipAfterYankCursor preσ I sel aw outDog outVat outSales out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by
        simpa [endSnipAfterYankCursor, endSnipAfterYankStack, endSnipYankCallAw,
          endRuntimeBlocks.endRuntime_block_2330_taken_stack] using rd2346⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd2330 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2330⟩
          ((⟨0⟩ : UInt256) :: endSnipYankCallRest preσ I outDog outVat outSales sel)
          (endSnipYankCallMem preσ I outDog outVat outSales)
          (endSnipYankCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSnipYankCallCursor,
        endSnipYankCallStack, endSnipYankCallRest, endSnipYankCallAw] using rd
    have rd2337 := endRuntimeBlocks.endRuntime_block_2330_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSnipYankCallRest preσ I outDog outVat outSales sel)
      (by simp [endSnipYankCallRest]) (by native_decide) rd2330
    exact endRuntimeBlocks.endRuntime_block_2337
      (R := endRuntimeBlocks.endRuntime_block_2330_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSnipYankCallRest preσ I outDog outVat outSales sel))
      (by simp [endRuntimeBlocks.endRuntime_block_2330_fallthrough_stack,
        endSnipYankCallRest])
      rd2337

abbrev endSnipAfterYankRel (s0 : State) (I : ExecutionEnv) (sel : UInt256)
    (outDog : ByteArray) : StateRel :=
  fun cur frame e =>
    ∃ preσ outVat outSales awYank,
      frame = endSnipAfterYankFrame I outDog outVat outSales ∧
      CallStateRel s0 I cur.world e ∧
      outVat.size < UInt256.size ∧
      160 ≤ outVat.size ∧
      outSales.size < UInt256.size ∧
      192 ≤ outSales.size ∧
      cur.stack = endSnipAfterYankStack preσ I outDog outVat outSales sel ∧
      cur.mem = endSnipYankCallMem preσ I outDog outVat outSales ∧
      cur.aw = endSnipYankCallAw awYank

end Benchmarks.Dss.End
