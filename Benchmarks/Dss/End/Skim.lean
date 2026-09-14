import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.FileAddress
import Benchmarks.Dss.End.RuntimeBlocks_010
import Benchmarks.Dss.End.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `skim(bytes32,address)` -/

abbrev endSkimStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)

theorem endDecode_legacyBytes32_address_skim_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "urn"] [bytes32, addr]
        I.calldata =
      some (endSkimStore I) := by
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
      ¬ ([bytes32, addr].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, addr, isDynamicABIType]
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [show decodeABIValues? [bytes32, addr] (I.calldata.toList.drop 4) 0 0 64 64
        DecodeMode.legacySolc05 =
        some ([endArg0Bytes32Value I, endArg1AddressValue I], 64) by
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
    rw [show isDynamicABIType addr = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? addr = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval1 :
        decodeABIValue? addr (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
          some (endArg1AddressValue I, 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := addr) (bytes := I.calldata.toList.drop 4) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress
          (I.calldata.toList.drop 4) 32 = some (endArg1AddressValue I, 64)
      rw [decodeScalarWord_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
        (start := 32) htake36]
      rw [hword36]
    rw [hval1]
    simp]
  simp [decodeCalldata.insertValues, endSkimStore]

theorem endDecode_legacyBytes32_address_skim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "urn"] [bytes32, addr]
        I.calldata = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, addr].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, addr, isDynamicABIType]
  have hshortArgs : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

abbrev endSkimTagSlot (I : ExecutionEnv) : UInt256 :=
  tagSlot (endArg0Bytes32Key I)

abbrev endSkimTagWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 12) (endArg0Word I)

abbrev endSkimTagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I)

abbrev endSkimTagWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endSkimTagWorldSlot I)

abbrev endSkimVatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_6705_taken_memory
    (mem := solcFreePtrMem) (x1 := endArg0Word I)

abbrev endSkimVatIlksCallMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_6795_taken_memory
    (mem := endSkimVatIlksBaseMem I) (x1 := endArg0Word I)

abbrev endSkimVatIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I, ⟨0⟩,
    endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkimVatIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨160⟩] ++
    endSkimVatIlksCallRest σ I sel

abbrev endSkimVatIlksCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨6874⟩, stack := endSkimVatIlksCallStack σ I sel,
    mem := endSkimVatIlksCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endSkimVatIlksCallAw (aw : UInt256) : UInt256 :=
  endFlowVatIlksCallAw aw

abbrev endSkimVatIlksReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endSkimVatIlksCallMem I) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endSkimAfterVatIlksAw (aw : UInt256) : UInt256 :=
  M (endSkimVatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSkimAfterVatIlksFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimStore I).insert "vatIlk" (collapseReturns (endFlowVatIlksValues out)) }

abbrev endSkimAfterRateFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterVatIlksFrame I out).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord out)) }

abbrev endSkimAfterVatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6914⟩,
    stack := [UInt256.ofNat out.size,
      memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I out),
      ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel],
    mem := endSkimVatIlksReturnMem I out,
    aw := endSkimAfterVatIlksAw aw,
    rdata := out,
    world := world }

theorem endSkimVatIlksBaseMem_eq_hashMem (I : ExecutionEnv) :
    endSkimVatIlksBaseMem I =
      twoWordHashMem (endArg0Word I) (UInt256.ofNat 12) solcFreePtrMem := by
  unfold endSkimVatIlksBaseMem twoWordHashMem wordAt0Mem wordAt32Mem
  dsimp [endRuntimeBlocks.endRuntime_block_6705_taken_memory]
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem endSkimVatIlksBaseMem_size (I : ExecutionEnv) :
    (endSkimVatIlksBaseMem I).size = 96 := by
  rw [endSkimVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_size_96 (endArg0Word I) (UInt256.ofNat 12) solcFreePtrMem_size

theorem endSkimVatIlksBaseMem_read64 (I : ExecutionEnv) :
    (endSkimVatIlksBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_read64 (endArg0Word I) (UInt256.ofNat 12)
    solcFreePtrMem_size solcFreePtrMem_read64

theorem endSkimVatIlksBaseMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endSkimVatIlksBaseMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkimVatIlksBaseMem I)
    (by rw [endSkimVatIlksBaseMem_size I]; omega)
    (endSkimVatIlksBaseMem_read64 I)

theorem endSkimVatIlksCallMem_eq_full (I : ExecutionEnv) :
    endSkimVatIlksCallMem I =
      (endArg0Word I).toByteArray.write 0
        (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
          (endSkimVatIlksBaseMem I) 128 32)
        132 32 := by
  unfold endSkimVatIlksCallMem endFlowVatIlksSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_6795_taken_memory]
  rw [endSkimVatIlksBaseMem_mload64 I]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]

theorem endSkimVatIlksMemSel_size_ge160 (I : ExecutionEnv) :
    160 ≤ (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkimVatIlksBaseMem I) 128

theorem endSkimVatIlksCallMem_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endSkimVatIlksCallMem I).size := by
  rw [endSkimVatIlksCallMem_eq_full I]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32)
    132

theorem endSkimVatIlksCallMem_read64 (I : ExecutionEnv) :
    (endSkimVatIlksCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimVatIlksCallMem_eq_full I]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32)
    132 64
    (by have := endSkimVatIlksMemSel_size_ge160 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkimVatIlksBaseMem I) 128 64
    (by rw [endSkimVatIlksBaseMem_size I]) (by omega)]
  exact endSkimVatIlksBaseMem_read64 I

theorem endSkimVatIlksCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endSkimVatIlksCallMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkimVatIlksCallMem I)
    (by have := endSkimVatIlksCallMem_size_ge164 I; omega)
    (endSkimVatIlksCallMem_read64 I)

theorem endSkimVatIlksCallMem_readSelector (I : ExecutionEnv) :
    (endSkimVatIlksCallMem I).readWithPadding 128 4 = ilksSelector := by
  rw [endSkimVatIlksCallMem_eq_full I]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endSkimVatIlksMemSel_size_ge160 I; omega) (by omega)
    (by have := endSkimVatIlksMemSel_size_ge160 I; omega) (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endSkimVatIlksBaseMem I) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFlowVatIlksSelectorEncodedWord_prefix]

theorem endSkimVatIlksCallMem_readIlk (I : ExecutionEnv) :
    (endSkimVatIlksCallMem I).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSkimVatIlksCallMem_eq_full I]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I)
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32)
    132

theorem endSkimVatIlksCallMem_readCallData (I : ExecutionEnv) :
    (endSkimVatIlksCallMem I).readWithPadding 128 36 =
      endFlowVatIlksEncodedCall I := by
  have hsize := endSkimVatIlksCallMem_size_ge164 I
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSkimVatIlksCallMem I) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endSkimVatIlksCallMem_readSelector I, endSkimVatIlksCallMem_readIlk I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFlowVatIlksEncodedCall, endFlowVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

theorem endSkimVatIlksMemSel_size (I : ExecutionEnv) :
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32).size = 160 := by
  exact toByteArray_write32_size_of_ge (endSkimVatIlksBaseMem I)
    endFlowVatIlksSelectorEncodedWord 128 96 160
    (endSkimVatIlksBaseMem_size I) (by omega) (by native_decide) rfl

theorem endSkimVatIlksCallMem_size (I : ExecutionEnv) :
    (endSkimVatIlksCallMem I).size = 164 := by
  rw [endSkimVatIlksCallMem_eq_full I]
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endSkimVatIlksBaseMem I) 128 32)
    (endArg0Word I) 132 160 164
    (endSkimVatIlksMemSel_size I)
    (by rw [endSkimVatIlksMemSel_size I]; omega)
    (by omega)

theorem endSkimVatIlksReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endSkimVatIlksReturnMem I out).size = 288 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkimVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSkimVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endSkimVatIlksCallMem_size I]; omega)
    (by rw [endSkimVatIlksCallMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSkimVatIlksCallMem_size I]
  omega

theorem endSkimVatIlksReturnMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endSkimVatIlksReturnMem I out).readWithPadding 64 32 =
      (endSkimVatIlksCallMem I).readWithPadding 64 32 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkimVatIlksReturnMem
  rw [hcopy]
  exact write_read_below_gen_extend out (endSkimVatIlksCallMem I) 128 160 64
    (by decide) h160
    (by rw [endSkimVatIlksCallMem_size I]; omega)
    (by omega)

theorem endSkimVatIlksReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I out) = ⟨128⟩ := by
  have hbase := endSkimVatIlksCallMem_mload64 I
  unfold memLoad at hbase ⊢
  rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide] at hbase ⊢
  rw [if_neg (by
    rw [endSkimVatIlksReturnMem_size I out hout h160]
    omega)]
  rw [endSkimVatIlksReturnMem_read64 I out hout h160]
  rw [if_neg (by
    rw [endSkimVatIlksCallMem_size I]
    omega)] at hbase
  exact hbase

theorem endSkimVatIlksReturnMem_read160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endSkimVatIlksReturnMem I out).readWithPadding 160 32 =
      out.extract 32 64 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endSkimVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endSkimVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endSkimVatIlksCallMem_size I]; omega)
    (by rw [endSkimVatIlksCallMem_size I]; omega)]
  have hpre : ((endSkimVatIlksCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkimVatIlksCallMem_size I]
    omega
  have hcopySize : (out.extract 0 160).size = 160 := by
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

theorem endSkimVatIlksReturnMem_mload160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 160) (endSkimVatIlksReturnMem I out) =
      endFlowVatIlksRateWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSkimVatIlksReturnMem_size I out hout h160]
    omega)]
  rw [endSkimVatIlksReturnMem_read160 I out hout h160]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64)) =
    ABI.bytesToWord ((out.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

abbrev endSkimUrnsSelectorWord : UInt256 := endFreeUrnsSelectorWord

abbrev endSkimUrnsSelectorEncodedWord : UInt256 := endFreeUrnsSelectorEncodedWord

def endSkimUrnsPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg0Word I) ++
    EVM.Word.toBytesBE (endArg1AddressWord I)

def endSkimUrnsEncodedCall (I : ExecutionEnv) : ByteArray :=
  urnsSelector ++ ⟨(endSkimUrnsPayloadBytes I).toArray⟩

theorem endEncodeAddress_arg1_skim (I : ExecutionEnv) :
    encodeABIValue? addr (endArg1AddressValue I) =
      some (EVM.Word.toBytesBE (endArg1AddressWord I)) := by
  rw [endArg1AddressValue_masked I]
  have hmod :
      (endArg1AddressWord I).toNat % AccountAddress.size =
        (endArg1AddressWord I).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size]
      using endArg1AddressWord_canonical I
  have hword : EVM.word (endArg1AddressWord I).toNat = endArg1AddressWord I :=
    u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, hmod, hword]

theorem endEncodeABIValues_urns_skim (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    encodeABIValues? [bytes32, addr] [endArg0Bytes32Value I, endArg1AddressValue I] =
      some (endSkimUrnsPayloadBytes I) := by
  have hhead : abiTupleHeadSize? [bytes32, addr] = some 64 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I (by omega : 36 ≤ I.calldata.size), hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_arg1_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endSkimUrnsPayloadBytes]

theorem endEncodeCallWithSelector_urns_skim (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    ABI.encodeCallWithSelector? urnsSelector [bytes32, addr]
      [endArg0Bytes32Value I, endArg1AddressValue I] =
      some (endSkimUrnsEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_urns_skim I hsz68]
  simp [endSkimUrnsEncodedCall, endSkimUrnsPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_urns_skim (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    config.externalABI.encode? "urns" [endArg0Bytes32Value I, endArg1AddressValue I] =
      some (endSkimUrnsEncodedCall I) := by
  rw [endExternalEncode_urns_branch]
  exact endEncodeCallWithSelector_urns_skim I hsz68

abbrev endSkimUrnsMemSel (I : ExecutionEnv) (outIlks : ByteArray) : ByteArray :=
  endSkimUrnsSelectorEncodedWord.toByteArray.write 0
    (endSkimVatIlksReturnMem I outIlks) 128 32

abbrev endSkimUrnsMemIlk (I : ExecutionEnv) (outIlks : ByteArray) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endSkimUrnsMemSel I outIlks) 132 32

abbrev endSkimUrnsMemFull (I : ExecutionEnv) (outIlks : ByteArray) : ByteArray :=
  (endArg1AddressWord I).toByteArray.write 0 (endSkimUrnsMemIlk I outIlks) 164 32

abbrev endSkimUrnsCallMem (I : ExecutionEnv) (outIlks : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_6914_memory
    (mem := endSkimVatIlksReturnMem I outIlks)
    (x3 := endArg1AddressWord I) (x4 := endArg0Word I)

theorem endSkimUrnsCallMem_eq_full (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    endSkimUrnsCallMem I outIlks = endSkimUrnsMemFull I outIlks := by
  have hload := endSkimVatIlksReturnMem_mload64 I outIlks hout h160
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hclean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (endArg1AddressWord I) =
        endArg1AddressWord I := by
    rw [hmaskGenerated]
    exact solcAddrMask_clean_left (endArg1AddressWord_canonical I)
  unfold endSkimUrnsCallMem endSkimUrnsMemFull endSkimUrnsMemIlk endSkimUrnsMemSel
    endSkimUrnsSelectorEncodedWord endFreeUrnsSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_6914_memory]
  rw [hload, hclean]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 36)).toNat = 164 from by native_decide]

theorem endSkimUrnsMemSel_size_ge160 (I : ExecutionEnv) (outIlks : ByteArray) :
    160 ≤ (endSkimUrnsMemSel I outIlks).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded endSkimUrnsSelectorEncodedWord
    (endSkimVatIlksReturnMem I outIlks) 128

theorem endSkimUrnsMemIlk_size_ge164 (I : ExecutionEnv) (outIlks : ByteArray) :
    164 ≤ (endSkimUrnsMemIlk I outIlks).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endSkimUrnsMemSel I outIlks) 132

theorem endSkimUrnsCallMem_size_ge196 (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    196 ≤ (endSkimUrnsCallMem I outIlks).size := by
  rw [endSkimUrnsCallMem_eq_full I outIlks hout h160]
  exact toByteArray_write_size_ge_off_add32_unbounded (endArg1AddressWord I)
    (endSkimUrnsMemIlk I outIlks) 164

theorem endSkimUrnsCallMem_read64 (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    (endSkimUrnsCallMem I outIlks).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimUrnsCallMem_eq_full I outIlks hout h160]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1AddressWord I) (endSkimUrnsMemIlk I outIlks) 164 64
    (by have := endSkimUrnsMemIlk_size_ge164 I outIlks; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I) (endSkimUrnsMemSel I outIlks) 132 64
    (by have := endSkimUrnsMemSel_size_ge160 I outIlks; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endSkimUrnsSelectorEncodedWord (endSkimVatIlksReturnMem I outIlks) 128 64
    (by rw [endSkimVatIlksReturnMem_size I outIlks hout h160]; omega) (by omega)]
  rw [endSkimVatIlksReturnMem_read64 I outIlks hout h160, endSkimVatIlksCallMem_read64 I]

theorem endSkimUrnsCallMem_mload64 (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endSkimUrnsCallMem I outIlks)
    (by have := endSkimUrnsCallMem_size_ge196 I outIlks hout h160; omega)
    (endSkimUrnsCallMem_read64 I outIlks hout h160)

theorem endSkimUrnsCallMem_readSelector (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    (endSkimUrnsCallMem I outIlks).readWithPadding 128 4 = urnsSelector := by
  rw [endSkimUrnsCallMem_eq_full I outIlks hout h160]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endSkimUrnsMemIlk_size_ge164 I outIlks) (by omega)
    (by have := endSkimUrnsMemIlk_size_ge164 I outIlks; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endSkimUrnsMemSel_size_ge160 I outIlks; omega) (by omega)
    (by have := endSkimUrnsMemSel_size_ge160 I outIlks; omega) (by decide) (by decide)]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkimUrnsSelectorEncodedWord (endSkimVatIlksReturnMem I outIlks) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFreeUrnsSelectorEncodedWord_prefix]

theorem endSkimUrnsCallMem_readIlk (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    (endSkimUrnsCallMem I outIlks).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSkimUrnsCallMem_eq_full I outIlks hout h160]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg1AddressWord I) (endSkimUrnsMemIlk I outIlks) 164 132
    (by have := endSkimUrnsMemIlk_size_ge164 I outIlks; omega) (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I) (endSkimUrnsMemSel I outIlks) 132

theorem endSkimUrnsCallMem_readUrn (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    (endSkimUrnsCallMem I outIlks).readWithPadding 164 32 =
      (endArg1AddressWord I).toByteArray := by
  rw [endSkimUrnsCallMem_eq_full I outIlks hout h160]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg1AddressWord I) (endSkimUrnsMemIlk I outIlks) 164

theorem endSkimUrnsCallMem_readCallData (I : ExecutionEnv) (outIlks : ByteArray)
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    (endSkimUrnsCallMem I outIlks).readWithPadding 128 68 =
      endSkimUrnsEncodedCall I := by
  have hsize := endSkimUrnsCallMem_size_ge196 I outIlks hout h160
  rw [show 68 = 4 + 64 from rfl]
  rw [byteArray_readWithPadding_split (endSkimUrnsCallMem I outIlks) 128 4 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endSkimUrnsCallMem I outIlks) 132 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [endSkimUrnsCallMem_readSelector I outIlks hout h160,
    endSkimUrnsCallMem_readIlk I outIlks hout h160,
    endSkimUrnsCallMem_readUrn I outIlks hout h160]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSkimUrnsEncodedCall, endSkimUrnsPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endSkimUrnsRawVatTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))

abbrev endSkimUrnsCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256)
    (outIlks : ByteArray) : List UInt256 :=
  [memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I outIlks) + UInt256.ofNat 68,
    endSkimUrnsSelectorWord, endSkimUrnsRawVatTarget σ I, ⟨0⟩, ⟨0⟩,
    memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 64)
      (endSkimVatIlksReturnMem I outIlks)) (endSkimVatIlksReturnMem I outIlks),
    endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]

abbrev endSkimUrnsCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256)
    (outIlks : ByteArray) : List UInt256 :=
  [endSkimUrnsRawVatTarget σ I, ⟨0⟩,
    memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks),
    UInt256.sub (memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I outIlks))
      (memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks)) + UInt256.ofNat 68,
    memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks),
    ⟨64⟩] ++
    endSkimUrnsCallRest σ I sel outIlks

abbrev endSkimUrnsCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (outIlks rdata : ByteArray) : Cursor :=
  { pc := ⟨7010⟩, stack := endSkimUrnsCallStack world.2 I sel outIlks,
    mem := endSkimUrnsCallMem I outIlks, aw := aw, rdata := rdata, world := world }

abbrev endSkimUrnsCallAw (aw : UInt256) : UInt256 :=
  endFreeUrnsCallAw aw

abbrev endSkimUrnsReturnMem (I : ExecutionEnv) (outIlks outUrns : ByteArray) : ByteArray :=
  outUrns.write 0 (endSkimUrnsCallMem I outIlks) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat outUrns.size)).toNat

abbrev endSkimAfterUrnsAw (aw : UInt256) : UInt256 :=
  M (endSkimUrnsCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endSkimAfterUrnsFrame (I : ExecutionEnv) (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
      (collapseReturns (endFreeUrnsValues outUrns)) }

abbrev endSkimAfterUrnsCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outIlks outUrns : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨7050⟩,
    stack := [UInt256.ofNat outUrns.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      endFlowVatIlksRateWord outIlks,
      endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel],
    mem := endSkimUrnsReturnMem I outIlks outUrns,
    aw := endSkimAfterUrnsAw aw,
    rdata := outUrns,
    world := world }

theorem endSkimUrnsReturnMem_size (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimUrnsReturnMem I outIlks outUrns).size =
      (endSkimUrnsCallMem I outIlks).size := by
  have hfacts := callOutputFacts (endSkimUrnsCallMem I outIlks) outUrns (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) houtUrns (by
      change 128 + 64 ≤ (endSkimUrnsCallMem I outIlks).size
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega)
  simpa [endSkimUrnsReturnMem] using hfacts.size

theorem endSkimUrnsReturnMem_mload64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endSkimUrnsReturnMem I outIlks outUrns) = ⟨128⟩ := by
  have hfacts := callOutputFacts (endSkimUrnsCallMem I outIlks) outUrns (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) houtUrns (by
      change 128 + 64 ≤ (endSkimUrnsCallMem I outIlks).size
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega)
  have hread :
      (endSkimUrnsReturnMem I outIlks outUrns).readWithPadding 64 32 =
        (endSkimUrnsCallMem I outIlks).readWithPadding 64 32 := by
    simpa [endSkimUrnsReturnMem] using hfacts.readBelow 64 (by native_decide)
  have hbase := endSkimUrnsCallMem_mload64 I outIlks houtIlks h160
  unfold memLoad at hbase ⊢
  rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide] at hbase ⊢
  rw [if_neg (by
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega)]
  rw [hread]
  rw [if_neg (by
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega)] at hbase
  exact hbase

theorem endSkimUrnsReturnMem_read128 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size) :
    (endSkimUrnsReturnMem I outIlks outUrns).readWithPadding 128 32 =
      outUrns.extract 0 32 := by
  have hfacts := callOutputFacts (endSkimUrnsCallMem I outIlks) outUrns
    (⟨128⟩ : UInt256) (⟨64⟩ : UInt256) houtUrns (by
      change 128 + 64 ≤ (endSkimUrnsCallMem I outIlks).size
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega)
  simpa [endSkimUrnsReturnMem] using hfacts.readWord (by decide) (by omega)

theorem endSkimUrnsReturnMem_read160 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160Ilks : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size) :
    (endSkimUrnsReturnMem I outIlks outUrns).readWithPadding 160 32 =
      outUrns.extract 32 64 := by
  have hcopy :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat outUrns.size)).toNat = 64 := by
    rw [callCopyLength_toNat outUrns (⟨64⟩ : UInt256) houtUrns]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
    exact Nat.min_eq_left h64
  unfold endSkimUrnsReturnMem
  rw [hcopy]
  rw [write_eq_gen outUrns (endSkimUrnsCallMem I outIlks) 128 64
    (by decide) (by omega) (by
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160Ilks
      omega)]
  have hpre : ((endSkimUrnsCallMem I outIlks).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160Ilks
    omega
  have hcopySize : (outUrns.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hpre, hcopySize])]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 64 = 64 by omega]

theorem endSkimUrnsReturnMem_mload128 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size) :
    memLoad (UInt256.ofNat 128) (endSkimUrnsReturnMem I outIlks outUrns) =
      endFreeUrnsInkWord outUrns := by
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega)]
  rw [endSkimUrnsReturnMem_read128 I outIlks outUrns houtIlks h160 houtUrns h64]
  change UInt256.ofNat (fromByteArrayBigEndian (outUrns.extract 0 32)) =
    ABI.bytesToWord (outUrns.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endSkimUrnsReturnMem_mload160 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160Ilks : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size) :
    memLoad (UInt256.ofNat 160) (endSkimUrnsReturnMem I outIlks outUrns) =
      endFreeUrnsArtWord outUrns := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160Ilks houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160Ilks
    omega)]
  rw [endSkimUrnsReturnMem_read160 I outIlks outUrns houtIlks h160Ilks houtUrns h64]
  change UInt256.ofNat (fromByteArrayBigEndian (outUrns.extract 32 64)) =
    ABI.bytesToWord ((outUrns.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

theorem endSkimTagWord_init_eq {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz68 : 68 ≤ I.calldata.size) :
    endSkimTagWord (initState cA gh bl σ σ₀ g A I) I =
      endSkimTagWorldWord σ I := by
  have hslot : endSkimTagSlot I = endSkimTagWorldSlot I := by
    unfold endSkimTagSlot endSkimTagWorldSlot
    exact endTagSlot_eq I (by omega)
  simp [endSkimTagWord, endSkimTagWorldWord, hslot, initState, Solm.EVM.storageLoad,
    State.lookupAccount, storageRead, Account.lookupStorage]

theorem endSkimStore_get_tag_none (I : ExecutionEnv) :
    (endSkimStore I).get? "tag" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "tag") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "urn") (a := "tag") (endArg1AddressValue I) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "tag")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endSkimStore_get_ilk (I : ExecutionEnv) :
    (endSkimStore I).get? "ilk" = some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "urn") (a := "ilk") (endArg1AddressValue I) (by decide)]
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endSkimStore_getElem_ilk (I : ExecutionEnv) :
    (endSkimStore I)["ilk"] = endArg0Bytes32Value I := by
  have hopt : (endSkimStore I)["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSkimStore_get_ilk I
  have hpos := getElem?_pos (endSkimStore I) "ilk" (by
    simp [endSkimStore, Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSkimStore_get_urn (I : ExecutionEnv) :
    (endSkimStore I).get? "urn" = some (endArg1AddressValue I) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "urn") = some (endArg1AddressValue I)
  exact store_get_self ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    "urn" (endArg1AddressValue I)

theorem endSkimStore_getElem_urn (I : ExecutionEnv) :
    (endSkimStore I)["urn"] = endArg1AddressValue I := by
  have hopt : (endSkimStore I)["urn"]? = some (endArg1AddressValue I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSkimStore_get_urn I
  have hpos := getElem?_pos (endSkimStore I) "urn" (by
    simp [endSkimStore, Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSkimStore_get_vat_none (I : ExecutionEnv) :
    (endSkimStore I).get? "vat" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "vat") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "urn") (a := "vat") (endArg1AddressValue I) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "vat")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endSkimStore_get_vow_none (I : ExecutionEnv) :
    (endSkimStore I).get? "vow" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "vow") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "urn") (a := "vow") (endArg1AddressValue I) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "vow")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalVatAddress_skim (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endSkimStore I } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endSkimStore_get_vat_none I) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_skim (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_skim evm I]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_skim_false (evm : EVM.State) (I : ExecutionEnv)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skim evm I, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_skim_true (evm : EVM.State) (I : ExecutionEnv)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skim evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalSkimVatIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endSkimStore I } evm
      [.var "ilk"] = .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endSkimStore_getElem_ilk I]

theorem endEvalSkimRateFromVatIlk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks : ByteArray) :
    evalExpr? config (endSkimAfterVatIlksFrame I outIlks) evm
      (.tupleGet (.var "vatIlk") 1) =
      .ok (endUIntValue (endFlowVatIlksRateWord outIlks)) := by
  simp [evalExpr?, endSkimAfterVatIlksFrame, collapseReturns, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind, endUIntValue]

theorem endSkimAfterRateFrame_get_ilk (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne ((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))) (k := "rate") (a := "ilk")
    (endUIntValue (endFlowVatIlksRateWord outIlks)) (by decide)]
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "ilk")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  exact endSkimStore_get_ilk I

theorem endSkimAfterRateFrame_get_urn (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change ((((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne ((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))) (k := "rate") (a := "urn")
    (endUIntValue (endFlowVatIlksRateWord outIlks)) (by decide)]
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "urn")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  exact endSkimStore_get_urn I

theorem endSkimAfterRateFrame_get_vat_none (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals.get? "vat" = none := by
  change ((((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "vat") = none
  rw [store_get_ne ((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))) (k := "rate") (a := "vat")
    (endUIntValue (endFlowVatIlksRateWord outIlks)) (by decide)]
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "vat")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  exact endSkimStore_get_vat_none I

theorem endSkimAfterRateFrame_getElem_ilk (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals["ilk"] = endArg0Bytes32Value I := by
  exact endFlowFrame_getElem_ilk (I := I)
    (endSkimAfterRateFrame_get_ilk I outIlks) (by
      simp [endSkimAfterRateFrame, endSkimAfterVatIlksFrame, endSkimStore,
        Std.HashMap.mem_insert])

theorem endSkimAfterRateFrame_getElem_urn (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals["urn"] = endArg1AddressValue I := by
  have hopt :
      (endSkimAfterRateFrame I outIlks).locals["urn"]? =
        some (endArg1AddressValue I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endSkimAfterRateFrame_get_urn I outIlks
  have hpos := getElem?_pos (endSkimAfterRateFrame I outIlks).locals "urn" (by
    simp [endSkimAfterRateFrame, endSkimAfterVatIlksFrame, endSkimStore,
      Std.HashMap.mem_insert])
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endEvalSkimUrnsArgs (evm : EVM.State) (I : ExecutionEnv) (outIlks : ByteArray) :
    evalExprs? config (endSkimAfterRateFrame I outIlks) evm
      [.var "ilk", .var "urn"] =
      .ok [endArg0Bytes32Value I, endArg1AddressValue I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endSkimAfterRateFrame_getElem_ilk I outIlks,
    endSkimAfterRateFrame_getElem_urn I outIlks]

theorem endEvalVatAddress_skimAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outIlks : ByteArray) :
    evalExpr? config (endSkimAfterRateFrame I outIlks) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endSkimAfterRateFrame I outIlks) evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endSkimAfterRateFrame_get_vat_none I outIlks) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_skimAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (outIlks : ByteArray) :
    evalExpr? config (endSkimAfterRateFrame I outIlks)
        evm (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_skimAfterRate evm I outIlks]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_skimAfterRate_false (evm : EVM.State)
    (I : ExecutionEnv) (outIlks : ByteArray)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkimAfterRateFrame I outIlks) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skimAfterRate evm I outIlks, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_skimAfterRate_true (evm : EVM.State)
    (I : ExecutionEnv) (outIlks : ByteArray)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkimAfterRateFrame I outIlks) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skimAfterRate evm I outIlks]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalTag_skim (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.storage (tagRef (.var "ilk"))) =
      .ok (endUIntValue (endSkimTagWord evm I)) := by
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
    (hbase := endSkimStore_get_tag_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, tagRef,
        endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen,
        endSkimStore_getElem_ilk I])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_tag (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endSkimTagWord, endSkimTagSlot]

theorem endEvalTagGuard_skim_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_skim evm I hsz68, htag]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalTagGuard_skim_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_skim evm I hsz68]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : ¬ (endSkimTagWord evm I).toNat = 0 := by
    intro hzero
    exact htag (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endSkimBodyTagFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSkimStore I) skimTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skimTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalTagGuard_skim_false evm I hsz68 htag)))

theorem endSkimBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord evm I ≠ ⟨0⟩)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endSkimStore I) skimTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skimTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_skim_true evm I hsz68 htag)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_skim_false evm I hvatNoCode)))

theorem endSkimBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord evm I ≠ ⟨0⟩)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkimStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endSkimStore I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagGuard_skim_true evm I hsz68 htag)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_skim_true evm I hvatCode)) <|
      ExecBlock.nil)

theorem endX_skim_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd869 := endRuntimeBlocks.endRuntime_block_851_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_869
    (R := endRuntimeBlocks.endRuntime_block_851_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_851_fallthrough_stack])
    (by simpa using rd869)

theorem endX_skim_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6705⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd873 := endRuntimeBlocks.endRuntime_block_851_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd6705 := endRuntimeBlocks.endRuntime_block_873
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_851_taken_stack] using rd873)
  have hoff4 : (UInt256.ofNat 4).toNat = 4 := by native_decide
  have hoff36 : ((UInt256.ofNat 32) + (UInt256.ofNat 4)).toNat = 36 := by native_decide
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_873_stack, endArg1AddressWord,
      endArg1Word, endArg0Word, calldataWord, hoff4, hoff36, hmask] using rd6705⟩

theorem endX_skim_tag_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkimTagWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_skim_to_body (g := g) hsz68 hsize hreach
  have hcond :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) =
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkimTagWorldWord σ I = ⟨0⟩
    exact htag
  obtain ⟨_, _, rd6725⟩ := endRuntimeBlocks.endRuntime_block_6705_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcond
    (by simpa using rdBody)
  exact endRuntimeBlocks.endRuntime_block_6725
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_6705_fallthrough_memory] using rd6725)

set_option maxHeartbeats 12000000 in
theorem endX_skim_to_vat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkimTagWorldWord σ I ≠ ⟨0⟩)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6874⟩
      (endSkimVatIlksCallStack σ I sel) (endSkimVatIlksCallMem I) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_skim_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkimTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw6795, k6795, C6795, rd6795⟩ :=
    endRuntimeBlocks.endRuntime_block_6705_taken_packed
      (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
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
                (storageRead I.codeOwner σ (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner σ (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hmaskGenerated]
      simpa [endPackVatTarget] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw6872, k6872, C6872, rd6872⟩ :=
    endRuntimeBlocks.endRuntime_block_6795_taken_packed
      (mem := endSkimVatIlksBaseMem I) (x0 := endArg1AddressWord I)
      (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by simpa [endSkimVatIlksBaseMem] using rd6795)
  have hbase : memLoad (UInt256.ofNat 64) (endSkimVatIlksBaseMem I) = ⟨128⟩ :=
    endSkimVatIlksBaseMem_mload64 I
  have hcallRaw := endSkimVatIlksCallMem_mload64 I
  dsimp [endSkimVatIlksCallMem, endRuntimeBlocks.endRuntime_block_6795_taken_memory] at hcallRaw
  rw [hbase] at hcallRaw
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_6795_taken_stack (ee := I)
          (mem := endSkimVatIlksBaseMem I) (σ := σ) (x0 := endArg1AddressWord I)
          (x1 := endArg0Word I) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endSkimVatIlksCallStack σ I sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_6795_taken_stack,
      endSkimVatIlksCallStack, endSkimVatIlksCallRest, endFlowVatIlksSelectorWord,
      endPackVatTarget]
    rw [hbase, hcallRaw, hlen, hend, hmaskGenerated]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 160 = (⟨160⟩ : UInt256) from by native_decide]
  have rd6872' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6872⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endSkimVatIlksCallStack σ I sel)
        (endSkimVatIlksCallMem I) aw6872 ByteArray.empty (cA, σ) k6872 C6872 := by
    simpa [hstackTaken, endSkimVatIlksCallMem] using rd6872
  have rd6874 := endRuntimeBlocks.endRuntime_block_6872
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := endSkimVatIlksCallStack σ I sel)
    (by simp [endSkimVatIlksCallStack, endSkimVatIlksCallRest]) rd6872'
  exact ⟨aw6872, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_6872_stack, endSkimVatIlksCallStack,
      endSkimVatIlksCallRest] using rd6874⟩

theorem endX_skim_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (htag : endSkimTagWorldWord σ I ≠ ⟨0⟩)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_skim_to_body (g := g) hsz68 hsize hreach
  have hcondTag :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠
        UInt256.ofNat 0 := by
    rw [endFlowTagHashSlot solcFreePtrMem I]
    change endSkimTagWorldWord σ I ≠ ⟨0⟩
    exact htag
  obtain ⟨aw6795, k6795, C6795, rd6795⟩ :=
    endRuntimeBlocks.endRuntime_block_6705_taken_packed
      (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
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
                (storageRead I.codeOwner σ (UInt256.ofNat 1))))) = UInt256.ofNat 0 := by
    rw [hmaskGenerated]
    change UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
      UInt256.ofNat 0
    rw [hvatNoCode]
    native_decide
  obtain ⟨_, _, _, rd6868⟩ :=
    endRuntimeBlocks.endRuntime_block_6795_fallthrough_packed
      (mem := endSkimVatIlksBaseMem I) (x0 := endArg1AddressWord I)
      (x1 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode
      (by simpa [endSkimVatIlksBaseMem] using rd6795)
  exact endRuntimeBlocks.endRuntime_block_6868
    (R := endRuntimeBlocks.endRuntime_block_6795_fallthrough_stack
      (mem := endSkimVatIlksBaseMem I) (σ := σ)
      (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_6795_fallthrough_stack])
    rd6868

set_option maxHeartbeats 12000000 in
theorem endX_skim_to_urns_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6914⟩
      (endSkimAfterVatIlksCursor I sel aw outIlks world).stack
      (endSkimVatIlksReturnMem I outIlks) (endSkimAfterVatIlksAw aw) outIlks
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7010⟩
      (endSkimUrnsCallStack world.2 I sel outIlks) (endSkimUrnsCallMem I outIlks)
      aw' outIlks world k' C' := by
  obtain ⟨aw6997, k6997, C6997, rd6997⟩ :=
    endRuntimeBlocks.endRuntime_block_6914_packed
      (x0 := UInt256.ofNat outIlks.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I outIlks))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1AddressWord I)
      (x4 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by simpa [endSkimAfterVatIlksCursor] using rd)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htargetGenerated :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endPackVatTarget world.2 I := by
    rw [hmaskGenerated]
    change UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
        solcAddrMask =
      UInt256.land solcAddrMask (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
    rw [u256_land_comm]
  have rd6997' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6997⟩
        (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I) ::
          endSkimUrnsCallStack world.2 I sel outIlks)
        (endSkimUrnsCallMem I outIlks) aw6997 outIlks world k6997 C6997 := by
    simpa [endSkimAfterVatIlksCursor, endSkimUrnsCallStack, endSkimUrnsCallRest,
      endSkimUrnsRawVatTarget, endSkimUrnsCallMem, endSkimUrnsSelectorWord,
      endFreeUrnsSelectorWord] using rd6997
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    have hnonzero : extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I) ≠ ⟨0⟩ := by
      rw [endSkimUrnsRawVatTarget, htargetGenerated]
      exact hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw7008, k7008, C7008, rd7008⟩ :=
    endRuntimeBlocks.endRuntime_block_6997_taken_packed
      (x0 := extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I))
      (R := endSkimUrnsCallStack world.2 I sel outIlks)
      (by simp [endSkimUrnsCallStack, endSkimUrnsCallRest]) hcondCode (by jump_dest)
      rd6997'
  have rd7008' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7008⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I)) ::
          endSkimUrnsCallStack world.2 I sel outIlks)
        (endSkimUrnsCallMem I outIlks) aw7008 outIlks world k7008 C7008 := by
    simpa [endRuntimeBlocks.endRuntime_block_6997_taken_stack] using rd7008
  have rd7010 := endRuntimeBlocks.endRuntime_block_7008
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I)))
    (R := endSkimUrnsCallStack world.2 I sel outIlks)
    (by simp [endSkimUrnsCallStack, endSkimUrnsCallRest]) rd7008'
  exact ⟨aw7008, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_7008_stack] using rd7010⟩

theorem endX_skim_urns_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6914⟩
      (endSkimAfterVatIlksCursor I sel aw outIlks world).stack
      (endSkimVatIlksReturnMem I outIlks) (endSkimAfterVatIlksAw aw) outIlks
      world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw6997, k6997, C6997, rd6997⟩ :=
    endRuntimeBlocks.endRuntime_block_6914_packed
      (x0 := UInt256.ofNat outIlks.size)
      (x1 := memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I outIlks))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg1AddressWord I)
      (x4 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by simpa [endSkimAfterVatIlksCursor] using rd)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htargetGenerated :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endPackVatTarget world.2 I := by
    rw [hmaskGenerated]
    change UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
        solcAddrMask =
      UInt256.land solcAddrMask (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
    rw [u256_land_comm]
  have rd6997' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6997⟩
        (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I) ::
          endSkimUrnsCallStack world.2 I sel outIlks)
        (endSkimUrnsCallMem I outIlks) aw6997 outIlks world k6997 C6997 := by
    simpa [endSkimAfterVatIlksCursor, endSkimUrnsCallStack, endSkimUrnsCallRest,
      endSkimUrnsRawVatTarget, endSkimUrnsCallMem, endSkimUrnsSelectorWord,
      endFreeUrnsSelectorWord] using rd6997
  have hcondNoCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I))) =
        UInt256.ofNat 0 := by
    have hzero :
        extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I) = ⟨0⟩ := by
      rw [endSkimUrnsRawVatTarget, htargetGenerated]
      exact hvatNoCode
    rw [hzero]
    native_decide
  obtain ⟨aw7004, k7004, C7004, rd7004⟩ :=
    endRuntimeBlocks.endRuntime_block_6997_fallthrough_packed
      (x0 := extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I))
      (R := endSkimUrnsCallStack world.2 I sel outIlks)
      (by simp [endSkimUrnsCallStack, endSkimUrnsCallRest]) hcondNoCode rd6997'
  exact endRuntimeBlocks.endRuntime_block_7004
    (R := endRuntimeBlocks.endRuntime_block_6997_fallthrough_stack
      (x0 := extCodeSizeWord world.2 (endSkimUrnsRawVatTarget world.2 I))
      (R := endSkimUrnsCallStack world.2 I sel outIlks))
    (by simp [endRuntimeBlocks.endRuntime_block_6997_fallthrough_stack,
      endSkimUrnsCallStack, endSkimUrnsCallRest])
    rd7004

set_option maxHeartbeats 12000000 in
theorem endSkimVatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkimVatIlksCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endSkimStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
      (sequenceExit ⟨6914⟩
        (fun cur frame e =>
          frame = endSkimAfterVatIlksFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          160 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I cur.rdata),
              ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSkimVatIlksReturnMem I cur.rdata ∧
          cur.aw = endSkimAfterVatIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨6874⟩ = some (.GAS, .none); decide)
    (by simp [endSkimVatIlksCallStack, endSkimVatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨6875⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkimVatIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skim]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endPackVatTarget σ I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkimVatIlksArgs evm I
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_vatIlks I (by omega : 36 ≤ I.calldata.size)]
    change some (endFlowVatIlksEncodedCall I) =
      some ((endSkimVatIlksCallMem I).readWithPadding 128 36)
    rw [endSkimVatIlksCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h160 : 160 ≤ out.size
    · rw [endExternalDecode_vatIlks_ok h160]
      intro rd hrel
      have rd6876 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
            ((⟨1⟩ : UInt256) :: endSkimVatIlksCallRest σ I sel)
            (endSkimVatIlksReturnMem I out) (endSkimVatIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endSkimVatIlksCallStack, endSkimVatIlksCallRest,
          endSkimVatIlksCallAw, endSkimVatIlksReturnMem] using rd
      have rd6892 := endRuntimeBlocks.endRuntime_block_6876_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkimVatIlksCallRest σ I sel)
        (by simp [endSkimVatIlksCallRest]) (by native_decide) (by jump_dest) rd6876
      have rd6892' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6892⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
            (endSkimVatIlksReturnMem I out) (endSkimVatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_6876_taken_stack,
          endSkimVatIlksCallRest] using rd6892
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
      have rd6914 := endRuntimeBlocks.endRuntime_block_6892_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd6892'
      refine ⟨.ok (endSkimAfterVatIlksFrame I out) evm',
        Endpoint.reached (endSkimAfterVatIlksCursor I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSkimAfterVatIlksCursor, endSkimAfterVatIlksAw,
            endRuntimeBlocks.endRuntime_block_6892_taken_stack] using rd6914⟩
      · exact ⟨rfl, rfl, hrel, hout, h160, rfl, rfl, rfl⟩
    · have hshort : out.size < 160 := by omega
      rw [endExternalDecode_vatIlks_none_short hshort]
      intro rd
      have rd6876 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
            ((⟨1⟩ : UInt256) :: endSkimVatIlksCallRest σ I sel)
            (endSkimVatIlksReturnMem I out) (endSkimVatIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endSkimVatIlksCallStack, endSkimVatIlksCallRest,
          endSkimVatIlksCallAw, endSkimVatIlksReturnMem] using rd
      have rd6892 := endRuntimeBlocks.endRuntime_block_6876_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkimVatIlksCallRest σ I sel)
        (by simp [endSkimVatIlksCallRest]) (by native_decide) (by jump_dest) rd6876
      have rd6892' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6892⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
            (endSkimVatIlksReturnMem I out) (endSkimVatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_6876_taken_stack,
          endSkimVatIlksCallRest] using rd6892
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
      have rd6910 := endRuntimeBlocks.endRuntime_block_6892_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd6892'
      exact endRuntimeBlocks.endRuntime_block_6910
        (R := endRuntimeBlocks.endRuntime_block_6892_fallthrough_stack
          (mem := endSkimVatIlksReturnMem I out) (rdata := out)
          (R := [⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_6892_fallthrough_stack])
        rd6910
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd6876 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6876⟩
          ((⟨0⟩ : UInt256) :: endSkimVatIlksCallRest σ I sel)
          (endSkimVatIlksReturnMem I out) (endSkimVatIlksCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endSkimVatIlksCallStack, endSkimVatIlksCallRest,
        endSkimVatIlksCallAw, endSkimVatIlksReturnMem] using rd
    have rd6883 := endRuntimeBlocks.endRuntime_block_6876_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkimVatIlksCallRest σ I sel)
      (by simp [endSkimVatIlksCallRest]) (by native_decide) rd6876
    exact endRuntimeBlocks.endRuntime_block_6883
      (R := endRuntimeBlocks.endRuntime_block_6876_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkimVatIlksCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_6876_fallthrough_stack,
        endSkimVatIlksCallRest])
      rd6883

set_option maxHeartbeats 12000000 in
theorem endSkimUrnsExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks rdata k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkimUrnsCallCursor world I sel aw outIlks rdata)
      k C (endSkimAfterRateFrame I outIlks) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", .var "urn"] "vatUrn" ]
      (sequenceExit ⟨7050⟩
        (fun cur frame e =>
          frame = endSkimAfterUrnsFrame I outIlks cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          64 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
              endFlowVatIlksRateWord outIlks,
              endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endSkimUrnsReturnMem I outIlks cur.rdata ∧
          cur.aw = endSkimAfterUrnsAw aw)
        (runtimeExit (.abi []))) := by
  have hrawTarget :
      endSkimUrnsRawVatTarget world.2 I = endPackVatTarget world.2 I := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
      native_decide
    unfold endSkimUrnsRawVatTarget endPackVatTarget
    rw [hmask]
    rw [u256_land_comm]
  have hbase := endSkimVatIlksReturnMem_mload64 I outIlks houtIlks h160
  have hcall := endSkimUrnsCallMem_mload64 I outIlks houtIlks h160
  have hlen :
      UInt256.sub (⟨128⟩ : UInt256) (⟨128⟩ : UInt256) + UInt256.ofNat 68 =
        (⟨68⟩ : UInt256) := by
    native_decide
  have hsum196 : (⟨128⟩ : UInt256) + UInt256.ofNat 68 = (⟨196⟩ : UInt256) := by
    native_decide
  have haddr160 : UInt256.ofNat 32 + (⟨128⟩ : UInt256) = (⟨160⟩ : UInt256) := by
    native_decide
  have hrate := endSkimVatIlksReturnMem_mload160 I outIlks houtIlks h160
  have hstatusOk : UInt256.isZero (⟨1⟩ : UInt256) = (⟨0⟩ : UInt256) := by
    native_decide
  have hrate160 :
      memLoad (⟨160⟩ : UInt256) (endSkimVatIlksReturnMem I outIlks) =
        endFlowVatIlksRateWord outIlks := by
    simpa using hrate
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨7010⟩ = some (.GAS, .none); decide)
    (by simp [endSkimUrnsCallStack, endSkimUrnsCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endSkimUrnsRawVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I, endArg1AddressValue I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨7011⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkimUrnsCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skimAfterRate evm I outIlks]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat
          (endSkimUrnsRawVatTarget world.2 I).toNat))
    rw [hrawTarget]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    exact endEvalSkimUrnsArgs evm I outIlks
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endSkimUrnsRawVatTarget world.2 I).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endSkimUrnsRawVatTarget world.2 I).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_urns_skim I hsz68]
    change some (endSkimUrnsEncodedCall I) =
      some ((endSkimUrnsCallMem I outIlks).readWithPadding
        (memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks)).toNat
        (UInt256.sub (memLoad (UInt256.ofNat 64)
              (endSkimVatIlksReturnMem I outIlks))
            (memLoad (UInt256.ofNat 64) (endSkimUrnsCallMem I outIlks)) +
          UInt256.ofNat 68).toNat)
    rw [hcall, hbase, hlen]
    change some (endSkimUrnsEncodedCall I) =
      some ((endSkimUrnsCallMem I outIlks).readWithPadding 128 68)
    rw [endSkimUrnsCallMem_readCallData I outIlks houtIlks h160]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h64 : 64 ≤ out.size
    · rw [endExternalDecode_urns_ok h64]
      intro rd hrel
      have rd7012 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
            ((⟨1⟩ : UInt256) :: endSkimUrnsCallRest world.2 I sel outIlks)
            (endSkimUrnsReturnMem I outIlks out) (endSkimUrnsCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkimUrnsCallStack, endSkimUrnsCallRest,
          endSkimUrnsCallAw, endSkimUrnsReturnMem, hbase, hcall, hlen] using rd
      have rd7028 := endRuntimeBlocks.endRuntime_block_7012_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkimUrnsCallRest world.2 I sel outIlks)
        (by simp [endSkimUrnsCallRest]) (by native_decide) (by jump_dest) rd7012
      have rd7028' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7028⟩
            [⟨0⟩, ⟨196⟩, endSkimUrnsSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outIlks,
              endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
            (endSkimUrnsReturnMem I outIlks out) (endSkimUrnsCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_7012_taken_stack,
          endSkimUrnsCallRest, hbase, hrawTarget, hsum196, haddr160, hrate,
          hstatusOk, hrate160, endSkimUrnsSelectorWord, endFreeUrnsSelectorWord]
          using rd7028
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide,
          ulit_toNat' out.size hout]
        exact h64
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd7050 := endRuntimeBlocks.endRuntime_block_7028_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨196⟩)
        (x2 := endSkimUrnsSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outIlks,
          endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd7028'
      have hmem64 := endSkimUrnsReturnMem_mload64 I outIlks out houtIlks h160 hout
      refine ⟨.ok (endSkimAfterUrnsFrame I outIlks out) evm',
        Endpoint.reached (endSkimAfterUrnsCursor I sel aw outIlks out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endSkimAfterUrnsCursor, endSkimAfterUrnsAw,
            endRuntimeBlocks.endRuntime_block_7028_taken_stack, hmem64] using rd7050⟩
      · exact ⟨rfl, rfl, hrel, hout, h64, rfl, rfl, rfl⟩
    · have hshort : out.size < 64 := by omega
      rw [endExternalDecode_urns_none_short hshort]
      intro rd
      have rd7012 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
            ((⟨1⟩ : UInt256) :: endSkimUrnsCallRest world.2 I sel outIlks)
            (endSkimUrnsReturnMem I outIlks out) (endSkimUrnsCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endSkimUrnsCallStack, endSkimUrnsCallRest,
          endSkimUrnsCallAw, endSkimUrnsReturnMem, hbase, hcall, hlen] using rd
      have rd7028 := endRuntimeBlocks.endRuntime_block_7012_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endSkimUrnsCallRest world.2 I sel outIlks)
        (by simp [endSkimUrnsCallRest]) (by native_decide) (by jump_dest) rd7012
      have rd7028' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7028⟩
            [⟨0⟩, ⟨196⟩, endSkimUrnsSelectorWord, endPackVatTarget world.2 I,
              ⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outIlks,
              endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
            (endSkimUrnsReturnMem I outIlks out) (endSkimUrnsCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_7012_taken_stack,
          endSkimUrnsCallRest, hbase, hrawTarget, hsum196, haddr160, hrate,
          hstatusOk, hrate160, endSkimUrnsSelectorWord, endFreeUrnsSelectorWord]
          using rd7028
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd7046 := endRuntimeBlocks.endRuntime_block_7028_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨196⟩)
        (x2 := endSkimUrnsSelectorWord) (x3 := endPackVatTarget world.2 I)
        (R := [⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outIlks,
          endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd7028'
      exact endRuntimeBlocks.endRuntime_block_7046
        (R := endRuntimeBlocks.endRuntime_block_7028_fallthrough_stack
          (mem := endSkimUrnsReturnMem I outIlks out) (rdata := out)
          (R := [⟨0⟩, ⟨0⟩, endFlowVatIlksRateWord outIlks,
            endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_7028_fallthrough_stack])
        rd7046
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd7012 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7012⟩
          ((⟨0⟩ : UInt256) :: endSkimUrnsCallRest world.2 I sel outIlks)
          (endSkimUrnsReturnMem I outIlks out) (endSkimUrnsCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endSkimUrnsCallStack, endSkimUrnsCallRest,
        endSkimUrnsCallAw, endSkimUrnsReturnMem, hbase, hcall, hlen] using rd
    have rd7019 := endRuntimeBlocks.endRuntime_block_7012_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkimUrnsCallRest world.2 I sel outIlks)
      (by simp [endSkimUrnsCallRest]) (by native_decide) rd7012
    exact endRuntimeBlocks.endRuntime_block_7019
      (R := endRuntimeBlocks.endRuntime_block_7012_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkimUrnsCallRest world.2 I sel outIlks))
      (by simp [endRuntimeBlocks.endRuntime_block_7012_fallthrough_stack,
        endSkimUrnsCallRest])
      rd7019

/-! ### Arithmetic suffix after `vat.urns` -/

abbrev endSkimInkWord (outUrns : ByteArray) : UInt256 :=
  endFreeUrnsInkWord outUrns

abbrev endSkimArtWord (outUrns : ByteArray) : UInt256 :=
  endFreeUrnsArtWord outUrns

abbrev endSkimInkValue (outUrns : ByteArray) : Value :=
  endUIntValue (endSkimInkWord outUrns)

abbrev endSkimArtValue (outUrns : ByteArray) : Value :=
  endUIntValue (endSkimArtWord outUrns)

abbrev endSkimOwe0Word (outIlks outUrns : ByteArray) : UInt256 :=
  endGenericRmulResult (endSkimArtWord outUrns) (endFlowVatIlksRateWord outIlks)

abbrev endSkimAfterInkFrame (I : ExecutionEnv) (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
      (endSkimInkValue outUrns) }

abbrev endSkimAfterArtFrame (I : ExecutionEnv) (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
      (endSkimArtValue outUrns) }

abbrev endSkimAfterOwe0Frame (I : ExecutionEnv) (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
      (endUIntValue (endSkimOwe0Word outIlks outUrns)) }

theorem endSkimAfterRateFrame_get_rate (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord outIlks)) := by
  exact store_get_self (endSkimAfterVatIlksFrame I outIlks).locals "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))

theorem endSkimAfterUrnsFrame_get_vatUrn (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterUrnsFrame I outIlks outUrns).locals.get? "vatUrn" =
      some (collapseReturns (endFreeUrnsValues outUrns)) := by
  exact store_get_self (endSkimAfterRateFrame I outIlks).locals "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))

theorem endSkimAfterInkFrame_get_vatUrn (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterInkFrame I outIlks outUrns).locals.get? "vatUrn" =
      some (collapseReturns (endFreeUrnsValues outUrns)) := by
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "vatUrn") =
      some (collapseReturns (endFreeUrnsValues outUrns))
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "vatUrn") (endSkimInkValue outUrns) (by decide)]
  exact endSkimAfterUrnsFrame_get_vatUrn I outIlks outUrns

theorem endSkimAfterArtFrame_get_art (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    (endSkimAfterArtFrame I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  exact store_get_self (endSkimAfterInkFrame I outIlks outUrns).locals "art"
    (endSkimArtValue outUrns)

theorem endSkimAfterArtFrame_get_rate (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    (endSkimAfterArtFrame I outIlks outUrns).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord outIlks)) := by
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "rate") =
      some (endUIntValue (endFlowVatIlksRateWord outIlks))
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "rate") (endSkimArtValue outUrns) (by decide)]
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "rate") =
      some (endUIntValue (endFlowVatIlksRateWord outIlks))
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "rate") (endSkimInkValue outUrns) (by decide)]
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "rate") =
      some (endUIntValue (endFlowVatIlksRateWord outIlks))
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "rate") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  exact endSkimAfterRateFrame_get_rate I outIlks

theorem endEvalSkimVatUrnVarAfterUrns (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterUrnsFrame I outIlks outUrns) evm (.var "vatUrn") =
      .ok (collapseReturns (endFreeUrnsValues outUrns)) := by
  simpa [evalExpr?, EvalResult.ofOption]
    using endSkimAfterUrnsFrame_get_vatUrn I outIlks outUrns

theorem endEvalSkimVatUrnVarAfterInk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterInkFrame I outIlks outUrns) evm (.var "vatUrn") =
      .ok (collapseReturns (endFreeUrnsValues outUrns)) := by
  simpa [evalExpr?, EvalResult.ofOption]
    using endSkimAfterInkFrame_get_vatUrn I outIlks outUrns

theorem endEvalSkimInkFromUrn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterUrnsFrame I outIlks outUrns) evm
      (.tupleGet (.var "vatUrn") 0) = .ok (endSkimInkValue outUrns) := by
  rw [evalExpr?]
  rw [endEvalSkimVatUrnVarAfterUrns evm I outIlks outUrns]
  simp [tupleGetValue?, collapseReturns, endFreeUrnsValues, endSkimInkValue,
    endSkimInkWord, EvalResult.bind, bind]

theorem endEvalSkimArtFromUrn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterInkFrame I outIlks outUrns) evm
      (.tupleGet (.var "vatUrn") 1) = .ok (endSkimArtValue outUrns) := by
  rw [evalExpr?]
  rw [endEvalSkimVatUrnVarAfterInk evm I outIlks outUrns]
  simp [tupleGetValue?, collapseReturns, endFreeUrnsValues, endSkimArtValue,
    endSkimArtWord, EvalResult.bind, bind]

theorem endEvalSkimRmul0Args (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExprs? config (endSkimAfterArtFrame I outIlks outUrns) evm
      [.var "art", .var "rate"] =
      .ok [endSkimArtValue outUrns, endUIntValue (endFlowVatIlksRateWord outIlks)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterArtFrame_get_art I outIlks outUrns]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterArtFrame_get_rate I outIlks outUrns]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_rmul_skim_art_rate (outIlks outUrns : ByteArray) :
    bindParams? rmulFunction.params
      [endSkimArtValue outUrns, endUIntValue (endFlowVatIlksRateWord outIlks)] =
      some (endGenericMulStore (endSkimArtWord outUrns)
        (endFlowVatIlksRateWord outIlks)) := by
  simp [bindParams?, rmulFunction, endGenericMulStore, endSkimArtValue, endUIntValue]

theorem endSkimInternalRmul0Ok (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hfit : (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat < UInt256.size) :
    ExecStmt config (endSkimAfterArtFrame I outIlks outUrns) evm
      (.internalCall "rmul" [.var "art", .var "rate"] "owe0")
      (.ok (endSkimAfterOwe0Frame I outIlks outUrns) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterOwe0Frame,
    endSkimOwe0Word] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterArtFrame I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "owe0")
      (args := [.var "art", .var "rate"])
      (argVals := [endSkimArtValue outUrns, endUIntValue (endFlowVatIlksRateWord outIlks)])
      (callee := rmulFunction)
      (locals := endGenericMulStore (endSkimArtWord outUrns)
        (endFlowVatIlksRateWord outIlks))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericRmulMStore (endSkimArtWord outUrns)
            (endFlowVatIlksRateWord outIlks) })
      (value := some [endUIntValue (endSkimOwe0Word outIlks outUrns)])
      (endEvalSkimRmul0Args evm I outIlks outUrns)
      (by
        change lookupCallable? contract "rmul" = some rmulFunction.toCallable
        rfl)
      (endBindParams_rmul_skim_art_rate outIlks outUrns)
      (by
        simpa [endSkimOwe0Word] using
          endGenericRmulFunctionOk evm (endSkimArtWord outUrns)
            (endFlowVatIlksRateWord outIlks) hfit)

theorem endSkimInternalRmul0Revert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hover : UInt256.size ≤ (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat) :
    ExecStmt config (endSkimAfterArtFrame I outIlks outUrns) evm
      (.internalCall "rmul" [.var "art", .var "rate"] "owe0") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSkimAfterArtFrame I outIlks outUrns) (evm := evm)
    (name := "rmul") (retVar := "owe0")
    (args := [.var "art", .var "rate"])
    (argVals := [endSkimArtValue outUrns, endUIntValue (endFlowVatIlksRateWord outIlks)])
    (callee := rmulFunction)
    (locals := endGenericMulStore (endSkimArtWord outUrns)
      (endFlowVatIlksRateWord outIlks))
    (endEvalSkimRmul0Args evm I outIlks outUrns)
    (by
      change lookupCallable? contract "rmul" = some rmulFunction.toCallable
      rfl)
    (endBindParams_rmul_skim_art_rate outIlks outUrns)
    (endGenericRmulFunctionRevert evm (endSkimArtWord outUrns)
      (endFlowVatIlksRateWord outIlks) hover)

def endSkimPostUrnsRmul0Stmts : List Stmt :=
  [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
    .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
    .internalCall "rmul" [.var "art", .var "rate"] "owe0" ]

theorem endSkimPostUrnsRmul0Ok (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hfit : (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat < UInt256.size) :
    ExecBlock config (endSkimAfterUrnsFrame I outIlks outUrns) evm
      endSkimPostUrnsRmul0Stmts
      (.ok (endSkimAfterOwe0Frame I outIlks outUrns) evm) := by
  simp [endSkimPostUrnsRmul0Stmts]
  exact ExecBlock.consNormal (ExecStmt.letDecl
      (endEvalSkimInkFromUrn evm I outIlks outUrns)) <|
    ExecBlock.consNormal (ExecStmt.letDecl
      (endEvalSkimArtFromUrn evm I outIlks outUrns)) <|
    ExecBlock.consNormal (endSkimInternalRmul0Ok evm I outIlks outUrns hfit)
      ExecBlock.nil

theorem endSkimPostUrnsRmul0Revert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hover : UInt256.size ≤ (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat) :
    ExecBlock config (endSkimAfterUrnsFrame I outIlks outUrns) evm
      endSkimPostUrnsRmul0Stmts .reverted := by
  simp [endSkimPostUrnsRmul0Stmts]
  exact ExecBlock.consNormal (ExecStmt.letDecl
      (endEvalSkimInkFromUrn evm I outIlks outUrns)) <|
    ExecBlock.consNormal (ExecStmt.letDecl
      (endEvalSkimArtFromUrn evm I outIlks outUrns)) <|
    ExecBlock.consRevert (endSkimInternalRmul0Revert evm I outIlks outUrns hover)

theorem endX_skim_to_rmul0 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7050⟩
      (endSkimAfterUrnsCursor I sel aw outIlks outUrns world).stack
      (endSkimUrnsReturnMem I outIlks outUrns) (endSkimAfterUrnsAw aw) outUrns
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endFlowVatIlksRateWord outIlks, endSkimArtWord outUrns,
        ⟨7079⟩, ⟨7099⟩, ⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimUrnsReturnMem I outIlks outUrns) aw' outUrns world k' C' := by
  have hloadInk := endSkimUrnsReturnMem_mload128 I outIlks outUrns
    houtIlks h160 houtUrns h64
  have hloadArt := endSkimUrnsReturnMem_mload160 I outIlks outUrns
    houtIlks h160 houtUrns h64
  have hloadInk128 :
      memLoad (⟨128⟩ : UInt256) (endSkimUrnsReturnMem I outIlks outUrns) =
        endSkimInkWord outUrns := by
    simpa [endSkimInkWord] using hloadInk
  have hloadArt160 :
      memLoad (⟨160⟩ : UInt256) (endSkimUrnsReturnMem I outIlks outUrns) =
        endSkimArtWord outUrns := by
    simpa [endSkimArtWord] using hloadArt
  have hoff : (⟨128⟩ : UInt256) + UInt256.ofNat 32 = (⟨160⟩ : UInt256) := by
    native_decide
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endRuntimeBlocks.endRuntime_block_7050_packed
      (x0 := UInt256.ofNat outUrns.size) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
      (x4 := endFlowVatIlksRateWord outIlks)
      (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endSkimAfterUrnsCursor] using rd)
  exact ⟨aw10114, k10114, C10114, by
    simpa [endRuntimeBlocks.endRuntime_block_7050_stack, hoff, hloadInk128,
      hloadArt160] using rd10114⟩

theorem endX_skim_rmul0_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size)
    (hfit : (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7050⟩
      (endSkimAfterUrnsCursor I sel aw outIlks outUrns world).stack
      (endSkimUrnsReturnMem I outIlks outUrns) (endSkimAfterUrnsAw aw) outUrns
      world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7079⟩
      [endSkimOwe0Word outIlks outUrns, ⟨7099⟩, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimUrnsReturnMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_skim_to_rmul0 (g := g) houtIlks h160 houtUrns h64 rd
  obtain ⟨aw7079, k7079, C7079, rd7079⟩ :=
    endX_flow_rmul_ok
      (x := endSkimArtWord outUrns)
      (y := endFlowVatIlksRateWord outIlks)
      (ret := (⟨7079⟩ : UInt256))
      (R := [⟨7099⟩, ⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      hfit (by jump_dest) (by simp) rd10114
  exact ⟨aw7079, k7079, C7079, by
    simpa [endSkimOwe0Word] using rd7079⟩

theorem endX_skim_rmul0_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) (h64 : 64 ≤ outUrns.size)
    (hover : UInt256.size ≤ (endSkimArtWord outUrns).toNat *
        (endFlowVatIlksRateWord outIlks).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7050⟩
      (endSkimAfterUrnsCursor I sel aw outIlks outUrns world).stack
      (endSkimUrnsReturnMem I outIlks outUrns) (endSkimAfterUrnsAw aw) outUrns
      world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_skim_to_rmul0 (g := g) houtIlks h160 houtUrns h64 rd
  exact endX_flow_rmul_fail
    (x := endSkimArtWord outUrns)
    (y := endFlowVatIlksRateWord outIlks)
    (ret := (⟨7079⟩ : UInt256))
    (R := [⟨7099⟩, ⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    hover (by simp) rd10114

abbrev endSkimOweWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endGenericRmulResult (endSkimOwe0Word outIlks outUrns) (endSkimTagWorldWord σ I)

abbrev endSkimTagHashMem (I : ExecutionEnv) (outIlks outUrns : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_7079_memory
    (mem := endSkimUrnsReturnMem I outIlks outUrns) (x7 := endArg0Word I)

abbrev endSkimOweWord (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endGenericRmulResult (endSkimOwe0Word outIlks outUrns) (endSkimTagWord evm I)

abbrev endSkimAfterOweFrame (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
      (endUIntValue (endSkimOweWord evm I outIlks outUrns)) }

abbrev endSkimWadWord (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  if (endSkimInkWord outUrns).toNat ≤
      (endSkimOweWord evm I outIlks outUrns).toNat then
    endSkimInkWord outUrns
  else
    endSkimOweWord evm I outIlks outUrns

abbrev endSkimWadWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  if (endSkimInkWord outUrns).toNat ≤
      (endSkimOweWorldWord σ I outIlks outUrns).toNat then
    endSkimInkWord outUrns
  else
    endSkimOweWorldWord σ I outIlks outUrns

abbrev endSkimAfterWadFrame (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
      (endUIntValue (endSkimWadWord evm I outIlks outUrns)) }

abbrev endSkimDiffWord (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endGenericSubResult (endSkimOweWord evm I outIlks outUrns)
    (endSkimWadWord evm I outIlks outUrns)

abbrev endSkimDiffWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endGenericSubResult (endSkimOweWorldWord σ I outIlks outUrns)
    (endSkimWadWorldWord σ I outIlks outUrns)

abbrev endSkimAfterDiffFrame (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
      (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) }

abbrev endSkimGapSlot (I : ExecutionEnv) : UInt256 :=
  gapSlot (endArg0Bytes32Key I)

abbrev endSkimGapWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 13) (endArg0Word I)

abbrev endSkimGapWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimGapSlot I)

abbrev endSkimGapWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endSkimGapWorldSlot I)

abbrev endSkimGapNewWord (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endSkimGapWord evm I + endSkimDiffWord evm I outIlks outUrns

abbrev endSkimGapNewWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : UInt256 :=
  endSkimGapWorldWord σ I + endSkimDiffWorldWord σ I outIlks outUrns

abbrev endSkimAfterGapNewFrame (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : Frame :=
  { contract := contract,
    locals := (endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
      (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) }

abbrev endSkimGapStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1,
    storageWrite I.codeOwner world.2 (endSkimGapWorldSlot I)
      (endSkimGapNewWorldWord world.2 I outIlks outUrns))

theorem endSkimAfterRateFrame_get_tag_none (I : ExecutionEnv) (outIlks : ByteArray) :
    (endSkimAfterRateFrame I outIlks).locals.get? "tag" = none := by
  change ((((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "tag") = none
  rw [store_get_ne ((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))) (k := "rate") (a := "tag")
    (endUIntValue (endFlowVatIlksRateWord outIlks)) (by decide)]
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "tag")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  exact endSkimStore_get_tag_none I

theorem endSkimAfterUrnsFrame_get_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterUrnsFrame I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "ilk") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  exact endSkimAfterRateFrame_get_ilk I outIlks

theorem endSkimAfterUrnsFrame_get_tag_none (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterUrnsFrame I outIlks outUrns).locals.get? "tag" = none := by
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "tag") = none
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "tag") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  exact endSkimAfterRateFrame_get_tag_none I outIlks

theorem endSkimAfterInkFrame_get_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterInkFrame I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "ilk") (endSkimInkValue outUrns) (by decide)]
  exact endSkimAfterUrnsFrame_get_ilk I outIlks outUrns

theorem endSkimAfterInkFrame_get_ink (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterInkFrame I outIlks outUrns).locals.get? "ink" =
      some (endSkimInkValue outUrns) := by
  exact store_get_self (endSkimAfterUrnsFrame I outIlks outUrns).locals "ink"
    (endSkimInkValue outUrns)

theorem endSkimAfterInkFrame_get_tag_none (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterInkFrame I outIlks outUrns).locals.get? "tag" = none := by
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "tag") = none
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "tag") (endSkimInkValue outUrns) (by decide)]
  exact endSkimAfterUrnsFrame_get_tag_none I outIlks outUrns

theorem endSkimAfterArtFrame_get_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterArtFrame I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "ilk") (endSkimArtValue outUrns) (by decide)]
  exact endSkimAfterInkFrame_get_ilk I outIlks outUrns

theorem endSkimAfterArtFrame_get_ink (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterArtFrame I outIlks outUrns).locals.get? "ink" =
      some (endSkimInkValue outUrns) := by
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "ink") = some (endSkimInkValue outUrns)
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "ink") (endSkimArtValue outUrns) (by decide)]
  exact endSkimAfterInkFrame_get_ink I outIlks outUrns

theorem endSkimAfterArtFrame_get_tag_none (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterArtFrame I outIlks outUrns).locals.get? "tag" = none := by
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "tag") = none
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "tag") (endSkimArtValue outUrns) (by decide)]
  exact endSkimAfterInkFrame_get_tag_none I outIlks outUrns

theorem endSkimAfterOwe0Frame_get_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "ilk")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  exact endSkimAfterArtFrame_get_ilk I outIlks outUrns

theorem endSkimAfterOwe0Frame_get_ink (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "ink" =
      some (endSkimInkValue outUrns) := by
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "ink") =
      some (endSkimInkValue outUrns)
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "ink")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  exact endSkimAfterArtFrame_get_ink I outIlks outUrns

theorem endSkimAfterOwe0Frame_get_owe0 (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "owe0" =
      some (endUIntValue (endSkimOwe0Word outIlks outUrns)) := by
  exact store_get_self (endSkimAfterArtFrame I outIlks outUrns).locals "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))

theorem endSkimAfterOwe0Frame_get_tag_none (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "tag" = none := by
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "tag") = none
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "tag")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  exact endSkimAfterArtFrame_get_tag_none I outIlks outUrns

theorem endSkimAfterOwe0Frame_mem_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    "ilk" ∈ (endSkimAfterOwe0Frame I outIlks outUrns).locals := by
  have hmemStore : "ilk" ∈ endSkimStore I := by
    simp [endSkimStore, Std.HashMap.mem_insert]
  have hmemVatIlk : "ilk" ∈ (endSkimAfterVatIlksFrame I outIlks).locals := by
    change "ilk" ∈ (endSkimStore I).insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues outIlks))
    simp [Std.HashMap.mem_insert, hmemStore]
  have hmemRate : "ilk" ∈ (endSkimAfterRateFrame I outIlks).locals := by
    change "ilk" ∈ (endSkimAfterVatIlksFrame I outIlks).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord outIlks))
    simp [Std.HashMap.mem_insert, hmemVatIlk]
  have hmemUrns : "ilk" ∈ (endSkimAfterUrnsFrame I outIlks outUrns).locals := by
    change "ilk" ∈ (endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
      (collapseReturns (endFreeUrnsValues outUrns))
    simp [Std.HashMap.mem_insert, hmemRate]
  have hmemInk : "ilk" ∈ (endSkimAfterInkFrame I outIlks outUrns).locals := by
    change "ilk" ∈ (endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
      (endSkimInkValue outUrns)
    simp [Std.HashMap.mem_insert, hmemUrns]
  have hmemArt : "ilk" ∈ (endSkimAfterArtFrame I outIlks outUrns).locals := by
    change "ilk" ∈ (endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
      (endSkimArtValue outUrns)
    simp [Std.HashMap.mem_insert, hmemInk]
  have hmem : "ilk" ∈ (endSkimAfterOwe0Frame I outIlks outUrns).locals := by
    change "ilk" ∈ (endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
      (endUIntValue (endSkimOwe0Word outIlks outUrns))
    simp [Std.HashMap.mem_insert, hmemArt]
  exact hmem

theorem endSkimAfterOwe0Frame_getElem_ilk (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hmem : "ilk" ∈ (endSkimAfterOwe0Frame I outIlks outUrns).locals) :
    getElem (endSkimAfterOwe0Frame I outIlks outUrns).locals "ilk" hmem =
      endArg0Bytes32Value I := by
  have hget := endSkimAfterOwe0Frame_get_ilk I outIlks outUrns
  have hopt :
      (endSkimAfterOwe0Frame I outIlks outUrns).locals["ilk"]? =
        some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos (endSkimAfterOwe0Frame I outIlks outUrns).locals
    "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endSkimAfterOwe0Frame_evalVar_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterOwe0Frame I outIlks outUrns) evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSkimAfterOwe0Frame_get_ilk I outIlks outUrns]
  rfl

theorem endArg0Bytes32Value_toKey (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    valueToKey? (endArg0Bytes32Value I) = some (endArg0Bytes32Key I) := by
  have hdrop := endFlowArg0Drop32 I hsz36
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]
    exact Nat.min_eq_left hdrop
  change (if ((I.calldata.toList.drop 4).take 32).length = bytes32Width.val + 1 then
      some (KeyValue.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32))
    else none) =
      some (KeyValue.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32))
  rw [if_pos (by simpa [bytes32Width] using hlen)]

set_option maxHeartbeats 8000000 in
theorem endEvalStorageRefTag_of_get_ilk (solm : Frame) (evm : EVM.State)
    (I : ExecutionEnv) (hget : solm.locals.get? "ilk" = some (endArg0Bytes32Value I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config solm evm
        (tagRef (.var "ilk")) =
      .ok { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] } := by
  have hvar : evalExpr? config solm evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [hget]
    rfl
  have hkey := endArg0Bytes32Value_toKey I hsz36
  rw [evalStorageRef, tagRef]
  simp only [evalStorageRefSteps, evalStorageRefStep, hvar, hkey,
    EvalResult.bind, EvalResult.ofOption, bind, pure, List.nil_append]

theorem endEvalStorageRefTag_skimAfterOwe0 (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endSkimAfterOwe0Frame I outIlks outUrns) evm
        (tagRef (.var "ilk")) =
      .ok { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] } :=
  endEvalStorageRefTag_of_get_ilk
    (endSkimAfterOwe0Frame I outIlks outUrns) evm I
    (endSkimAfterOwe0Frame_get_ilk I outIlks outUrns)
    (by omega)

theorem endStorageTypeAt_tag_mindex (ilk : KeyValue) :
    storageTypeAt? contract.storage { base := "tag", steps := [.mindex ilk] } =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]

theorem endStorageLocLoad_tag_skim (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm (wordLoc (tagSlot (endArg0Bytes32Key I))) =
      endUIntValue (endSkimTagWord evm I) := by
  simp [endRuntimeStorageLocLoad_uint256, endSkimTagWord, endSkimTagSlot, endUIntValue]

set_option maxHeartbeats 12000000 in
theorem endEvalTag_skimAfterOwe0 (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endSkimAfterOwe0Frame I outIlks outUrns) evm
        (.storage (tagRef (.var "ilk"))) =
      .ok (endUIntValue (endSkimTagWord evm I)) := by
  simpa [endStorageLocLoad_tag_skim evm I] using
    (evalExpr_storage_scalar
      (cfg := config)
      (solm := endSkimAfterOwe0Frame I outIlks outUrns)
      (evm := evm)
      (slot := tagRef (.var "ilk"))
      (er := { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] })
      (t := .int uint256Int)
      (loc := wordLoc (tagSlot (endArg0Bytes32Key I)))
      (hbase := endSkimAfterOwe0Frame_get_tag_none I outIlks outUrns)
      (her := endEvalStorageRefTag_skimAfterOwe0 evm I outIlks outUrns hsz68)
      (hty := endStorageTypeAt_tag_mindex (endArg0Bytes32Key I))
      (hloc := endConfig_storage_tag (endArg0Bytes32Key I)))

theorem endEvalSkimRmul1Args (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endSkimAfterOwe0Frame I outIlks outUrns) evm
      [.var "owe0", .storage (tagRef (.var "ilk"))] =
      .ok [endUIntValue (endSkimOwe0Word outIlks outUrns),
        endUIntValue (endSkimTagWord evm I)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterOwe0Frame_get_owe0 I outIlks outUrns]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalTag_skimAfterOwe0 evm I outIlks outUrns hsz68]
  simp [EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_rmul_skim_owe0_tag (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    bindParams? rmulFunction.params
      [endUIntValue (endSkimOwe0Word outIlks outUrns),
        endUIntValue (endSkimTagWord evm I)] =
      some (endGenericMulStore (endSkimOwe0Word outIlks outUrns)
        (endSkimTagWord evm I)) := by
  simp [bindParams?, rmulFunction, endGenericMulStore, endUIntValue]

theorem endSkimInternalRmul1Ok (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endSkimOwe0Word outIlks outUrns).toNat *
        (endSkimTagWord evm I).toNat < UInt256.size) :
    ExecStmt config (endSkimAfterOwe0Frame I outIlks outUrns) evm
      (.internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe")
      (.ok (endSkimAfterOweFrame evm I outIlks outUrns) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterOweFrame,
    endSkimOweWord] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterOwe0Frame I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "owe")
      (args := [.var "owe0", .storage (tagRef (.var "ilk"))])
      (argVals := [endUIntValue (endSkimOwe0Word outIlks outUrns),
        endUIntValue (endSkimTagWord evm I)])
      (callee := rmulFunction)
      (locals := endGenericMulStore (endSkimOwe0Word outIlks outUrns)
        (endSkimTagWord evm I))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericRmulMStore (endSkimOwe0Word outIlks outUrns)
            (endSkimTagWord evm I) })
      (value := some [endUIntValue (endSkimOweWord evm I outIlks outUrns)])
      (endEvalSkimRmul1Args evm I outIlks outUrns hsz68)
      (by
        change lookupCallable? contract "rmul" = some rmulFunction.toCallable
        rfl)
      (endBindParams_rmul_skim_owe0_tag evm I outIlks outUrns)
      (by
        simpa [endSkimOweWord] using
          endGenericRmulFunctionOk evm (endSkimOwe0Word outIlks outUrns)
            (endSkimTagWord evm I) hfit)

theorem endSkimInternalRmul1Revert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endSkimOwe0Word outIlks outUrns).toNat *
        (endSkimTagWord evm I).toNat) :
    ExecStmt config (endSkimAfterOwe0Frame I outIlks outUrns) evm
      (.internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSkimAfterOwe0Frame I outIlks outUrns)
    (evm := evm) (name := "rmul") (retVar := "owe")
    (args := [.var "owe0", .storage (tagRef (.var "ilk"))])
    (argVals := [endUIntValue (endSkimOwe0Word outIlks outUrns),
      endUIntValue (endSkimTagWord evm I)])
    (callee := rmulFunction)
    (locals := endGenericMulStore (endSkimOwe0Word outIlks outUrns)
      (endSkimTagWord evm I))
    (endEvalSkimRmul1Args evm I outIlks outUrns hsz68)
    (by
      change lookupCallable? contract "rmul" = some rmulFunction.toCallable
      rfl)
    (endBindParams_rmul_skim_owe0_tag evm I outIlks outUrns)
    (endGenericRmulFunctionRevert evm (endSkimOwe0Word outIlks outUrns)
      (endSkimTagWord evm I) hover)

theorem endSkimAfterOweFrame_get_ink (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOweFrame evm I outIlks outUrns).locals.get? "ink" =
      some (endSkimInkValue outUrns) := by
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "ink") =
      some (endSkimInkValue outUrns)
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "ink")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOwe0Frame_get_ink I outIlks outUrns

theorem endSkimAfterOweFrame_get_owe (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOweFrame evm I outIlks outUrns).locals.get? "owe" =
      some (endUIntValue (endSkimOweWord evm I outIlks outUrns)) := by
  exact store_get_self (endSkimAfterOwe0Frame I outIlks outUrns).locals "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))

theorem endEvalGenericMinCondTrue (evm : EVM.State) (x y : UInt256)
    (hle : x.toNat ≤ y.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (.binary .le (.var "x") (.var "y")) = .ok (.bool true) := by
  have hleInt : decide (Int.ofNat x.toNat ≤ Int.ofNat y.toNat) = true :=
    decide_eq_true (Int.ofNat_le.mpr hle)
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hleInt]

theorem endEvalGenericMinCondFalse (evm : EVM.State) (x y : UInt256)
    (hlt : y.toNat < x.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (.binary .le (.var "x") (.var "y")) = .ok (.bool false) := by
  have hleInt : decide (Int.ofNat x.toNat ≤ Int.ofNat y.toNat) = false :=
    decide_eq_false (show ¬ Int.ofNat x.toNat ≤ Int.ofNat y.toNat from by
      exact not_le_of_gt (Int.ofNat_lt.mpr hlt))
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hleInt]

theorem endGenericMinFunctionLeft (evm : EVM.State) (x y : UInt256)
    (hle : x.toNat ≤ y.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      minFunction.body
      (.returned { contract := contract, locals := endGenericMulStore x y } evm
        (some [endUIntValue x])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [minFunction] using
    (ExecBlock.consReturn
      (ExecStmt.iteTrue
        (result := .returned { contract := contract, locals := endGenericMulStore x y } evm
          (some [endUIntValue x]))
        (endEvalGenericMinCondTrue evm x y hle)
        (ExecBlock.consReturn (stmts := [])
          (ExecStmt.return
            (exprs := [.var "x"]) (values := [endUIntValue x])
            (by
              simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind,
                bind, pure, endGenericMulStore_getElem_x])))))

theorem endGenericMinFunctionRight (evm : EVM.State) (x y : UInt256)
    (hlt : y.toNat < x.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      minFunction.body
      (.returned { contract := contract, locals := endGenericMulStore x y } evm
        (some [endUIntValue y])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [minFunction] using
    (ExecBlock.consReturn
      (ExecStmt.iteFalse
        (result := .returned { contract := contract, locals := endGenericMulStore x y } evm
          (some [endUIntValue y]))
        (endEvalGenericMinCondFalse evm x y hlt)
        (ExecBlock.consReturn (stmts := [])
          (ExecStmt.return
            (exprs := [.var "y"]) (values := [endUIntValue y])
            (by
              simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind,
                bind, pure, endGenericMulStore_getElem_y])))))

abbrev endGenericAddResult (x y : UInt256) : UInt256 :=
  x + y

abbrev endGenericAddZStore (x y : UInt256) : Store :=
  (endGenericMulStore x y).insert "z" (endUIntValue (endGenericAddResult x y))

theorem endGenericAddZStore_get_z (x y : UInt256) :
    (endGenericAddZStore x y).get? "z" =
      some (endUIntValue (endGenericAddResult x y)) := by
  exact store_get_self (endGenericMulStore x y) "z" (endUIntValue (endGenericAddResult x y))

theorem endGenericAddZStore_get_x (x y : UInt256) :
    (endGenericAddZStore x y).get? "x" = some (endUIntValue x) := by
  unfold endGenericAddZStore
  rw [store_get_ne (endGenericMulStore x y) (k := "z") (a := "x")
    (endUIntValue (endGenericAddResult x y)) (by decide)]
  exact endGenericMulStore_get_x x y

theorem endEvalGenericAddExpr (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat + y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .ok (endUIntValue (endGenericAddResult x y)) := by
  have hsum : (endGenericAddResult x y).toNat = x.toNat + y.toNat := by
    rw [endGenericAddResult, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hfitPow : x.toNat + y.toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat (x.toNat + y.toNat) ≥ (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have haddInt :
      Int.ofNat x.toNat + Int.ofNat y.toNat =
        Int.ofNat (x.toNat + y.toNat) := by
    exact (Nat.cast_add x.toNat y.toNat).symm
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt]
  have hcond :
      (decide (Int.ofNat (x.toNat + y.toNat) < 0) ||
        decide (Int.ofNat (x.toNat + y.toNat) ≥ (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg : decide (Int.ofNat (x.toNat + y.toNat) < 0) = false :=
      decide_eq_false (show ¬ Int.ofNat (x.toNat + y.toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat (x.toNat + y.toNat) ≥ (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [endGenericAddResult, hsum, endUIntValue]

theorem endEvalGenericAddExpr_revert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat (x.toNat + y.toNat) ≥ (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have haddInt :
      Int.ofNat x.toNat + Int.ofNat y.toNat =
        Int.ofNat (x.toNat + y.toNat) := by
    exact (Nat.cast_add x.toNat y.toNat).symm
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt, hhi]
  simp

theorem endEvalGenericAddGuard (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat + y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endGenericAddZStore x y } evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsum : (endGenericAddResult x y).toNat = x.toNat + y.toNat := by
    rw [endGenericAddResult, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgeProp :
      Int.ofNat x.toNat ≤ Int.ofNat (endGenericAddResult x y).toNat := by
    rw [hsum]
    exact Int.ofNat_le.mpr (by omega)
  have hge :
      decide (Int.ofNat (endGenericAddResult x y).toNat ≥ Int.ofNat x.toNat) = true := by
    exact decide_eq_true hgeProp
  simp only [evalExpr?, endGenericAddZStore_get_z, endGenericAddZStore_get_x,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hge]

theorem endGenericAddFunctionOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      addFunction.body
      (.returned { contract := contract, locals := endGenericAddZStore x y } evm
        (some [endUIntValue (endGenericAddResult x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [addFunction, endGenericAddZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalGenericAddExpr evm x y hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalGenericAddGuard evm x y hfit)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [endUIntValue (endGenericAddResult x y)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endGenericAddZStore_get_z])))

theorem endGenericAddFunctionRevert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      addFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [addFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalGenericAddExpr_revert evm x y hover)))

theorem endEvalSkimMinArgs (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExprs? config (endSkimAfterOweFrame evm I outIlks outUrns) evm
      [.var "ink", .var "owe"] =
      .ok [endSkimInkValue outUrns,
        endUIntValue (endSkimOweWord evm I outIlks outUrns)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterOweFrame_get_ink evm I outIlks outUrns]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterOweFrame_get_owe evm I outIlks outUrns]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_min_skim_ink_owe (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    bindParams? minFunction.params
      [endSkimInkValue outUrns, endUIntValue (endSkimOweWord evm I outIlks outUrns)] =
      some (endGenericMulStore (endSkimInkWord outUrns)
        (endSkimOweWord evm I outIlks outUrns)) := by
  simp [bindParams?, minFunction, endGenericMulStore, endSkimInkValue, endUIntValue]

theorem endSkimInternalMinLeft (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hle : (endSkimInkWord outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat) :
    ExecStmt config (endSkimAfterOweFrame evm I outIlks outUrns) evm
      (.internalCall "min" [.var "ink", .var "owe"] "wad")
      (.ok (endSkimAfterWadFrame evm I outIlks outUrns) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterWadFrame,
    endSkimWadWord, hle] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterOweFrame evm I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "min") (retVar := "wad")
      (args := [.var "ink", .var "owe"])
      (argVals := [endSkimInkValue outUrns,
        endUIntValue (endSkimOweWord evm I outIlks outUrns)])
      (callee := minFunction)
      (locals := endGenericMulStore (endSkimInkWord outUrns)
        (endSkimOweWord evm I outIlks outUrns))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericMulStore (endSkimInkWord outUrns)
            (endSkimOweWord evm I outIlks outUrns) })
      (value := some [endUIntValue (endSkimInkWord outUrns)])
      (endEvalSkimMinArgs evm I outIlks outUrns)
      (by
        change lookupCallable? contract "min" = some minFunction.toCallable
        rfl)
      (endBindParams_min_skim_ink_owe evm I outIlks outUrns)
      (endGenericMinFunctionLeft evm (endSkimInkWord outUrns)
        (endSkimOweWord evm I outIlks outUrns) hle)

theorem endSkimInternalMinRight (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hlt : (endSkimOweWord evm I outIlks outUrns).toNat <
        (endSkimInkWord outUrns).toNat) :
    ExecStmt config (endSkimAfterOweFrame evm I outIlks outUrns) evm
      (.internalCall "min" [.var "ink", .var "owe"] "wad")
      (.ok (endSkimAfterWadFrame evm I outIlks outUrns) evm) := by
  have hnot :
      ¬ (endSkimInkWord outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat := by
    omega
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterWadFrame,
    endSkimWadWord, if_neg hnot] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterOweFrame evm I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "min") (retVar := "wad")
      (args := [.var "ink", .var "owe"])
      (argVals := [endSkimInkValue outUrns,
        endUIntValue (endSkimOweWord evm I outIlks outUrns)])
      (callee := minFunction)
      (locals := endGenericMulStore (endSkimInkWord outUrns)
        (endSkimOweWord evm I outIlks outUrns))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericMulStore (endSkimInkWord outUrns)
            (endSkimOweWord evm I outIlks outUrns) })
      (value := some [endUIntValue (endSkimOweWord evm I outIlks outUrns)])
      (endEvalSkimMinArgs evm I outIlks outUrns)
      (by
        change lookupCallable? contract "min" = some minFunction.toCallable
        rfl)
      (endBindParams_min_skim_ink_owe evm I outIlks outUrns)
      (endGenericMinFunctionRight evm (endSkimInkWord outUrns)
        (endSkimOweWord evm I outIlks outUrns) hlt)

theorem endSkimAfterOwe0Frame_get_art (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "art") =
      some (endSkimArtValue outUrns)
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "art")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  exact endSkimAfterArtFrame_get_art I outIlks outUrns

theorem endSkimAfterOweFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOweFrame evm I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "ilk")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOwe0Frame_get_ilk I outIlks outUrns

theorem endSkimAfterOweFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOweFrame evm I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "art") =
      some (endSkimArtValue outUrns)
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "art")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOwe0Frame_get_art I outIlks outUrns

theorem endSkimAfterWadFrame_get_owe (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterWadFrame evm I outIlks outUrns).locals.get? "owe" =
      some (endUIntValue (endSkimOweWord evm I outIlks outUrns)) := by
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "owe") =
      some (endUIntValue (endSkimOweWord evm I outIlks outUrns))
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "owe")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOweFrame_get_owe evm I outIlks outUrns

theorem endSkimAfterWadFrame_get_wad (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterWadFrame evm I outIlks outUrns).locals.get? "wad" =
      some (endUIntValue (endSkimWadWord evm I outIlks outUrns)) := by
  exact store_get_self (endSkimAfterOweFrame evm I outIlks outUrns).locals "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))

theorem endSkimAfterWadFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterWadFrame evm I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "ilk")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOweFrame_get_ilk evm I outIlks outUrns

theorem endSkimAfterWadFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterWadFrame evm I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "art") =
      some (endSkimArtValue outUrns)
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "art")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOweFrame_get_art evm I outIlks outUrns

theorem endEvalSkimSubArgs (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExprs? config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      [.var "owe", .var "wad"] =
      .ok [endUIntValue (endSkimOweWord evm I outIlks outUrns),
        endUIntValue (endSkimWadWord evm I outIlks outUrns)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterWadFrame_get_owe evm I outIlks outUrns]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterWadFrame_get_wad evm I outIlks outUrns]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_sub_skim_owe_wad (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    bindParams? subFunction.params
      [endUIntValue (endSkimOweWord evm I outIlks outUrns),
        endUIntValue (endSkimWadWord evm I outIlks outUrns)] =
      some (endGenericMulStore (endSkimOweWord evm I outIlks outUrns)
        (endSkimWadWord evm I outIlks outUrns)) := by
  simp [bindParams?, subFunction, endGenericMulStore, endUIntValue]

theorem endSkimInternalSubOk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hle : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat) :
    ExecStmt config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      (.internalCall "sub" [.var "owe", .var "wad"] "diff")
      (.ok (endSkimAfterDiffFrame evm I outIlks outUrns) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterDiffFrame,
    endSkimDiffWord, endGenericSubResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterWadFrame evm I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "sub") (retVar := "diff")
      (args := [.var "owe", .var "wad"])
      (argVals := [endUIntValue (endSkimOweWord evm I outIlks outUrns),
        endUIntValue (endSkimWadWord evm I outIlks outUrns)])
      (callee := subFunction)
      (locals := endGenericMulStore (endSkimOweWord evm I outIlks outUrns)
        (endSkimWadWord evm I outIlks outUrns))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericSubZStore (endSkimOweWord evm I outIlks outUrns)
            (endSkimWadWord evm I outIlks outUrns) })
      (value := some [endUIntValue (endSkimDiffWord evm I outIlks outUrns)])
      (endEvalSkimSubArgs evm I outIlks outUrns)
      (by
        change lookupCallable? contract "sub" = some subFunction.toCallable
        rfl)
      (endBindParams_sub_skim_owe_wad evm I outIlks outUrns)
      (by
        simpa [endSkimDiffWord, endGenericSubResult] using
          endGenericSubFunctionOk evm (endSkimOweWord evm I outIlks outUrns)
            (endSkimWadWord evm I outIlks outUrns) hle)

theorem endSkimInternalSubRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hlt : (endSkimOweWord evm I outIlks outUrns).toNat <
        (endSkimWadWord evm I outIlks outUrns).toNat) :
    ExecStmt config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      (.internalCall "sub" [.var "owe", .var "wad"] "diff") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSkimAfterWadFrame evm I outIlks outUrns)
    (evm := evm) (name := "sub") (retVar := "diff")
    (args := [.var "owe", .var "wad"])
    (argVals := [endUIntValue (endSkimOweWord evm I outIlks outUrns),
      endUIntValue (endSkimWadWord evm I outIlks outUrns)])
    (callee := subFunction)
    (locals := endGenericMulStore (endSkimOweWord evm I outIlks outUrns)
      (endSkimWadWord evm I outIlks outUrns))
    (endEvalSkimSubArgs evm I outIlks outUrns)
    (by
      change lookupCallable? contract "sub" = some subFunction.toCallable
      rfl)
    (endBindParams_sub_skim_owe_wad evm I outIlks outUrns)
    (endGenericSubFunctionRevert evm (endSkimOweWord evm I outIlks outUrns)
      (endSkimWadWord evm I outIlks outUrns) hlt)

theorem endSkimAfterDiffFrame_get_diff (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "diff" =
      some (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) := by
  exact store_get_self (endSkimAfterWadFrame evm I outIlks outUrns).locals "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))

theorem endSkimAfterDiffFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "ilk")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterWadFrame_get_ilk evm I outIlks outUrns

theorem endSkimAfterDiffFrame_get_wad (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "wad" =
      some (endUIntValue (endSkimWadWord evm I outIlks outUrns)) := by
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "wad") =
      some (endUIntValue (endSkimWadWord evm I outIlks outUrns))
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "wad")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterWadFrame_get_wad evm I outIlks outUrns

theorem endSkimAfterDiffFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "art") =
      some (endSkimArtValue outUrns)
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "art")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterWadFrame_get_art evm I outIlks outUrns

theorem endSkimAfterDiffFrame_get_gap_none (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "gap" = none := by
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "gap")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "gap")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "gap")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "gap")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "gap") = none
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "gap") (endSkimArtValue outUrns) (by decide)]
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "gap") = none
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "gap") (endSkimInkValue outUrns) (by decide)]
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "gap") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  change (((endSkimAfterVatIlksFrame I outIlks).locals.insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "gap") = none
  rw [store_get_ne (endSkimAfterVatIlksFrame I outIlks).locals
    (k := "rate") (a := "gap") (endUIntValue (endFlowVatIlksRateWord outIlks))
    (by decide)]
  change (((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).get? "gap") = none
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "gap")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "urn"
    (endArg1AddressValue I)).get? "gap") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "urn") (a := "gap") (endArg1AddressValue I) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "gap")
    (endArg0Bytes32Value I) (by decide)]
  simp

set_option maxHeartbeats 8000000 in
theorem endEvalStorageRefGap_of_get_ilk (solm : Frame) (evm : EVM.State)
    (I : ExecutionEnv) (hget : solm.locals.get? "ilk" = some (endArg0Bytes32Value I))
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config solm evm
        (gapRef (.var "ilk")) =
      .ok { base := "gap", steps := [.mindex (endArg0Bytes32Key I)] } := by
  have hvar : evalExpr? config solm evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [hget]
    rfl
  have hkey := endArg0Bytes32Value_toKey I hsz36
  rw [evalStorageRef, gapRef]
  simp only [evalStorageRefSteps, evalStorageRefStep, hvar, hkey,
    EvalResult.bind, EvalResult.ofOption, bind, pure, List.nil_append]

theorem endEvalStorageRefGap_skimAfterDiff (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endSkimAfterDiffFrame evm I outIlks outUrns) evm
        (gapRef (.var "ilk")) =
      .ok { base := "gap", steps := [.mindex (endArg0Bytes32Key I)] } :=
  endEvalStorageRefGap_of_get_ilk
    (endSkimAfterDiffFrame evm I outIlks outUrns) evm I
    (endSkimAfterDiffFrame_get_ilk evm I outIlks outUrns)
    (by omega)

theorem endStorageTypeAt_gap_mindex (ilk : KeyValue) :
    storageTypeAt? contract.storage { base := "gap", steps := [.mindex ilk] } =
      some (.elem (.int uint256Int)) := by
  simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]

theorem endStorageLocLoad_gap_skim (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm (wordLoc (gapSlot (endArg0Bytes32Key I))) =
      endUIntValue (endSkimGapWord evm I) := by
  simp [endRuntimeStorageLocLoad_uint256, endSkimGapWord, endSkimGapSlot, endUIntValue]

set_option maxHeartbeats 12000000 in
theorem endEvalGap_skimAfterDiff (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endSkimAfterDiffFrame evm I outIlks outUrns) evm
        (.storage (gapRef (.var "ilk"))) =
      .ok (endUIntValue (endSkimGapWord evm I)) := by
  simpa [endStorageLocLoad_gap_skim evm I] using
    (evalExpr_storage_scalar
      (cfg := config)
      (solm := endSkimAfterDiffFrame evm I outIlks outUrns)
      (evm := evm)
      (slot := gapRef (.var "ilk"))
      (er := { base := "gap", steps := [.mindex (endArg0Bytes32Key I)] })
      (t := .int uint256Int)
      (loc := wordLoc (gapSlot (endArg0Bytes32Key I)))
      (hbase := endSkimAfterDiffFrame_get_gap_none evm I outIlks outUrns)
      (her := endEvalStorageRefGap_skimAfterDiff evm I outIlks outUrns hsz68)
      (hty := endStorageTypeAt_gap_mindex (endArg0Bytes32Key I))
      (hloc := endConfig_storage_gap (endArg0Bytes32Key I)))

theorem endEvalSkimAddArgs (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endSkimAfterDiffFrame evm I outIlks outUrns) evm
      [.storage (gapRef (.var "ilk")), .var "diff"] =
      .ok [endUIntValue (endSkimGapWord evm I),
        endUIntValue (endSkimDiffWord evm I outIlks outUrns)] := by
  rw [evalExprs?]
  rw [endEvalGap_skimAfterDiff evm I outIlks outUrns hsz68]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endSkimAfterDiffFrame_get_diff evm I outIlks outUrns]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_add_skim_gap_diff (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    bindParams? addFunction.params
      [endUIntValue (endSkimGapWord evm I),
        endUIntValue (endSkimDiffWord evm I outIlks outUrns)] =
      some (endGenericMulStore (endSkimGapWord evm I)
        (endSkimDiffWord evm I outIlks outUrns)) := by
  simp [bindParams?, addFunction, endGenericMulStore, endUIntValue]

theorem endSkimInternalAddOk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat < UInt256.size) :
    ExecStmt config (endSkimAfterDiffFrame evm I outIlks outUrns) evm
      (.internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew")
      (.ok (endSkimAfterGapNewFrame evm I outIlks outUrns) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endSkimAfterGapNewFrame,
    endSkimGapNewWord, endGenericAddResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endSkimAfterDiffFrame evm I outIlks outUrns)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "gapNew")
      (args := [.storage (gapRef (.var "ilk")), .var "diff"])
      (argVals := [endUIntValue (endSkimGapWord evm I),
        endUIntValue (endSkimDiffWord evm I outIlks outUrns)])
      (callee := addFunction)
      (locals := endGenericMulStore (endSkimGapWord evm I)
        (endSkimDiffWord evm I outIlks outUrns))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericAddZStore (endSkimGapWord evm I)
            (endSkimDiffWord evm I outIlks outUrns) })
      (value := some [endUIntValue (endSkimGapNewWord evm I outIlks outUrns)])
      (endEvalSkimAddArgs evm I outIlks outUrns hsz68)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_skim_gap_diff evm I outIlks outUrns)
      (by
        simpa [endSkimGapNewWord, endGenericAddResult] using
          endGenericAddFunctionOk evm (endSkimGapWord evm I)
            (endSkimDiffWord evm I outIlks outUrns) hfit)

theorem endSkimInternalAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat) :
    ExecStmt config (endSkimAfterDiffFrame evm I outIlks outUrns) evm
      (.internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endSkimAfterDiffFrame evm I outIlks outUrns)
    (evm := evm) (name := "add") (retVar := "gapNew")
    (args := [.storage (gapRef (.var "ilk")), .var "diff"])
    (argVals := [endUIntValue (endSkimGapWord evm I),
      endUIntValue (endSkimDiffWord evm I outIlks outUrns)])
    (callee := addFunction)
    (locals := endGenericMulStore (endSkimGapWord evm I)
      (endSkimDiffWord evm I outIlks outUrns))
    (endEvalSkimAddArgs evm I outIlks outUrns hsz68)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_skim_gap_diff evm I outIlks outUrns)
    (endGenericAddFunctionRevert evm (endSkimGapWord evm I)
      (endSkimDiffWord evm I outIlks outUrns) hover)

theorem endSkimAfterGapNewFrame_get_gapNew (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "gapNew" =
      some (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) := by
  exact store_get_self (endSkimAfterDiffFrame evm I outIlks outUrns).locals "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))

theorem endSkimAfterGapNewFrame_get_wad (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "wad" =
      some (endUIntValue (endSkimWadWord evm I outIlks outUrns)) := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "wad") =
      some (endUIntValue (endSkimWadWord evm I outIlks outUrns))
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "wad")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterDiffFrame_get_wad evm I outIlks outUrns

theorem endSkimAfterGapNewFrame_get_art (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "art" =
      some (endSkimArtValue outUrns) := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "art") =
      some (endSkimArtValue outUrns)
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "art")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterDiffFrame_get_art evm I outIlks outUrns

theorem endSkimAfterGapNewFrame_get_gap_none (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "gap" = none := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "gap") = none
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "gap")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterDiffFrame_get_gap_none evm I outIlks outUrns

theorem endEvalGapNew_skim (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
        (.var "gapNew") =
      .ok (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) := by
  rw [evalExpr?]
  rw [endSkimAfterGapNewFrame_get_gapNew evm I outIlks outUrns]
  rfl

theorem endAssignGapNew_skim (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evm
        .storage (gapRef (.var "ilk"))
        (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) =
      .ok (endSkimAfterGapNewFrame evm I outIlks outUrns,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns)) := by
  rw [assignStorageRef_storage_scalar
    (slot := gapRef (.var "ilk"))
    (er := { base := "gap", steps := [.mindex (endArg0Bytes32Key I)] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (gapSlot (endArg0Bytes32Key I)))
    (n := Int.ofNat (endSkimGapNewWord evm I outIlks outUrns).toNat)
    (hbase := endSkimAfterGapNewFrame_get_gap_none evm I outIlks outUrns)
    (her := by
      exact endEvalStorageRefGap_of_get_ilk
        (endSkimAfterGapNewFrame evm I outIlks outUrns) evm I
        (by
          change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
            (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "ilk") =
              some (endArg0Bytes32Value I)
          rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
            (k := "gapNew") (a := "ilk")
            (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
          exact endSkimAfterDiffFrame_get_ilk evm I outIlks outUrns)
        (by omega))
    (hty := endStorageTypeAt_gap_mindex (endArg0Bytes32Key I))
    (hloc := endConfig_storage_gap (endArg0Bytes32Key I))
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm (gapSlot (endArg0Bytes32Key I))
          (endSkimGapNewWord evm I outIlks outUrns))]

theorem endEvalSkimWadVarAfterGapNew (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
        (.var "wad") =
      .ok (endUIntValue (endSkimWadWord evm I outIlks outUrns)) := by
  rw [evalExpr?]
  rw [endSkimAfterGapNewFrame_get_wad evm I outIlks outUrns]
  rfl

theorem endEvalSkimArtVarAfterGapNew (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
        (.var "art") =
      .ok (endSkimArtValue outUrns) := by
  rw [evalExpr?]
  rw [endSkimAfterGapNewFrame_get_art evm I outIlks outUrns]
  rfl

theorem endEvalSkimWadLimit_true (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hwad : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .le (.var "wad") (.intLit int256Limit)) = .ok (.bool true) := by
  have hle : Int.ofNat (endSkimWadWord evm I outIlks outUrns).toNat ≤ int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hwad
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkimWadVarAfterGapNew evm evmEval I outIlks outUrns]
  simp [evalExpr?, evalBinaryOp?, endUIntValue, EvalResult.bind, bind, pure]
  exact hle

theorem endEvalSkimWadLimit_false (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hwad : endFreeInt256LimitWord.toNat <
        (endSkimWadWord evm I outIlks outUrns).toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .le (.var "wad") (.intLit int256Limit)) = .ok (.bool false) := by
  have hlt : int256Limit < Int.ofNat (endSkimWadWord evm I outIlks outUrns).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hwad
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkimWadVarAfterGapNew evm evmEval I outIlks outUrns]
  simp [evalExpr?, evalBinaryOp?, endUIntValue, EvalResult.bind, bind, pure]
  exact hlt

theorem endEvalSkimArtLimit_true (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .le (.var "art") (.intLit int256Limit)) = .ok (.bool true) := by
  have hle : Int.ofNat (endSkimArtWord outUrns).toNat ≤ int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkimArtVarAfterGapNew evm evmEval I outIlks outUrns]
  simp [evalExpr?, evalBinaryOp?, endSkimArtValue, endSkimArtWord,
    EvalResult.bind, bind, pure]
  exact hle

theorem endEvalSkimArtLimit_false (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hart : endFreeInt256LimitWord.toNat < (endSkimArtWord outUrns).toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .le (.var "art") (.intLit int256Limit)) = .ok (.bool false) := by
  have hlt : int256Limit < Int.ofNat (endSkimArtWord outUrns).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hart
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSkimArtVarAfterGapNew evm evmEval I outIlks outUrns]
  simp [evalExpr?, evalBinaryOp?, endSkimArtValue, endSkimArtWord,
    EvalResult.bind, bind, pure]
  exact hlt

theorem endEvalSkimLimitGuard_true (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hwad : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit))) =
      .ok (.bool true) := by
  rw [evalExpr?]
  rw [endEvalSkimWadLimit_true evm evmEval I outIlks outUrns hwad]
  rw [endEvalSkimArtLimit_true evm evmEval I outIlks outUrns hart]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSkimLimitGuard_wad_false (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hwad : endFreeInt256LimitWord.toNat <
        (endSkimWadWord evm I outIlks outUrns).toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSkimWadLimit_false evm evmEval I outIlks outUrns hwad]
  simp [EvalResult.bind, bind, pure]

theorem endEvalSkimLimitGuard_art_false (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hwad : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat < (endSkimArtWord outUrns).toNat) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit))) =
      .ok (.bool false) := by
  rw [evalExpr?]
  rw [endEvalSkimWadLimit_true evm evmEval I outIlks outUrns hwad]
  rw [endEvalSkimArtLimit_false evm evmEval I outIlks outUrns hart]
  simp [EvalResult.bind, bind, pure]

def endSkimAfterWadSuffixStmts : List Stmt :=
  [ .internalCall "sub" [.var "owe", .var "wad"] "diff",
    .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
    .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
    .require
      (.binary .and
        (.binary .le (.var "wad") (.intLit int256Limit))
        (.binary .le (.var "art") (.intLit int256Limit))) ]

theorem endSkimAfterWadSuffixOk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hsub : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat)
    (hfit : (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat < UInt256.size)
    (hwad : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    ExecBlock config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      endSkimAfterWadSuffixStmts
      (.ok (endSkimAfterGapNewFrame evm I outIlks outUrns)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))) := by
  simp [endSkimAfterWadSuffixStmts]
  exact ExecBlock.consNormal
    (endSkimInternalSubOk evm I outIlks outUrns hsub) <|
    ExecBlock.consNormal
      (endSkimInternalAddOk evm I outIlks outUrns hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign
        (endEvalGapNew_skim evm evm I outIlks outUrns)
        (endAssignGapNew_skim evm I outIlks outUrns hsz68)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (endEvalSkimLimitGuard_true evm
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))
          I outIlks outUrns hwad hart)) <|
    ExecBlock.nil

/-! ### Final `vat.grab` call for `skim(bytes32,address)` -/

abbrev endSkimGrabSelectorWord : UInt256 := endFreeGrabSelectorWord

abbrev endSkimGrabSelectorEncodedWord : UInt256 := endFreeGrabSelectorEncodedWord

theorem endSkimAfterOwe0Frame_get_urn (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOwe0Frame I outIlks outUrns).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "urn")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "urn") = some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "urn") (endSkimArtValue outUrns) (by decide)]
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "urn") = some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "urn") (endSkimInkValue outUrns) (by decide)]
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "urn") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  exact endSkimAfterRateFrame_get_urn I outIlks

theorem endSkimAfterOweFrame_get_urn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterOweFrame evm I outIlks outUrns).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "urn")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOwe0Frame_get_urn I outIlks outUrns

theorem endSkimAfterWadFrame_get_urn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterWadFrame evm I outIlks outUrns).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "urn")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterOweFrame_get_urn evm I outIlks outUrns

theorem endSkimAfterDiffFrame_get_urn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterDiffFrame evm I outIlks outUrns).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "urn")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterWadFrame_get_urn evm I outIlks outUrns

theorem endSkimAfterGapNewFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "ilk") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "ilk")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterDiffFrame_get_ilk evm I outIlks outUrns

theorem endSkimAfterGapNewFrame_get_urn (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "urn" =
      some (endArg1AddressValue I) := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "urn") =
      some (endArg1AddressValue I)
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "urn")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  exact endSkimAfterDiffFrame_get_urn evm I outIlks outUrns

theorem endSkimAfterGapNewFrame_get_vat_none (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "vat" = none := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "vat")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "vat")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "vat")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "vat")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "vat")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "vat") = none
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "vat") (endSkimArtValue outUrns) (by decide)]
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "vat") = none
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "vat") (endSkimInkValue outUrns) (by decide)]
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "vat") = none
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "vat") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  exact endSkimAfterRateFrame_get_vat_none I outIlks

theorem endSkimAfterGapNewFrame_get_vow_none (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimAfterGapNewFrame evm I outIlks outUrns).locals.get? "vow" = none := by
  change (((endSkimAfterDiffFrame evm I outIlks outUrns).locals.insert "gapNew"
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterDiffFrame evm I outIlks outUrns).locals
    (k := "gapNew") (a := "vow")
    (endUIntValue (endSkimGapNewWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterWadFrame evm I outIlks outUrns).locals.insert "diff"
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterWadFrame evm I outIlks outUrns).locals
    (k := "diff") (a := "vow")
    (endUIntValue (endSkimDiffWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOweFrame evm I outIlks outUrns).locals.insert "wad"
    (endUIntValue (endSkimWadWord evm I outIlks outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterOweFrame evm I outIlks outUrns).locals
    (k := "wad") (a := "vow")
    (endUIntValue (endSkimWadWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterOwe0Frame I outIlks outUrns).locals.insert "owe"
    (endUIntValue (endSkimOweWord evm I outIlks outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterOwe0Frame I outIlks outUrns).locals
    (k := "owe") (a := "vow")
    (endUIntValue (endSkimOweWord evm I outIlks outUrns)) (by decide)]
  change (((endSkimAfterArtFrame I outIlks outUrns).locals.insert "owe0"
    (endUIntValue (endSkimOwe0Word outIlks outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterArtFrame I outIlks outUrns).locals
    (k := "owe0") (a := "vow")
    (endUIntValue (endSkimOwe0Word outIlks outUrns)) (by decide)]
  change (((endSkimAfterInkFrame I outIlks outUrns).locals.insert "art"
    (endSkimArtValue outUrns)).get? "vow") = none
  rw [store_get_ne (endSkimAfterInkFrame I outIlks outUrns).locals
    (k := "art") (a := "vow") (endSkimArtValue outUrns) (by decide)]
  change (((endSkimAfterUrnsFrame I outIlks outUrns).locals.insert "ink"
    (endSkimInkValue outUrns)).get? "vow") = none
  rw [store_get_ne (endSkimAfterUrnsFrame I outIlks outUrns).locals
    (k := "ink") (a := "vow") (endSkimInkValue outUrns) (by decide)]
  change (((endSkimAfterRateFrame I outIlks).locals.insert "vatUrn"
    (collapseReturns (endFreeUrnsValues outUrns))).get? "vow") = none
  rw [store_get_ne (endSkimAfterRateFrame I outIlks).locals
    (k := "vatUrn") (a := "vow") (collapseReturns (endFreeUrnsValues outUrns))
    (by decide)]
  change ((((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).insert "rate"
    (endUIntValue (endFlowVatIlksRateWord outIlks))).get? "vow") = none
  rw [store_get_ne ((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))) (k := "rate") (a := "vow")
    (endUIntValue (endFlowVatIlksRateWord outIlks)) (by decide)]
  change (((endSkimStore I).insert "vatIlk"
    (collapseReturns (endFlowVatIlksValues outIlks))).get? "vow") = none
  rw [store_get_ne (endSkimStore I) (k := "vatIlk") (a := "vow")
    (collapseReturns (endFlowVatIlksValues outIlks)) (by decide)]
  exact endSkimStore_get_vow_none I

theorem endEvalSkimIlkVarAfterGapNew (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
        (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endSkimAfterGapNewFrame_get_ilk evm I outIlks outUrns]
  rfl

theorem endEvalSkimUrnVarAfterGapNew (evm evmEval : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame evm I outIlks outUrns) evmEval
        (.var "urn") =
      .ok (endArg1AddressValue I) := by
  rw [evalExpr?]
  rw [endSkimAfterGapNewFrame_get_urn evm I outIlks outUrns]
  rfl

theorem endEvalVatAddress_skimAfterGapNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      vatRef = .ok { base := "vat", steps := [] } := by
    rw [evalStorageRef]
    simp [evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  calc
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (.storage vatRef) =
      .ok (storageLocLoad evm (addrLoc ⟨1⟩)) :=
        evalExpr_storage_scalar
          (hbase := endSkimAfterGapNewFrame_get_vat_none baseEvm I outIlks outUrns)
          (her := her) (hty := hty) (hloc := endConfig_storage_vat)
    _ = .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
        rw [endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVowAddress_skimAfterGapNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      vowRef = .ok { base := "vow", steps := [] } := by
    rw [evalStorageRef]
    simp [evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vow", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  unfold vowAddr
  calc
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (.storage vowRef) =
      .ok (storageLocLoad evm (addrLoc ⟨4⟩)) :=
        evalExpr_storage_scalar
          (hbase := endSkimAfterGapNewFrame_get_vow_none baseEvm I outIlks outUrns)
          (her := her) (hty := hty) (hloc := endConfig_storage_vow)
    _ = .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
        rw [endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_skimAfterGapNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_skimAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_skimAfterGapNew_false (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skimAfterGapNew baseEvm evm I outIlks outUrns, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_skimAfterGapNew_true (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skimAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalSkimNegWadAfterGapNew (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      (.unary .neg (asInt256 (.var "wad"))) =
      .ok (.int (-(Int.ofNat (endSkimWadWord baseEvm I outIlks outUrns).toNat))) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (Expr.cast (.var "wad") int256St)
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endSkimWadWord baseEvm I outIlks outUrns).toNat)))
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← (do
        let value ← evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          (.var "wad")
        EvalResult.ofOption EvalError.typeError (castValue? value int256St))
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endSkimWadWord baseEvm I outIlks outUrns).toNat)))
  rw [endEvalSkimWadVarAfterGapNew baseEvm evm I outIlks outUrns]
  simp [int256St, castValue?, evalUnaryOp?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, endUIntValue]

theorem endEvalSkimNegArtAfterGapNew (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      (.unary .neg (asInt256 (.var "art"))) =
      .ok (.int (-(Int.ofNat (endSkimArtWord outUrns).toNat))) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        (Expr.cast (.var "art") int256St)
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endSkimArtWord outUrns).toNat)))
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← (do
        let value ← evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          (.var "art")
        EvalResult.ofOption EvalError.typeError (castValue? value int256St))
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endSkimArtWord outUrns).toNat)))
  rw [endEvalSkimArtVarAfterGapNew baseEvm evm I outIlks outUrns]
  simp [int256St, castValue?, evalUnaryOp?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, endSkimArtValue, endUIntValue]

theorem endEvalSkimGrabArgs (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    evalExprs? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      [.var "ilk", .var "urn", thisAddr, vowAddr,
        .unary .neg (asInt256 (.var "wad")),
        .unary .neg (asInt256 (.var "art"))] =
    .ok [endArg0Bytes32Value I, endArg1AddressValue I,
      .address evm.executionEnv.codeOwner,
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat),
      .int (-(Int.ofNat (endSkimWadWord baseEvm I outIlks outUrns).toNat)),
      .int (-(Int.ofNat (endSkimArtWord outUrns).toNat))] := by
  rw [evalExprs?]
  rw [endEvalSkimIlkVarAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSkimUrnVarAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  have hthis :
      evalExpr? config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
        thisAddr = .ok (.address evm.executionEnv.codeOwner) := by
    simp [evalExpr?, thisAddr, envValue, pure]
  rw [hthis]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalVowAddress_skimAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSkimNegWadAfterGapNew baseEvm evm I outIlks outUrns]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalSkimNegArtAfterGapNew baseEvm evm I outIlks outUrns]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endEncodeAddress_this_skim (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.codeOwner) =
      some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) := by
  have hownerWord : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by
    rfl
  simp [addr, encodeABIValue?, encodeABIWord?, hownerWord]

theorem endEncodeABIWord_int256_negWord (w : UInt256)
    (hle : w.toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIWord? int256 (.int (-(Int.ofNat w.toNat))) =
      some (UInt256.sub (⟨0⟩ : UInt256) w) := by
  unfold int256 int256Int
  change (if (⟨256, by decide⟩ : BitWidth).val = 0 then none else
      (let positiveLimit := Int.ofNat (EVM.twoPow ((⟨256, by decide⟩ : BitWidth).val - 1))
       if -positiveLimit ≤ -(Int.ofNat w.toNat) ∧
            -(Int.ofNat w.toNat) < positiveLimit then
         some (EVM.wordOfInt (-(Int.ofNat w.toNat)))
       else none)) =
    some (UInt256.sub (⟨0⟩ : UInt256) w)
  rw [if_neg (by decide : ¬ (⟨256, by decide⟩ : BitWidth).val = 0)]
  change (if
      -Int.ofNat (EVM.twoPow 255) ≤ -(Int.ofNat w.toNat) ∧
        -(Int.ofNat w.toNat) < Int.ofNat (EVM.twoPow 255) then
      some (EVM.wordOfInt (-(Int.ofNat w.toNat)))
    else none) =
    some (UInt256.sub (⟨0⟩ : UInt256) w)
  have hrange :
      -Int.ofNat (EVM.twoPow 255) ≤ -(Int.ofNat w.toNat) ∧
        -(Int.ofNat w.toNat) < Int.ofNat (EVM.twoPow 255) := by
    constructor
    · rw [← endFreeInt256LimitWord_toNat]
      exact neg_le_neg (Int.ofNat_le.mpr hle)
    · have hpos : (0 : Int) < Int.ofNat (EVM.twoPow 255) := by
        norm_num [EVM.twoPow]
      exact lt_of_le_of_lt (neg_nonpos.mpr (Int.ofNat_nonneg _)) hpos
  rw [if_pos hrange]
  rw [endWordOfInt_neg_ofNat_toNat]

theorem endEncodeInt256_negWord (w : UInt256)
    (hle : w.toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIValue? int256 (.int (-(Int.ofNat w.toNat))) =
      some (EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) w)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? int256 (.int (-(Int.ofNat w.toNat)))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) w))
  rw [endEncodeABIWord_int256_negWord w hle]
  simp only [bind, Option.bind]

def endSkimGrabPayloadBytes (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : List UInt8 :=
  (((((EVM.Word.toBytesBE (endArg0Word I) ++
      EVM.Word.toBytesBE (endArg1AddressWord I)) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) ++
      EVM.Word.toBytesBE (endPackVowTarget postσ I)) ++
      EVM.Word.toBytesBE
        (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))) ++
      EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns)))

def endSkimGrabEncodedCall (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  grabSelector ++ ⟨(endSkimGrabPayloadBytes preσ postσ I outIlks outUrns).toArray⟩

theorem endEncodeABIValues_grab_skim (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hwad : (endSkimWadWorldWord preσ I outIlks outUrns).toNat ≤
      endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIValues? [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endArg1AddressValue I, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
        .int (-(Int.ofNat (endSkimArtWord outUrns).toNat))] =
      some (endSkimGrabPayloadBytes preσ postσ I outIlks outUrns) := by
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
  rw [endEncodeAddress_arg1_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_this_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow postσ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_negWord (endSkimWadWorldWord preσ I outIlks outUrns) hwad, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_negWord (endSkimArtWord outUrns) hart, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSkimGrabPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_grab_skim (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hwad : (endSkimWadWorldWord preσ I outIlks outUrns).toNat ≤
      endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endArg1AddressValue I, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
        .int (-(Int.ofNat (endSkimArtWord outUrns).toNat))] =
      some (endSkimGrabEncodedCall preσ postσ I outIlks outUrns) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_grab_skim preσ postσ I outIlks outUrns hsz68 hwad hart]
  simp [endSkimGrabEncodedCall, endSkimGrabPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_grab_skim (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hwad : (endSkimWadWorldWord preσ I outIlks outUrns).toNat ≤
      endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
      [endArg0Bytes32Value I, endArg1AddressValue I, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
        .int (-(Int.ofNat (endSkimArtWord outUrns).toNat))] =
      some (endSkimGrabEncodedCall preσ postσ I outIlks outUrns) := by
  rw [endExternalEncode_grab_branch]
  exact endEncodeCallWithSelector_grab_skim preσ postσ I outIlks outUrns hsz68 hwad hart

theorem endSkimTagWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimTagWord evm I = endSkimTagWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (tagSlot (endArg0Bytes32Key I))
  have hslot := endTagSlot_eq I (by omega : 36 ≤ I.calldata.size)
  have h12 : (⟨12⟩ : UInt256) = UInt256.ofNat 12 := by native_decide
  unfold endSkimTagWord endSkimTagWorldWord endSkimTagWorldSlot
  rw [hload, hslot]
  rw [h12]

theorem endSkimOweWord_eq_world_of_callRel {s0 world I evm outIlks outUrns}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimOweWord evm I outIlks outUrns =
      endSkimOweWorldWord world.2 I outIlks outUrns := by
  have htag := endSkimTagWord_eq_world_of_callRel h hsz68
  simp [endSkimOweWord, endSkimOweWorldWord, htag]

theorem endSkimWadWord_eq_world_of_callRel {s0 world I evm outIlks outUrns}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimWadWord evm I outIlks outUrns =
      endSkimWadWorldWord world.2 I outIlks outUrns := by
  have howe :=
    endSkimOweWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) h hsz68
  simp [endSkimWadWord, endSkimWadWorldWord, howe]

theorem endSkimMinTakenCond (ink owe : UInt256) (hle : ink.toNat ≤ owe.toNat) :
    UInt256.isZero (UInt256.gt ink owe) ≠ UInt256.ofNat 0 := by
  have hgt : UInt256.gt ink owe = (⟨0⟩ : UInt256) := ugt_zero hle
  rw [hgt]
  decide

theorem endSkimMinFallthroughCond (ink owe : UInt256) (hlt : owe.toNat < ink.toNat) :
    UInt256.isZero (UInt256.gt ink owe) = UInt256.ofNat 0 := by
  have hgt : UInt256.gt ink owe = (⟨1⟩ : UInt256) := ugt_one hlt
  rw [hgt]
  decide

theorem endX_skim_to_rmul1 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7079⟩
      [endSkimOwe0Word outIlks outUrns, ⟨7099⟩, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimUrnsReturnMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endSkimTagWorldWord world.2 I, endSkimOwe0Word outIlks outUrns,
        ⟨7099⟩, ⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endRuntimeBlocks.endRuntime_block_7079_packed
      (x0 := endSkimOwe0Word outIlks outUrns) (x1 := (⟨7099⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endSkimArtWord outUrns)
      (x4 := endSkimInkWord outUrns) (x5 := endFlowVatIlksRateWord outIlks)
      (x6 := endArg1AddressWord I) (x7 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  have htagSlot :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 12).toByteArray.write 0
            ((endArg0Word I).toByteArray.write 0
              (endSkimUrnsReturnMem I outIlks outUrns)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        endSkimTagWorldSlot I := by
    simpa [endSkimTagWorldSlot, endFlowTagWorldSlot] using
      endFlowTagHashSlot (endSkimUrnsReturnMem I outIlks outUrns) I
  exact ⟨aw10114, k10114, C10114, by
    simpa [endRuntimeBlocks.endRuntime_block_7079_stack,
      endRuntimeBlocks.endRuntime_block_7079_memory, endSkimTagHashMem,
      endSkimTagWorldWord, htagSlot] using rd10114⟩

theorem endX_skim_rmul1_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hfit : (endSkimOwe0Word outIlks outUrns).toNat *
        (endSkimTagWorldWord world.2 I).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7079⟩
      [endSkimOwe0Word outIlks outUrns, ⟨7099⟩, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimUrnsReturnMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7099⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_skim_to_rmul1 (g := g) rd
  obtain ⟨aw7099, k7099, C7099, rd7099⟩ :=
    endX_flow_rmul_ok
      (x := endSkimOwe0Word outIlks outUrns)
      (y := endSkimTagWorldWord world.2 I)
      (ret := (⟨7099⟩ : UInt256))
      (R := [⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      hfit (by jump_dest) (by simp) rd10114
  exact ⟨aw7099, k7099, C7099, by
    simpa [endSkimOweWorldWord] using rd7099⟩

theorem endX_skim_rmul1_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ (endSkimOwe0Word outIlks outUrns).toNat *
        (endSkimTagWorldWord world.2 I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7079⟩
      [endSkimOwe0Word outIlks outUrns, ⟨7099⟩, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimUrnsReturnMem I outIlks outUrns) aw outUrns world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_skim_to_rmul1 (g := g) rd
  exact endX_flow_rmul_fail
    (x := endSkimOwe0Word outIlks outUrns)
    (y := endSkimTagWorldWord world.2 I)
    (ret := (⟨7099⟩ : UInt256))
    (R := [⟨0⟩, endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    hover (by simp) rd10114

theorem endX_skim_to_min {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7099⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10206⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, endSkimInkWord outUrns,
        ⟨7113⟩, ⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10206, k10206, C10206, rd10206⟩ :=
    endRuntimeBlocks.endRuntime_block_7099_packed
      (x0 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x1 := (⟨0⟩ : UInt256)) (x2 := endSkimArtWord outUrns)
      (x3 := endSkimInkWord outUrns)
      (R := [endFlowVatIlksRateWord outIlks, endArg1AddressWord I,
        endArg0Word I, ⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  exact ⟨aw10206, k10206, C10206, by
    simpa [endRuntimeBlocks.endRuntime_block_7099_stack] using rd10206⟩

theorem endX_skim_min_left {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hle : (endSkimInkWord outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7099⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimInkWord outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10206, k10206, C10206, rd10206⟩ := endX_skim_to_min (g := g) rd
  have hcond := endSkimMinTakenCond
    (endSkimInkWord outUrns) (endSkimOweWorldWord world.2 I outIlks outUrns) hle
  obtain ⟨aw10222, k10222, C10222, rd10222⟩ :=
    endRuntimeBlocks.endRuntime_block_10206_taken_packed
      (x0 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimInkWord outUrns)
      (R := [⟨7113⟩, ⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd10206
  obtain ⟨aw10224, k10224, C10224, rd10224⟩ :=
    endRuntimeBlocks.endRuntime_block_10222_packed
      (x0 := (⟨0⟩ : UInt256))
      (x1 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimInkWord outUrns)
      (R := [⟨7113⟩, ⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp)
      (by simpa [endRuntimeBlocks.endRuntime_block_10206_taken_stack] using rd10222)
  obtain ⟨aw7113, k7113, C7113, rd7113⟩ :=
    endRuntimeBlocks.endRuntime_block_10224_packed
      (x0 := endSkimInkWord outUrns) (x1 := (⟨0⟩ : UInt256))
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimInkWord outUrns) (x4 := (⟨7113⟩ : UInt256))
      (R := [⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10222_stack] using rd10224)
  exact ⟨aw7113, k7113, C7113, by
    simpa [endRuntimeBlocks.endRuntime_block_10224_stack] using rd7113⟩

theorem endX_skim_min_right {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hlt : (endSkimOweWorldWord world.2 I outIlks outUrns).toNat <
        (endSkimInkWord outUrns).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7099⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimOweWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10206, k10206, C10206, rd10206⟩ := endX_skim_to_min (g := g) rd
  have hcond := endSkimMinFallthroughCond
    (endSkimInkWord outUrns) (endSkimOweWorldWord world.2 I outIlks outUrns) hlt
  obtain ⟨aw10217, k10217, C10217, rd10217⟩ :=
    endRuntimeBlocks.endRuntime_block_10206_fallthrough_packed
      (x0 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimInkWord outUrns)
      (R := [⟨7113⟩, ⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hcond rd10206
  obtain ⟨aw10224, k10224, C10224, rd10224⟩ :=
    endRuntimeBlocks.endRuntime_block_10217_packed
      (x0 := (⟨0⟩ : UInt256))
      (x1 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (R := [endSkimInkWord outUrns, ⟨7113⟩, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns, endSkimArtWord outUrns,
        endSkimInkWord outUrns, endFlowVatIlksRateWord outIlks,
        endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10206_fallthrough_stack] using rd10217)
  obtain ⟨aw7113, k7113, C7113, rd7113⟩ :=
    endRuntimeBlocks.endRuntime_block_10224_packed
      (x0 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x1 := (⟨0⟩ : UInt256))
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimInkWord outUrns) (x4 := (⟨7113⟩ : UInt256))
      (R := [⟨0⟩, endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10217_stack] using rd10224)
  exact ⟨aw7113, k7113, C7113, by
    simpa [endRuntimeBlocks.endRuntime_block_10224_stack] using rd7113⟩

abbrev endSkimGapHashMem (I : ExecutionEnv) (outIlks outUrns : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_7113_memory
    (mem := endSkimTagHashMem I outIlks outUrns) (x7 := endArg0Word I)

abbrev endSkimAfterGapStoreMem (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_7150_fallthrough_memory
    (mem := endSkimGapHashMem I outIlks outUrns) (x7 := endArg0Word I)

theorem wordAt0Mem_size_of_ge32 (word : UInt256) {mem : ByteArray}
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 mem.size mem.size rfl
    (by omega) (by omega)

theorem twoWordHashMem_size_of_ge64 (key slot : UInt256) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32 mem.size mem.size
    (wordAt0Mem_size_of_ge32 key (by omega))
    (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)
    (by omega)

theorem twoWordHashMem_read64_of_ge96 (key slot : UInt256) {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)
      (by omega)
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]
  exact hread64

theorem endSkimUrnsReturnMem_read64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimUrnsReturnMem I outIlks outUrns).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hfacts := callOutputFacts (endSkimUrnsCallMem I outIlks) outUrns (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) houtUrns (by
      change 128 + 64 ≤ (endSkimUrnsCallMem I outIlks).size
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega)
  have hread :
      (endSkimUrnsReturnMem I outIlks outUrns).readWithPadding 64 32 =
        (endSkimUrnsCallMem I outIlks).readWithPadding 64 32 := by
    simpa [endSkimUrnsReturnMem] using hfacts.readBelow 64 (by native_decide)
  rw [hread]
  exact endSkimUrnsCallMem_read64 I outIlks houtIlks h160

theorem endSkimTagHashMem_size (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimTagHashMem I outIlks outUrns).size =
      (endSkimUrnsReturnMem I outIlks outUrns).size := by
  have hbase : 64 ≤ (endSkimUrnsReturnMem I outIlks outUrns).size := by
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  simpa [endSkimTagHashMem, endRuntimeBlocks.endRuntime_block_7079_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 12) hbase

theorem endSkimTagHashMem_read64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimTagHashMem I outIlks outUrns).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hbase : 96 ≤ (endSkimUrnsReturnMem I outIlks outUrns).size := by
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  have hread := endSkimUrnsReturnMem_read64 I outIlks outUrns houtIlks h160 houtUrns
  simpa [endSkimTagHashMem, endRuntimeBlocks.endRuntime_block_7079_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 12) hbase hread

theorem endSkimGapHashMem_size (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGapHashMem I outIlks outUrns).size =
      (endSkimTagHashMem I outIlks outUrns).size := by
  have htag : 64 ≤ (endSkimTagHashMem I outIlks outUrns).size := by
    rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  simpa [endSkimGapHashMem, endRuntimeBlocks.endRuntime_block_7113_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 13) htag

theorem endSkimGapHashMem_read64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGapHashMem I outIlks outUrns).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have htag : 96 ≤ (endSkimTagHashMem I outIlks outUrns).size := by
    rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  have hread := endSkimTagHashMem_read64 I outIlks outUrns houtIlks h160 houtUrns
  simpa [endSkimGapHashMem, endRuntimeBlocks.endRuntime_block_7113_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 13) htag hread

theorem endSkimAfterGapStoreMem_size (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimAfterGapStoreMem I outIlks outUrns).size =
      (endSkimGapHashMem I outIlks outUrns).size := by
  have hgap : 64 ≤ (endSkimGapHashMem I outIlks outUrns).size := by
    rw [endSkimGapHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  simpa [endSkimAfterGapStoreMem, endRuntimeBlocks.endRuntime_block_7150_fallthrough_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 13) hgap

theorem endSkimAfterGapStoreMem_read64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimAfterGapStoreMem I outIlks outUrns).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hgap : 96 ≤ (endSkimGapHashMem I outIlks outUrns).size := by
    rw [endSkimGapHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
    rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
    have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
    omega
  have hread := endSkimGapHashMem_read64 I outIlks outUrns houtIlks h160 houtUrns
  simpa [endSkimAfterGapStoreMem, endRuntimeBlocks.endRuntime_block_7150_fallthrough_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 13) hgap hread

theorem endSkimAfterGapStoreMem_mload64 (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endSkimAfterGapStoreMem I outIlks outUrns) = ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥
        (endSkimAfterGapStoreMem I outIlks outUrns).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkimAfterGapStoreMem I outIlks outUrns).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endSkimAfterGapStoreMem I outIlks outUrns)
    (by
      rw [endSkimAfterGapStoreMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimGapHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega)
    (endSkimAfterGapStoreMem_read64 I outIlks outUrns houtIlks h160 houtUrns)

abbrev endSkimGrabMemSel (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    ByteArray :=
  endSkimGrabSelectorEncodedWord.toByteArray.write 0
    (endSkimAfterGapStoreMem I outIlks outUrns) 128 32

abbrev endSkimGrabMemIlk (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endSkimGrabMemSel I outIlks outUrns) 132 32

abbrev endSkimGrabMemUrn (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    ByteArray :=
  (endArg1AddressWord I).toByteArray.write 0 (endSkimGrabMemIlk I outIlks outUrns)
    164 32

abbrev endSkimGrabMemThis (I : ExecutionEnv) (outIlks outUrns : ByteArray) :
    ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (endSkimGrabMemUrn I outIlks outUrns) 196 32

abbrev endSkimGrabMemVow (postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  (endPackVowTarget postσ I).toByteArray.write 0
    (endSkimGrabMemThis I outIlks outUrns) 228 32

abbrev endSkimGrabMemWad (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns)).toByteArray.write
    0 (endSkimGrabMemVow postσ I outIlks outUrns) 260 32

abbrev endSkimGrabMemFull (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns)).toByteArray.write 0
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 32

abbrev endSkimGrabCallMem (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_7253_memory
    (ee := I) (mem := endSkimAfterGapStoreMem I outIlks outUrns) (σ := postσ)
    (x0 := endSkimWadWorldWord preσ I outIlks outUrns)
    (x2 := endSkimArtWord outUrns)
    (x5 := endArg1AddressWord I) (x6 := endArg0Word I)

theorem endSkimGrabCallMem_eq_full (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    endSkimGrabCallMem preσ postσ I outIlks outUrns =
      endSkimGrabMemFull preσ postσ I outIlks outUrns := by
  have hfreeCall := endSkimAfterGapStoreMem_mload64 I outIlks outUrns
    houtIlks h160 houtUrns
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcleanUrn :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (endArg1AddressWord I) =
        endArg1AddressWord I := by
    rw [hmaskGenerated]
    exact solcAddrMask_clean_left (endArg1AddressWord_canonical I)
  have hvow :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner postσ (UInt256.ofNat 4)) =
        endPackVowTarget postσ I := by
    unfold endPackVowTarget
    rw [hmaskGenerated]
  unfold endSkimGrabCallMem endSkimGrabMemFull endSkimGrabMemWad endSkimGrabMemVow
    endSkimGrabMemThis endSkimGrabMemUrn endSkimGrabMemIlk endSkimGrabMemSel
    endSkimGrabSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_7253_memory]
  rw [hfreeCall, hcleanUrn, hvow]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
  rw [endFreeGrabSelectorEncodedWord_generated]
  rfl

theorem endSkimGrabMemSel_size_ge160 (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    160 ≤ (endSkimGrabMemSel I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded endSkimGrabSelectorEncodedWord
    (endSkimAfterGapStoreMem I outIlks outUrns) 128

theorem endSkimGrabMemIlk_size_ge164 (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    164 ≤ (endSkimGrabMemIlk I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endSkimGrabMemSel I outIlks outUrns) 132

theorem endSkimGrabMemUrn_size_ge196 (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    196 ≤ (endSkimGrabMemUrn I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endArg1AddressWord I)
    (endSkimGrabMemIlk I outIlks outUrns) 164

theorem endSkimGrabMemThis_size_ge228 (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    228 ≤ (endSkimGrabMemThis I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkimGrabMemUrn I outIlks outUrns) 196

theorem endSkimGrabMemVow_size_ge260 (postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    260 ≤ (endSkimGrabMemVow postσ I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228

theorem endSkimGrabMemWad_size_ge292 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    292 ≤ (endSkimGrabMemWad preσ postσ I outIlks outUrns).size :=
  toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260

theorem endSkimGrabCallMem_size_ge324 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    324 ≤ (endSkimGrabCallMem preσ postσ I outIlks outUrns).size := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292

theorem endSkimGrabCallMem_read64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 64
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260 64
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228 64
    (by have := endSkimGrabMemThis_size_ge228 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkimGrabMemUrn I outIlks outUrns) 196 64
    (by have := endSkimGrabMemUrn_size_ge196 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg1AddressWord I)
    (endSkimGrabMemIlk I outIlks outUrns) 164 64
    (by have := endSkimGrabMemIlk_size_ge164 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg0Word I)
    (endSkimGrabMemSel I outIlks outUrns) 132 64
    (by have := endSkimGrabMemSel_size_ge160 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSkimGrabSelectorEncodedWord
    (endSkimAfterGapStoreMem I outIlks outUrns) 128 64
    (by
      rw [endSkimAfterGapStoreMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimGapHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimTagHashMem_size I outIlks outUrns houtIlks h160 houtUrns]
      rw [endSkimUrnsReturnMem_size I outIlks outUrns houtIlks h160 houtUrns]
      have hsize := endSkimUrnsCallMem_size_ge196 I outIlks houtIlks h160
      omega) (by omega)]
  exact endSkimAfterGapStoreMem_read64 I outIlks outUrns houtIlks h160 houtUrns

theorem endSkimGrabCallMem_mload64 (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endSkimGrabCallMem preσ postσ I outIlks outUrns) =
      ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥
        (endSkimGrabCallMem preσ postσ I outIlks outUrns).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endSkimGrabCallMem preσ postσ I outIlks outUrns)
    (by
      have hge := endSkimGrabCallMem_size_ge324 preσ postσ I outIlks outUrns
        houtIlks h160 houtUrns
      change 64 < (endSkimGrabCallMem preσ postσ I outIlks outUrns).size
      omega)
    (endSkimGrabCallMem_read64 preσ postσ I outIlks outUrns houtIlks h160 houtUrns)

theorem endSkimGrabCallMem_readSelector (preσ postσ : AccountMap)
    (I : ExecutionEnv) (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 128 4 =
      grabSelector := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [write32_read_below_len _ _ 292 128 4 (by rw [toByteArray_size])
    (endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns) (by omega)
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size])
    (endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns) (by omega)
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (endSkimGrabMemThis_size_ge228 I outIlks outUrns) (by omega)
    (by have := endSkimGrabMemThis_size_ge228 I outIlks outUrns; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endSkimGrabMemUrn_size_ge196 I outIlks outUrns) (by omega)
    (by have := endSkimGrabMemUrn_size_ge196 I outIlks outUrns; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endSkimGrabMemIlk_size_ge164 I outIlks outUrns) (by omega)
    (by have := endSkimGrabMemIlk_size_ge164 I outIlks outUrns; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endSkimGrabMemSel_size_ge160 I outIlks outUrns; omega) (by omega)
    (by have := endSkimGrabMemSel_size_ge160 I outIlks outUrns; omega)
    (by decide) (by decide)]
  change ((endSkimGrabSelectorEncodedWord.toByteArray.write 0
      (endSkimAfterGapStoreMem I outIlks outUrns) 128 32).readWithPadding 128 4) =
    grabSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkimGrabSelectorEncodedWord (endSkimAfterGapStoreMem I outIlks outUrns) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFreeGrabSelectorEncodedWord_prefix]

theorem endSkimGrabCallMem_readIlk (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 132
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260 132
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228 132
    (by have := endSkimGrabMemThis_size_ge228 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkimGrabMemUrn I outIlks outUrns) 196 132
    (by have := endSkimGrabMemUrn_size_ge196 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg1AddressWord I)
    (endSkimGrabMemIlk I outIlks outUrns) 164 132
    (by have := endSkimGrabMemIlk_size_ge164 I outIlks outUrns; omega) (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      (endSkimGrabMemSel I outIlks outUrns) 132 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I)
    (endSkimGrabMemSel I outIlks outUrns) 132

theorem endSkimGrabCallMem_readUrn (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 164 32 =
      (endArg1AddressWord I).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 164
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260 164
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228 164
    (by have := endSkimGrabMemThis_size_ge228 I outIlks outUrns; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkimGrabMemUrn I outIlks outUrns) 196 164
    (by have := endSkimGrabMemUrn_size_ge196 I outIlks outUrns; omega) (by omega)]
  change (((endArg1AddressWord I).toByteArray.write 0
      (endSkimGrabMemIlk I outIlks outUrns) 164 32).readWithPadding 164 32) =
    (endArg1AddressWord I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg1AddressWord I)
    (endSkimGrabMemIlk I outIlks outUrns) 164

theorem endSkimGrabCallMem_readThis (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 196 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 196
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260 196
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228 196
    (by have := endSkimGrabMemThis_size_ge228 I outIlks outUrns; omega) (by omega)]
  change (((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (endSkimGrabMemUrn I outIlks outUrns) 196 32).readWithPadding 196 32) =
    (UInt256.ofNat I.codeOwner.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkimGrabMemUrn I outIlks outUrns) 196

theorem endSkimGrabCallMem_readVow (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 228 32 =
      (endPackVowTarget postσ I).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 228
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260 228
    (by have := endSkimGrabMemVow_size_ge260 postσ I outIlks outUrns; omega)
    (by omega)]
  change (((endPackVowTarget postσ I).toByteArray.write 0
      (endSkimGrabMemThis I outIlks outUrns) 228 32).readWithPadding 228 32) =
    (endPackVowTarget postσ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkimGrabMemThis I outIlks outUrns) 228

theorem endSkimGrabCallMem_readWad (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 260 32 =
      (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns)).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 260
    (by have := endSkimGrabMemWad_size_ge292 preσ postσ I outIlks outUrns; omega)
    (by omega)]
  change (((UInt256.sub (⟨0⟩ : UInt256)
        (endSkimWadWorldWord preσ I outIlks outUrns)).toByteArray.write 0
      (endSkimGrabMemVow postσ I outIlks outUrns) 260 32).readWithPadding 260 32) =
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns)).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimWadWorldWord preσ I outIlks outUrns))
    (endSkimGrabMemVow postσ I outIlks outUrns) 260

theorem endSkimGrabCallMem_readArt (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 292 32 =
      (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns)).toByteArray := by
  rw [endSkimGrabCallMem_eq_full preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns]
  change (((UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns)).toByteArray.write 0
      (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292 32).readWithPadding 292 32) =
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns)).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endSkimArtWord outUrns))
    (endSkimGrabMemWad preσ postσ I outIlks outUrns) 292

theorem endSkimGrabCallMem_readCallData (preσ postσ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    (endSkimGrabCallMem preσ postσ I outIlks outUrns).readWithPadding 128 196 =
      endSkimGrabEncodedCall preσ postσ I outIlks outUrns := by
  have hsize := endSkimGrabCallMem_size_ge324 preσ postσ I outIlks outUrns
    houtIlks h160 houtUrns
  rw [show 196 = 4 + 192 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 128 4 192
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 192 = 32 + 160 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 132 32 160
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 160 = 32 + 128 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 164 32 128
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [show 128 = 32 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 196 32 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 196 + 32 = 228 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 228 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 228 + 32 = 260 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkimGrabCallMem preσ postσ I outIlks outUrns) 260 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 260 + 32 = 292 by norm_num]
  rw [endSkimGrabCallMem_readSelector preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readIlk preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readUrn preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readThis preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readVow preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readWad preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns,
    endSkimGrabCallMem_readArt preσ postσ I outIlks outUrns
      houtIlks h160 houtUrns]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSkimGrabEncodedCall, endSkimGrabPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endSkimGrabCallRest (preσ postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outIlks outUrns : ByteArray) : List UInt256 :=
  [⟨324⟩, endSkimGrabSelectorWord, endPackVatTarget postσ I,
    endSkimWadWorldWord preσ I outIlks outUrns,
    endSkimOweWorldWord preσ I outIlks outUrns,
    endSkimArtWord outUrns, endSkimInkWord outUrns,
    endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
    ⟨562⟩, sel]

abbrev endSkimGrabCallStack (preσ postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outIlks outUrns : ByteArray) : List UInt256 :=
  [endPackVatTarget postσ I, ⟨0⟩, ⟨128⟩, ⟨196⟩, ⟨128⟩, ⟨0⟩] ++
    endSkimGrabCallRest preσ postσ I sel outIlks outUrns

abbrev endSkimGrabCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (outIlks outUrns : ByteArray) : Cursor :=
  { pc := ⟨7371⟩, stack := endSkimGrabCallStack preσ world.2 I sel outIlks outUrns,
    mem := endSkimGrabCallMem preσ world.2 I outIlks outUrns, aw := aw,
    rdata := outUrns, world := world }

abbrev endSkimGrabCallAw (aw : UInt256) : UInt256 :=
  endFreeGrabCallAw aw

theorem endX_skim_to_grab_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {preσ : AccountMap} {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      [endSkimWadWorldWord preσ I outIlks outUrns,
        endSkimOweWorldWord preσ I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimAfterGapStoreMem I outIlks outUrns) aw outUrns world k C) :
    ∃ awNext kNext CNext, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7371⟩
      (endSkimGrabCallStack preσ world.2 I sel outIlks outUrns)
      (endSkimGrabCallMem preσ world.2 I outIlks outUrns) awNext outUrns
      world kNext CNext := by
  obtain ⟨aw7334, k7334, C7334, rd7334⟩ :=
    endRuntimeBlocks.endRuntime_block_7253_packed
      (x0 := endSkimWadWorldWord preσ I outIlks outUrns)
      (x1 := endSkimOweWorldWord preσ I outIlks outUrns)
      (x2 := endSkimArtWord outUrns) (x3 := endSkimInkWord outUrns)
      (x4 := endFlowVatIlksRateWord outIlks) (x5 := endArg1AddressWord I)
      (x6 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) rd
  have hpreMload := endSkimAfterGapStoreMem_mload64 I outIlks outUrns
    houtIlks h160 houtUrns
  have hcallMload := endSkimGrabCallMem_mload64 preσ world.2 I outIlks outUrns
    houtIlks h160 houtUrns
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
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    rw [htarget]
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw7369, k7369, C7369, rd7369⟩ :=
    endRuntimeBlocks.endRuntime_block_7334_taken_packed
      (x0 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x1 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))
      (x2 := memLoad (UInt256.ofNat 64)
        (endSkimGrabCallMem preσ world.2 I outIlks outUrns))
      (x3 := memLoad (UInt256.ofNat 64)
        (endSkimAfterGapStoreMem I outIlks outUrns))
      (x4 := (⟨0⟩ : UInt256))
      (R := [endSkimWadWorldWord preσ I outIlks outUrns,
        endSkimOweWorldWord preσ I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_7253_stack, endSkimGrabCallMem]
          using rd7334)
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 196 =
      ⟨196⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 196 = ⟨324⟩ := by
    native_decide
  have hstack7369 :
      endRuntimeBlocks.endRuntime_block_7334_taken_stack (σ := world.2)
          (x0 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
          (x1 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (x2 := memLoad (UInt256.ofNat 64)
            (endSkimGrabCallMem preσ world.2 I outIlks outUrns))
          (x3 := memLoad (UInt256.ofNat 64)
            (endSkimAfterGapStoreMem I outIlks outUrns))
          (x4 := (⟨0⟩ : UInt256))
          (R := [endSkimWadWorldWord preσ I outIlks outUrns,
            endSkimOweWorldWord preσ I outIlks outUrns,
            endSkimArtWord outUrns, endSkimInkWord outUrns,
            endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
            ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkimGrabCallStack preσ world.2 I sel outIlks outUrns := by
    dsimp [endRuntimeBlocks.endRuntime_block_7334_taken_stack,
      endSkimGrabCallStack, endSkimGrabCallRest]
    rw [htarget, hcallMload, hpreMload, hlen, hend]
  have rd7369Ok :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7369⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkimGrabCallStack preσ world.2 I sel outIlks outUrns)
        (endSkimGrabCallMem preσ world.2 I outIlks outUrns) aw7369 outUrns
        world k7369 C7369 := by
    simpa [hstack7369] using rd7369
  obtain ⟨aw7371, k7371, C7371, rd7371⟩ :=
    endRuntimeBlocks.endRuntime_block_7369_packed
      (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
      (R := endSkimGrabCallStack preσ world.2 I sel outIlks outUrns)
      (by simp [endSkimGrabCallStack, endSkimGrabCallRest]) rd7369Ok
  exact ⟨aw7371, k7371, C7371, by
    simpa [endRuntimeBlocks.endRuntime_block_7369_stack] using rd7371⟩

theorem endSkimGrabExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C baseEvm evm}
    {preσ : AccountMap} {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size)
    (hwadEq :
      endSkimWadWord baseEvm I outIlks outUrns =
        endSkimWadWorldWord preσ I outIlks outUrns)
    (hwad : (endSkimWadWorldWord preσ I outIlks outUrns).toNat ≤
      endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkimGrabCallCursor world preσ I sel aw outIlks outUrns)
      k C (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
            .unary .neg (asInt256 (.var "wad")),
            .unary .neg (asInt256 (.var "art"))] "_grab" ]
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨7371⟩ = some (.GAS, .none); decide)
    (by simp [endSkimGrabCallCursor, endSkimGrabCallStack, endSkimGrabCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I, endArg1AddressValue I, .address I.codeOwner,
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
      .int (-(Int.ofNat (endSkimArtWord outUrns).toNat))])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨7372⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkimGrabCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skimAfterGapNew baseEvm evm I outIlks outUrns]
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
    rw [endEvalSkimGrabArgs baseEvm evm I outIlks outUrns]
    rw [h.env, hwadEq]
    change EvalResult.ok
      [endArg0Bytes32Value I, endArg1AddressValue I, Value.address I.codeOwner,
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        Value.int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
        Value.int (-(Int.ofNat (endSkimArtWord outUrns).toNat))] =
      EvalResult.ok
        [endArg0Bytes32Value I, endArg1AddressValue I, Value.address I.codeOwner,
          Value.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          Value.int (-(Int.ofNat (endSkimWadWorldWord preσ I outIlks outUrns).toNat)),
          Value.int (-(Int.ofNat (endSkimArtWord outUrns).toNat))]
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
    rw [endExternalEncode_grab_skim preσ world.2 I outIlks outUrns hsz68 hwad hart]
    change some (endSkimGrabEncodedCall preσ world.2 I outIlks outUrns) =
      some ((endSkimGrabCallMem preσ world.2 I outIlks outUrns).readWithPadding 128 196)
    rw [endSkimGrabCallMem_readCallData preσ world.2 I outIlks outUrns
      houtIlks h160 houtUrns]
  · intro out evmNext worldNext kNext CNext
    dsimp only
    intro _ _
    rw [endExternalDecode_grab out]
    intro rd hrel
    have rd7373 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
          ((⟨1⟩ : UInt256) :: endSkimGrabCallRest preσ world.2 I sel outIlks outUrns)
          (endSkimGrabCallMem preσ world.2 I outIlks outUrns)
          (endSkimGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkimGrabCallCursor,
        endSkimGrabCallStack, endSkimGrabCallRest, endSkimGrabCallAw] using rd
    have rd7389 := endRuntimeBlocks.endRuntime_block_7373_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endSkimGrabCallRest preσ world.2 I sel outIlks outUrns)
      (by simp [endSkimGrabCallRest]) (by native_decide) (by jump_dest) rd7373
    have rd562 := endRuntimeBlocks.endRuntime_block_7389
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨324⟩ : UInt256))
      (x2 := endSkimGrabSelectorWord) (x3 := endPackVatTarget world.2 I)
      (x4 := endSkimWadWorldWord preσ I outIlks outUrns)
      (x5 := endSkimOweWorldWord preσ I outIlks outUrns)
      (x6 := endSkimArtWord outUrns) (x7 := endSkimInkWord outUrns)
      (x8 := endFlowVatIlksRateWord outIlks) (x9 := endArg1AddressWord I)
      (x10 := endArg0Word I) (x11 := (⟨562⟩ : UInt256)) (R := [sel])
      (by simp) hperm (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_7373_taken_stack,
          endSkimGrabCallRest] using rd7389)
    have rdret := endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp) rd562
    exact BlockProgress.ofRDret ExecBlock.nil rdret
      (by simpa using hrel.created.symm)
      (by simpa using hrel.accounts)
      abiVoidFallthrough
  · intro out worldNext kNext CNext
    dsimp only
    intro rd
    have rd7373 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7373⟩
          ((⟨0⟩ : UInt256) :: endSkimGrabCallRest preσ world.2 I sel outIlks outUrns)
          (endSkimGrabCallMem preσ world.2 I outIlks outUrns)
          (endSkimGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkimGrabCallCursor,
        endSkimGrabCallStack, endSkimGrabCallRest, endSkimGrabCallAw] using rd
    have rd7380 := endRuntimeBlocks.endRuntime_block_7373_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endSkimGrabCallRest preσ world.2 I sel outIlks outUrns)
      (by simp [endSkimGrabCallRest]) (by native_decide) rd7373
    exact endRuntimeBlocks.endRuntime_block_7380
      (R := endRuntimeBlocks.endRuntime_block_7373_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endSkimGrabCallRest preσ world.2 I sel outIlks outUrns))
      (by simp [endRuntimeBlocks.endRuntime_block_7373_fallthrough_stack,
        endSkimGrabCallRest])
      rd7380

theorem endSkimGapHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 13).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endSkimGapWorldSlot I := by
  simpa [endSkimGapWorldSlot, endFlowGapWorldSlot] using
    endFlowGapHashSlot mem I

theorem endSkimGapHashSlot_generated (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0)
        ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (UInt256.ofNat 0)))
        ((UInt256.ofNat 13).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          ((UInt256.ofNat 32) + (UInt256.ofNat 0)).toNat 32)
      = endSkimGapWorldSlot I := by
  simpa [endSkimGapWorldSlot, endFlowGapWorldSlot] using
    endFlowGapHashSlot_generated mem I

theorem endSkimLimitGtNonzero (w : UInt256)
    (hgt : endFreeInt256LimitWord.toNat < w.toNat) :
    UInt256.gt w (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) ≠
      UInt256.ofNat 0 := by
  change UInt256.gt w endFreeInt256LimitWord ≠ UInt256.ofNat 0
  rw [Reasoning.Theory.ugt_one hgt]
  decide

theorem endSkimLimitGtZero (w : UInt256)
    (hle : w.toNat ≤ endFreeInt256LimitWord.toNat) :
    UInt256.gt w (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) =
      UInt256.ofNat 0 := by
  change UInt256.gt w endFreeInt256LimitWord = UInt256.ofNat 0
  exact Reasoning.Theory.ugt_zero hle

theorem endSkimLimitFlagPass (w : UInt256)
    (hle : w.toNat ≤ endFreeInt256LimitWord.toNat) :
    UInt256.isZero
        (UInt256.gt w (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) ≠
      UInt256.ofNat 0 := by
  rw [endSkimLimitGtZero w hle]
  decide

theorem endSkimLimitFlagFail (w : UInt256)
    (hgt : endFreeInt256LimitWord.toNat < w.toNat) :
    UInt256.isZero
        (UInt256.gt w (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) =
      UInt256.ofNat 0 := by
  change UInt256.isZero (UInt256.gt w endFreeInt256LimitWord) = UInt256.ofNat 0
  rw [Reasoning.Theory.ugt_one hgt]
  decide

theorem endX_skim_after_min_to_guard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hsub : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (hfit : (endSkimGapWorldWord world.2 I).toNat +
        (endSkimDiffWorldWord world.2 I outIlks outUrns).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7150⟩
      [endSkimGapNewWorldWord world.2 I outIlks outUrns,
        endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimGapHashMem I outIlks outUrns) aw' outUrns world k' C' := by
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_7113_packed
      (x0 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x1 := (⟨0⟩ : UInt256))
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns) (x4 := endSkimInkWord outUrns)
      (x5 := endFlowVatIlksRateWord outIlks) (x6 := endArg1AddressWord I)
      (x7 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  have hgapSlot := endSkimGapHashSlot (endSkimTagHashMem I outIlks outUrns) I
  have rd10154' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
        [endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns, ⟨7145⟩,
          endSkimGapWorldWord world.2 I, ⟨7150⟩,
          endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimGapHashMem I outIlks outUrns) aw10154 outUrns world k10154 C10154 := by
    simpa [endRuntimeBlocks.endRuntime_block_7113_stack,
      endSkimGapHashMem, endSkimGapWorldWord, hgapSlot] using rd10154
  obtain ⟨aw7145, k7145, C7145, rd7145⟩ :=
    endX_flow_sub_ok
      (x := endSkimOweWorldWord world.2 I outIlks outUrns)
      (y := endSkimWadWorldWord world.2 I outIlks outUrns)
      (ret := (⟨7145⟩ : UInt256))
      (R := [endSkimGapWorldWord world.2 I, ⟨7150⟩,
        endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      hsub (by jump_dest) (by simp) rd10154'
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_7145_packed
      (R := [endSkimDiffWorldWord world.2 I outIlks outUrns,
        endSkimGapWorldWord world.2 I, ⟨7150⟩,
        endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endSkimDiffWorldWord, endGenericSubResult] using rd7145)
  have hcond := endPackAddSuccessCond
    (endSkimDiffWorldWord world.2 I outIlks outUrns)
    (endSkimGapWorldWord world.2 I) hfit
  have rd10108 := endRuntimeBlocks.endRuntime_block_10092_taken
    (x0 := endSkimDiffWorldWord world.2 I outIlks outUrns)
    (x1 := endSkimGapWorldWord world.2 I)
    (R := [⟨7150⟩, endSkimWadWorldWord world.2 I outIlks outUrns,
      endSkimOweWorldWord world.2 I outIlks outUrns,
      endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    (by simp) hcond (by jump_dest) rd10092
  obtain ⟨aw7150, k7150, C7150, rd7150⟩ :=
    endRuntimeBlocks.endRuntime_block_10108_packed
      (x0 := endSkimDiffWorldWord world.2 I outIlks outUrns +
        endSkimGapWorldWord world.2 I)
      (x1 := endSkimDiffWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimGapWorldWord world.2 I)
      (x3 := (⟨7150⟩ : UInt256))
      (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10092_taken_stack] using rd10108)
  have hsum :
      endSkimDiffWorldWord world.2 I outIlks outUrns + endSkimGapWorldWord world.2 I =
        endSkimGapNewWorldWord world.2 I outIlks outUrns := by
    simp [endSkimGapNewWorldWord, u256_add_comm]
  exact ⟨aw7150, k7150, C7150, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack, hsum] using rd7150⟩

theorem endX_skim_after_min_wad_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hsub : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (hfit : (endSkimGapWorldWord world.2 I).toNat +
        (endSkimDiffWorldWord world.2 I outIlks outUrns).toNat < UInt256.size)
    (hwad : endFreeInt256LimitWord.toNat <
        (endSkimWadWorldWord world.2 I outIlks outUrns).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw7150, k7150, C7150, rd7150⟩ :=
    endX_skim_after_min_to_guard (g := g) hsub hfit rd
  have hcond := endSkimLimitGtNonzero
    (endSkimWadWorldWord world.2 I outIlks outUrns) hwad
  obtain ⟨aw7189, k7189, C7189, rd7189⟩ :=
    endRuntimeBlocks.endRuntime_block_7150_taken_packed
      (x0 := endSkimGapNewWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns) (x4 := endSkimInkWord outUrns)
      (x5 := endFlowVatIlksRateWord outIlks) (x6 := endArg1AddressWord I)
      (x7 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hperm hcond (by jump_dest) rd7150
  have hgapSlot := endSkimGapHashSlot (endSkimGapHashMem I outIlks outUrns) I
  have rd7189' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7189⟩
        [UInt256.isZero (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))),
          endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimAfterGapStoreMem I outIlks outUrns) aw7189 outUrns
        (endSkimGapStoredWorld world I outIlks outUrns) k7189 C7189 := by
    simpa [endSkimAfterGapStoreMem, endSkimGapStoredWorld,
      endRuntimeBlocks.endRuntime_block_7150_taken_stack,
      endRuntimeBlocks.endRuntime_block_7150_taken_memory, hgapSlot] using rd7189
  have hflag := endSkimLimitFlagFail
    (endSkimWadWorldWord world.2 I outIlks outUrns) hwad
  obtain ⟨aw7194, k7194, C7194, rd7194⟩ :=
    endRuntimeBlocks.endRuntime_block_7189_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))))
      (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hflag rd7189'
  exact endRuntimeBlocks.endRuntime_block_7194
    (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
      endSkimOweWorldWord world.2 I outIlks outUrns,
      endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    (by simp) rd7194

theorem endX_skim_after_min_art_guard_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hsub : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (hfit : (endSkimGapWorldWord world.2 I).toNat +
        (endSkimDiffWorldWord world.2 I outIlks outUrns).toNat < UInt256.size)
    (hwad : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat < (endSkimArtWord outUrns).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw7150, k7150, C7150, rd7150⟩ :=
    endX_skim_after_min_to_guard (g := g) hsub hfit rd
  have hcond := endSkimLimitGtZero
    (endSkimWadWorldWord world.2 I outIlks outUrns) hwad
  obtain ⟨aw7180, k7180, C7180, rd7180⟩ :=
    endRuntimeBlocks.endRuntime_block_7150_fallthrough_packed
      (x0 := endSkimGapNewWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns) (x4 := endSkimInkWord outUrns)
      (x5 := endFlowVatIlksRateWord outIlks) (x6 := endArg1AddressWord I)
      (x7 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hperm hcond rd7150
  have hgapSlot := endSkimGapHashSlot (endSkimGapHashMem I outIlks outUrns) I
  have rd7180' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7180⟩
        [UInt256.isZero (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))),
          endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimAfterGapStoreMem I outIlks outUrns) aw7180 outUrns
        (endSkimGapStoredWorld world I outIlks outUrns) k7180 C7180 := by
    simpa [endSkimAfterGapStoreMem, endSkimGapStoredWorld,
      endRuntimeBlocks.endRuntime_block_7150_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_7150_fallthrough_memory, hgapSlot] using rd7180
  obtain ⟨aw7189, k7189, C7189, rd7189⟩ :=
    endRuntimeBlocks.endRuntime_block_7180_packed
      (x0 := UInt256.isZero
        (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))))
      (x1 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns)
      (R := [endSkimInkWord outUrns, endFlowVatIlksRateWord outIlks,
        endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd7180'
  have hflag := endSkimLimitFlagFail (endSkimArtWord outUrns) hart
  obtain ⟨aw7194, k7194, C7194, rd7194⟩ :=
    endRuntimeBlocks.endRuntime_block_7189_fallthrough_packed
      (x0 := UInt256.isZero
        (UInt256.gt (endSkimArtWord outUrns)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))))
      (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hflag
      (by simpa [endRuntimeBlocks.endRuntime_block_7180_stack] using rd7189)
  exact endRuntimeBlocks.endRuntime_block_7194
    (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
      endSkimOweWorldWord world.2 I outIlks outUrns,
      endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    (by simp) rd7194

theorem endX_skim_after_min_guards_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hsub : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (hfit : (endSkimGapWorldWord world.2 I).toNat +
        (endSkimDiffWorldWord world.2 I outIlks outUrns).toNat < UInt256.size)
    (hwad : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimAfterGapStoreMem I outIlks outUrns) aw' outUrns
      (endSkimGapStoredWorld world I outIlks outUrns) k' C' := by
  obtain ⟨aw7150, k7150, C7150, rd7150⟩ :=
    endX_skim_after_min_to_guard (g := g) hsub hfit rd
  have hcond := endSkimLimitGtZero
    (endSkimWadWorldWord world.2 I outIlks outUrns) hwad
  obtain ⟨aw7180, k7180, C7180, rd7180⟩ :=
    endRuntimeBlocks.endRuntime_block_7150_fallthrough_packed
      (x0 := endSkimGapNewWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns) (x4 := endSkimInkWord outUrns)
      (x5 := endFlowVatIlksRateWord outIlks) (x6 := endArg1AddressWord I)
      (x7 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hperm hcond rd7150
  have hgapSlot := endSkimGapHashSlot (endSkimGapHashMem I outIlks outUrns) I
  have rd7180' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7180⟩
        [UInt256.isZero (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))),
          endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimAfterGapStoreMem I outIlks outUrns) aw7180 outUrns
        (endSkimGapStoredWorld world I outIlks outUrns) k7180 C7180 := by
    simpa [endSkimAfterGapStoreMem, endSkimGapStoredWorld,
      endRuntimeBlocks.endRuntime_block_7150_fallthrough_stack,
      endRuntimeBlocks.endRuntime_block_7150_fallthrough_memory, hgapSlot] using rd7180
  obtain ⟨aw7189, k7189, C7189, rd7189⟩ :=
    endRuntimeBlocks.endRuntime_block_7180_packed
      (x0 := UInt256.isZero
        (UInt256.gt (endSkimWadWorldWord world.2 I outIlks outUrns)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))))
      (x1 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns)
      (R := [endSkimInkWord outUrns, endFlowVatIlksRateWord outIlks,
        endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel])
      (by simp) rd7180'
  have hflag := endSkimLimitFlagPass (endSkimArtWord outUrns) hart
  obtain ⟨aw7253, k7253, C7253, rd7253⟩ :=
    endRuntimeBlocks.endRuntime_block_7189_taken_packed
      (x0 := UInt256.isZero
        (UInt256.gt (endSkimArtWord outUrns)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))))
      (R := [endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hflag (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_7180_stack] using rd7189)
  exact ⟨aw7253, k7253, C7253, by
    simpa [endRuntimeBlocks.endRuntime_block_7189_taken_stack] using rd7253⟩

theorem endSkimAfterWadSuffixSubRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray)
    (hlt : (endSkimOweWord evm I outIlks outUrns).toNat <
        (endSkimWadWord evm I outIlks outUrns).toNat) :
    ExecBlock config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      endSkimAfterWadSuffixStmts .reverted := by
  simp [endSkimAfterWadSuffixStmts]
  exact ExecBlock.consRevert (endSkimInternalSubRevert evm I outIlks outUrns hlt)

theorem endSkimAfterWadSuffixAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hsub : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat)
    (hover : UInt256.size ≤ (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat) :
    ExecBlock config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      endSkimAfterWadSuffixStmts .reverted := by
  simp [endSkimAfterWadSuffixStmts]
  exact ExecBlock.consNormal
    (endSkimInternalSubOk evm I outIlks outUrns hsub) <|
    ExecBlock.consRevert
      (endSkimInternalAddRevert evm I outIlks outUrns hsz68 hover)

theorem endSkimAfterWadSuffixWadGuardRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hsub : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat)
    (hfit : (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat < UInt256.size)
    (hwad : endFreeInt256LimitWord.toNat <
        (endSkimWadWord evm I outIlks outUrns).toNat) :
    ExecBlock config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      endSkimAfterWadSuffixStmts .reverted := by
  simp [endSkimAfterWadSuffixStmts]
  exact ExecBlock.consNormal
    (endSkimInternalSubOk evm I outIlks outUrns hsub) <|
    ExecBlock.consNormal
      (endSkimInternalAddOk evm I outIlks outUrns hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign
        (endEvalGapNew_skim evm evm I outIlks outUrns)
        (endAssignGapNew_skim evm I outIlks outUrns hsz68)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSkimLimitGuard_wad_false evm
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))
          I outIlks outUrns hwad))

theorem endSkimAfterWadSuffixArtGuardRevert (evm : EVM.State) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hsub : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat)
    (hfit : (endSkimGapWord evm I).toNat +
        (endSkimDiffWord evm I outIlks outUrns).toNat < UInt256.size)
    (hwad : (endSkimWadWord evm I outIlks outUrns).toNat ≤
        endFreeInt256LimitWord.toNat)
    (hart : endFreeInt256LimitWord.toNat < (endSkimArtWord outUrns).toNat) :
    ExecBlock config (endSkimAfterWadFrame evm I outIlks outUrns) evm
      endSkimAfterWadSuffixStmts .reverted := by
  simp [endSkimAfterWadSuffixStmts]
  exact ExecBlock.consNormal
    (endSkimInternalSubOk evm I outIlks outUrns hsub) <|
    ExecBlock.consNormal
      (endSkimInternalAddOk evm I outIlks outUrns hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign
        (endEvalGapNew_skim evm evm I outIlks outUrns)
        (endAssignGapNew_skim evm I outIlks outUrns hsz68)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalSkimLimitGuard_art_false evm
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))
          I outIlks outUrns hwad hart))

theorem endSkimDiffWord_eq_world_of_callRel {s0 world I evm outIlks outUrns}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimDiffWord evm I outIlks outUrns =
      endSkimDiffWorldWord world.2 I outIlks outUrns := by
  have howe :=
    endSkimOweWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) h hsz68
  have hwad :=
    endSkimWadWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) h hsz68
  simp [endSkimDiffWord, endSkimDiffWorldWord, howe, hwad]

theorem endSkimGapSlot_eq_world (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimGapSlot I = endSkimGapWorldSlot I := by
  have hslot := endGapSlot_eq I (by omega : 36 ≤ I.calldata.size)
  have h13 : (⟨13⟩ : UInt256) = UInt256.ofNat 13 := by native_decide
  unfold endSkimGapSlot endSkimGapWorldSlot
  rw [hslot, h13]

theorem endSkimGapWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimGapWord evm I = endSkimGapWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (gapSlot (endArg0Bytes32Key I))
  have hslot := endGapSlot_eq I (by omega : 36 ≤ I.calldata.size)
  have h13 : (⟨13⟩ : UInt256) = UInt256.ofNat 13 := by native_decide
  unfold endSkimGapWord endSkimGapWorldWord endSkimGapWorldSlot endSkimGapSlot
  rw [hload, hslot]
  rw [h13]

theorem endSkimGapNewWord_eq_world_of_callRel {s0 world I evm outIlks outUrns}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endSkimGapNewWord evm I outIlks outUrns =
      endSkimGapNewWorldWord world.2 I outIlks outUrns := by
  have hgap := endSkimGapWord_eq_world_of_callRel h hsz68
  have hdiff :=
    endSkimDiffWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) h hsz68
  simp [endSkimGapNewWord, endSkimGapNewWorldWord, hgap, hdiff]

theorem endSkimWadWorld_le_oweWorld (σ : AccountMap) (I : ExecutionEnv)
    (outIlks outUrns : ByteArray) :
    (endSkimWadWorldWord σ I outIlks outUrns).toNat ≤
      (endSkimOweWorldWord σ I outIlks outUrns).toNat := by
  unfold endSkimWadWorldWord
  split <;> omega

theorem endX_skim_grab_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {preσ : AccountMap} {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
      [endSkimWadWorldWord preσ I outIlks outUrns,
        endSkimOweWorldWord preσ I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimAfterGapStoreMem I outIlks outUrns) aw outUrns world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw7334, k7334, C7334, rd7334⟩ :=
    endRuntimeBlocks.endRuntime_block_7253_packed
      (x0 := endSkimWadWorldWord preσ I outIlks outUrns)
      (x1 := endSkimOweWorldWord preσ I outIlks outUrns)
      (x2 := endSkimArtWord outUrns) (x3 := endSkimInkWord outUrns)
      (x4 := endFlowVatIlksRateWord outIlks) (x5 := endArg1AddressWord I)
      (x6 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) rd
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
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord world.2
              (UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    rw [htarget, hvatNoCode]
    native_decide
  obtain ⟨aw7365, k7365, C7365, rd7365⟩ :=
    endRuntimeBlocks.endRuntime_block_7334_fallthrough_packed
      (x0 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x1 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))
      (x2 := memLoad (UInt256.ofNat 64)
        (endSkimGrabCallMem preσ world.2 I outIlks outUrns))
      (x3 := memLoad (UInt256.ofNat 64)
        (endSkimAfterGapStoreMem I outIlks outUrns))
      (x4 := (⟨0⟩ : UInt256))
      (R := [endSkimWadWorldWord preσ I outIlks outUrns,
        endSkimOweWorldWord preσ I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) hcondCode
      (by
        simpa [endRuntimeBlocks.endRuntime_block_7253_stack, endSkimGrabCallMem]
          using rd7334)
  exact endRuntimeBlocks.endRuntime_block_7365
    (R := endRuntimeBlocks.endRuntime_block_7334_fallthrough_stack
      (σ := world.2)
      (x0 := storageRead I.codeOwner world.2 (UInt256.ofNat 1))
      (x1 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))
      (x2 := memLoad (UInt256.ofNat 64)
        (endSkimGrabCallMem preσ world.2 I outIlks outUrns))
      (x3 := memLoad (UInt256.ofNat 64)
        (endSkimAfterGapStoreMem I outIlks outUrns))
      (x4 := (⟨0⟩ : UInt256))
      (R := [endSkimWadWorldWord preσ I outIlks outUrns,
        endSkimOweWorldWord preσ I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_7334_fallthrough_stack])
    rd7365

theorem endSkimGrabCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preσ : AccountMap} {baseEvm : EVM.State}
    {outIlks outUrns : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size)
    (hwadEq :
      endSkimWadWord baseEvm I outIlks outUrns =
        endSkimWadWorldWord preσ I outIlks outUrns)
    (hwad : (endSkimWadWorldWord preσ I outIlks outUrns).toNat ≤
      endFreeInt256LimitWord.toNat)
    (hart : (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨7253⟩
      (fun cur frame e =>
        frame = endSkimAfterGapNewFrame baseEvm I outIlks outUrns ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata = outUrns ∧
        cur.stack =
          [endSkimWadWorldWord preσ I outIlks outUrns,
            endSkimOweWorldWord preσ I outIlks outUrns,
            endSkimArtWord outUrns, endSkimInkWord outUrns,
            endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
            ⟨562⟩, sel] ∧
        cur.mem = endSkimAfterGapStoreMem I outIlks outUrns ∧
        cur.aw = aw)
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "urn", thisAddr, vowAddr,
          .unary .neg (asInt256 (.var "wad")),
          .unary .neg (asInt256 (.var "art"))]
        "_grab")
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hrdata, hstack, hmem, haw⟩
  cases hframe
  have rd7253 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7253⟩
        [endSkimWadWorldWord preσ I outIlks outUrns,
          endSkimOweWorldWord preσ I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimAfterGapStoreMem I outIlks outUrns) aw outUrns cur.world k C := by
    simpa [hpc, hstack, hmem, haw, hrdata] using rd
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
        ExecBlock config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", .var "urn", thisAddr, vowAddr,
              .unary .neg (asInt256 (.var "wad")),
              .unary .neg (asInt256 (.var "art"))] "_grab")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skimAfterGapNew_false baseEvm evm
              I outIlks outUrns hsrcNoCode)))
    have hrev := endX_skim_grab_no_code
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outIlks := outIlks)
      (outUrns := outUrns) (k := k) (C := C) (preσ := preσ)
      (world := cur.world) houtIlks h160 houtUrns hvatNoCode rd7253
    exact BlockProgress.ofRDrev hsource hrev
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hrequire :
        ExecBlock config (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skimAfterGapNew_true baseEvm evm
            I outIlks outUrns hsrcCode))
        ExecBlock.nil
    obtain ⟨aw7371, k7371, C7371, rd7371⟩ :=
      endX_skim_to_grab_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outIlks := outIlks)
        (outUrns := outUrns) (k := k) (C := C) (preσ := preσ)
        (world := cur.world) houtIlks h160 houtUrns hvatNoCode rd7253
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimGrabCallCursor cur.world preσ I sel aw7371 outIlks outUrns)
          k7371 C7371 (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "urn", thisAddr, vowAddr,
                .unary .neg (asInt256 (.var "wad")),
                .unary .neg (asInt256 (.var "art"))] "_grab" ]
          (runtimeExit (.abi [])) :=
      endSkimGrabExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw7371)
        (outIlks := outIlks) (outUrns := outUrns) (k := k7371) (C := C7371)
        (baseEvm := baseEvm) (evm := evm) (preσ := preσ) (world := cur.world)
        hperm hsz68 houtIlks h160 houtUrns hwadEq hwad hart
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "urn", thisAddr, vowAddr,
                .unary .neg (asInt256 (.var "wad")),
                .unary .neg (asInt256 (.var "art"))] "_grab" ]
          (runtimeExit (.abi [])) :=
      htail (by simpa [endSkimGrabCallCursor] using rd7371) hrel
    have hprogress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimAfterGapNewFrame baseEvm I outIlks outUrns) evm
          ([ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
            [ .externalCall (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))] "_grab" ])
          (runtimeExit (.abi [])) :=
      BlockProgress.prepend hrequire htailProgress
    simpa [checkedExternalCallStmts] using hprogress

theorem endX_skim_after_min_add_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outIlks outUrns k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hsub : (endSkimWadWorldWord world.2 I outIlks outUrns).toNat ≤
        (endSkimOweWorldWord world.2 I outIlks outUrns).toNat)
    (hover : UInt256.size ≤ (endSkimGapWorldWord world.2 I).toNat +
        (endSkimDiffWorldWord world.2 I outIlks outUrns).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
      [endSkimWadWorldWord world.2 I outIlks outUrns, ⟨0⟩,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]
      (endSkimTagHashMem I outIlks outUrns) aw outUrns world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_7113_packed
      (x0 := endSkimWadWorldWord world.2 I outIlks outUrns)
      (x1 := (⟨0⟩ : UInt256))
      (x2 := endSkimOweWorldWord world.2 I outIlks outUrns)
      (x3 := endSkimArtWord outUrns) (x4 := endSkimInkWord outUrns)
      (x5 := endFlowVatIlksRateWord outIlks) (x6 := endArg1AddressWord I)
      (x7 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  have hgapSlot := endSkimGapHashSlot (endSkimTagHashMem I outIlks outUrns) I
  have rd10154' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
        [endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns, ⟨7145⟩,
          endSkimGapWorldWord world.2 I, ⟨7150⟩,
          endSkimWadWorldWord world.2 I outIlks outUrns,
          endSkimOweWorldWord world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimGapHashMem I outIlks outUrns) aw10154 outUrns world k10154 C10154 := by
    simpa [endRuntimeBlocks.endRuntime_block_7113_stack,
      endSkimGapHashMem, endSkimGapWorldWord, hgapSlot] using rd10154
  obtain ⟨aw7145, k7145, C7145, rd7145⟩ :=
    endX_flow_sub_ok
      (x := endSkimOweWorldWord world.2 I outIlks outUrns)
      (y := endSkimWadWorldWord world.2 I outIlks outUrns)
      (ret := (⟨7145⟩ : UInt256))
      (R := [endSkimGapWorldWord world.2 I, ⟨7150⟩,
        endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      hsub (by jump_dest) (by simp) rd10154'
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_7145_packed
      (R := [endSkimDiffWorldWord world.2 I outIlks outUrns,
        endSkimGapWorldWord world.2 I, ⟨7150⟩,
        endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endSkimDiffWorldWord, endGenericSubResult] using rd7145)
  have hcond := endPackAddFailCond
    (endSkimDiffWorldWord world.2 I outIlks outUrns)
    (endSkimGapWorldWord world.2 I) hover
  have rd10104 := endRuntimeBlocks.endRuntime_block_10092_fallthrough
    (x0 := endSkimDiffWorldWord world.2 I outIlks outUrns)
    (x1 := endSkimGapWorldWord world.2 I)
    (R := [⟨7150⟩, endSkimWadWorldWord world.2 I outIlks outUrns,
      endSkimOweWorldWord world.2 I outIlks outUrns,
      endSkimArtWord outUrns, endSkimInkWord outUrns,
      endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
      ⟨562⟩, sel])
    (by simp) hcond rd10092
  exact endRuntimeBlocks.endRuntime_block_10104
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endSkimDiffWorldWord world.2 I outIlks outUrns)
      (x1 := endSkimGapWorldWord world.2 I)
      (R := [⟨7150⟩, endSkimWadWorldWord world.2 I outIlks outUrns,
        endSkimOweWorldWord world.2 I outIlks outUrns,
        endSkimArtWord outUrns, endSkimInkWord outUrns,
        endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
        ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endSkimAfterWadSuffixThenGrabRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outIlks outUrns : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size)
    (houtUrns : outUrns.size < UInt256.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨7113⟩
      (fun cur frame e =>
        frame = endSkimAfterWadFrame e I outIlks outUrns ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata = outUrns ∧
        cur.stack =
          [endSkimWadWorldWord cur.world.2 I outIlks outUrns, ⟨0⟩,
            endSkimOweWorldWord cur.world.2 I outIlks outUrns,
            endSkimArtWord outUrns, endSkimInkWord outUrns,
            endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
            ⟨562⟩, sel] ∧
        cur.mem = endSkimTagHashMem I outIlks outUrns ∧
        cur.aw = aw)
      (endSkimAfterWadSuffixStmts ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
            .unary .neg (asInt256 (.var "wad")),
            .unary .neg (asInt256 (.var "art"))]
          "_grab")
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hrdata, hstack, hmem, haw⟩
  cases hframe
  have rd7113 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7113⟩
        [endSkimWadWorldWord cur.world.2 I outIlks outUrns, ⟨0⟩,
          endSkimOweWorldWord cur.world.2 I outIlks outUrns,
          endSkimArtWord outUrns, endSkimInkWord outUrns,
          endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
          ⟨562⟩, sel]
        (endSkimTagHashMem I outIlks outUrns) aw outUrns cur.world k C := by
    simpa [hpc, hstack, hmem, haw, hrdata] using rd
  have howe :=
    endSkimOweWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) hrel hsz68
  have hwadEq :=
    endSkimWadWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) hrel hsz68
  have hdiff :=
    endSkimDiffWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns) hrel hsz68
  have hgap := endSkimGapWord_eq_world_of_callRel hrel hsz68
  have hgapNew :=
    endSkimGapNewWord_eq_world_of_callRel (outIlks := outIlks) (outUrns := outUrns)
      hrel hsz68
  have hsubWorld :=
    endSkimWadWorld_le_oweWorld cur.world.2 I outIlks outUrns
  have hsubSource :
      (endSkimWadWord evm I outIlks outUrns).toNat ≤
        (endSkimOweWord evm I outIlks outUrns).toNat := by
    simpa [hwadEq, howe] using hsubWorld
  by_cases hfitWorld :
      (endSkimGapWorldWord cur.world.2 I).toNat +
        (endSkimDiffWorldWord cur.world.2 I outIlks outUrns).toNat < UInt256.size
  · have hfitSource :
        (endSkimGapWord evm I).toNat +
          (endSkimDiffWord evm I outIlks outUrns).toNat < UInt256.size := by
      simpa [hgap, hdiff] using hfitWorld
    by_cases hwad :
        (endSkimWadWorldWord cur.world.2 I outIlks outUrns).toNat ≤
          endFreeInt256LimitWord.toNat
    · have hwadSource :
          (endSkimWadWord evm I outIlks outUrns).toNat ≤
            endFreeInt256LimitWord.toNat := by
        simpa [hwadEq] using hwad
      by_cases hart :
          (endSkimArtWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat
      · have hsource := endSkimAfterWadSuffixOk evm I outIlks outUrns hsz68
          hsubSource hfitSource hwadSource hart
        obtain ⟨aw7253, k7253, C7253, rd7253⟩ :=
          endX_skim_after_min_guards_ok
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
            (outIlks := outIlks) (outUrns := outUrns) (k := k) (C := C)
            (world := cur.world) hperm hsubWorld hfitWorld hwad hart rd7113
        have hstored :=
          hrel.storageStore_codeOwner (endSkimGapSlot I)
            (endSkimGapNewWord evm I outIlks outUrns)
        have hrelPost :
            CallStateRel (initState cA gh bl σ σ₀ g A I) I
              (endSkimGapStoredWorld cur.world I outIlks outUrns)
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
                (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns)) := by
          simpa [endSkimGapStoredWorld, storageWrite, hgapNew,
            endSkimGapSlot_eq_world I hsz68] using hstored
        have htailProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endSkimAfterGapNewFrame evm I outIlks outUrns)
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
                (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))
              (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))]
                "_grab")
              (runtimeExit (.abi [])) :=
          endSkimGrabCheckedCallRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw7253)
            (preσ := cur.world.2) (baseEvm := evm)
            (outIlks := outIlks) (outUrns := outUrns)
            hperm hsz68 houtIlks h160 houtUrns hwadEq hwad hart
            { pc := ⟨7253⟩,
              stack :=
                [endSkimWadWorldWord cur.world.2 I outIlks outUrns,
                  endSkimOweWorldWord cur.world.2 I outIlks outUrns,
                  endSkimArtWord outUrns, endSkimInkWord outUrns,
                  endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
                  ⟨562⟩, sel],
              mem := endSkimAfterGapStoreMem I outIlks outUrns,
              aw := aw7253,
              rdata := outUrns,
              world := endSkimGapStoredWorld cur.world I outIlks outUrns }
            k7253 C7253
            (endSkimAfterGapNewFrame evm I outIlks outUrns)
            (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
              (endSkimGapSlot I) (endSkimGapNewWord evm I outIlks outUrns))
            rfl rd7253
            ⟨rfl, hrelPost, rfl, rfl, rfl, rfl⟩
        exact BlockProgress.prepend hsource htailProgress
      · have hartGt :
            endFreeInt256LimitWord.toNat < (endSkimArtWord outUrns).toNat := by
          omega
        have hsource := endSkimAfterWadSuffixArtGuardRevert evm I outIlks outUrns
          hsz68 hsubSource hfitSource hwadSource hartGt
        have hrev := endX_skim_after_min_art_guard_fail
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
          (outIlks := outIlks) (outUrns := outUrns) (k := k) (C := C)
          (world := cur.world) hperm hsubWorld hfitWorld hwad hartGt rd7113
        exact BlockProgress.ofRDrev
          (Reasoning.Theory.execBlock_append_term hsource
            (by intros; intro h; cases h))
          hrev
    · have hwadGt :
          endFreeInt256LimitWord.toNat <
            (endSkimWadWorldWord cur.world.2 I outIlks outUrns).toNat := by
        omega
      have hwadSourceGt :
          endFreeInt256LimitWord.toNat <
            (endSkimWadWord evm I outIlks outUrns).toNat := by
        simpa [hwadEq] using hwadGt
      have hsource := endSkimAfterWadSuffixWadGuardRevert evm I outIlks outUrns
        hsz68 hsubSource hfitSource hwadSourceGt
      have hrev := endX_skim_after_min_wad_guard_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
        (outIlks := outIlks) (outUrns := outUrns) (k := k) (C := C)
        (world := cur.world) hperm hsubWorld hfitWorld hwadGt rd7113
      exact BlockProgress.ofRDrev
        (Reasoning.Theory.execBlock_append_term hsource
          (by intros; intro h; cases h))
        hrev
  · have hoverWorld :
        UInt256.size ≤ (endSkimGapWorldWord cur.world.2 I).toNat +
          (endSkimDiffWorldWord cur.world.2 I outIlks outUrns).toNat := by
      omega
    have hoverSource :
        UInt256.size ≤ (endSkimGapWord evm I).toNat +
          (endSkimDiffWord evm I outIlks outUrns).toNat := by
      simpa [hgap, hdiff] using hoverWorld
    have hsource := endSkimAfterWadSuffixAddRevert evm I outIlks outUrns
      hsz68 hsubSource hoverSource
    have hrev := endX_skim_after_min_add_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outIlks := outIlks) (outUrns := outUrns) (k := k) (C := C)
      (world := cur.world) hsubWorld hoverWorld rd7113
    exact BlockProgress.ofRDrev
      (Reasoning.Theory.execBlock_append_term hsource
        (by intros; intro h; cases h))
      hrev

def endSkimPostUrnsRmul1MinStmts : List Stmt :=
  [ .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
    .internalCall "min" [.var "ink", .var "owe"] "wad" ]

def endSkimPostUrnsTailStmts : List Stmt :=
  endSkimPostUrnsRmul0Stmts ++ endSkimPostUrnsRmul1MinStmts

theorem endSkimPostUrnsSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outIlks : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtIlks : outIlks.size < UInt256.size) (h160 : 160 ≤ outIlks.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨7050⟩
      (fun cur frame e =>
        frame = endSkimAfterUrnsFrame I outIlks cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        64 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
            endFlowVatIlksRateWord outIlks,
            endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSkimUrnsReturnMem I outIlks cur.rdata ∧
        cur.aw = endSkimAfterUrnsAw aw)
      (endSkimPostUrnsTailStmts ++
        (endSkimAfterWadSuffixStmts ++
          checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", .var "urn", thisAddr, vowAddr,
              .unary .neg (asInt256 (.var "wad")),
              .unary .neg (asInt256 (.var "art"))]
            "_grab"))
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, houtUrns, h64, hstack, hmem, haw⟩
  cases hframe
  have rd7050 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7050⟩
        [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          endFlowVatIlksRateWord outIlks,
          endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
        (endSkimUrnsReturnMem I outIlks cur.rdata) (endSkimAfterUrnsAw aw)
        cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have htagEq := endSkimTagWord_eq_world_of_callRel hrel hsz68
  by_cases hfit0 :
      (endSkimArtWord cur.rdata).toNat *
        (endFlowVatIlksRateWord outIlks).toNat < UInt256.size
  · have hsource0 := endSkimPostUrnsRmul0Ok evm I outIlks cur.rdata hfit0
    obtain ⟨aw7079, k7079, C7079, rd7079⟩ :=
      endX_skim_rmul0_ok
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
        (outIlks := outIlks) (outUrns := cur.rdata) (k := k) (C := C)
        (world := cur.world) houtIlks h160 houtUrns h64 hfit0 rd7050
    by_cases hfit1 :
        (endSkimOwe0Word outIlks cur.rdata).toNat *
          (endSkimTagWorldWord cur.world.2 I).toNat < UInt256.size
    · have hfit1Source :
          (endSkimOwe0Word outIlks cur.rdata).toNat *
            (endSkimTagWord evm I).toNat < UInt256.size := by
        simpa [htagEq] using hfit1
      have hsource1 :
          ExecBlock config (endSkimAfterOwe0Frame I outIlks cur.rdata) evm
            [ .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe" ]
            (.ok (endSkimAfterOweFrame evm I outIlks cur.rdata) evm) :=
        ExecBlock.consNormal
          (endSkimInternalRmul1Ok evm I outIlks cur.rdata hsz68 hfit1Source)
          ExecBlock.nil
      have hsource01 :
          ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
            (endSkimPostUrnsRmul0Stmts ++
              [ .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe" ])
            (.ok (endSkimAfterOweFrame evm I outIlks cur.rdata) evm) :=
        Reasoning.Theory.execBlock_append hsource0 hsource1
      obtain ⟨aw7099, k7099, C7099, rd7099⟩ :=
        endX_skim_rmul1_ok
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) (aw := aw7079)
          (outIlks := outIlks) (outUrns := cur.rdata) (k := k7079)
          (C := C7079) (world := cur.world) hfit1 rd7079
      have howeEq :=
        endSkimOweWord_eq_world_of_callRel (outIlks := outIlks)
          (outUrns := cur.rdata) hrel hsz68
      by_cases hleMin :
          (endSkimInkWord cur.rdata).toNat ≤
            (endSkimOweWorldWord cur.world.2 I outIlks cur.rdata).toNat
      · have hleSource :
            (endSkimInkWord cur.rdata).toNat ≤
              (endSkimOweWord evm I outIlks cur.rdata).toNat := by
          simpa [howeEq] using hleMin
        have hsourceMin :
            ExecBlock config (endSkimAfterOweFrame evm I outIlks cur.rdata) evm
              [ .internalCall "min" [.var "ink", .var "owe"] "wad" ]
              (.ok (endSkimAfterWadFrame evm I outIlks cur.rdata) evm) :=
          ExecBlock.consNormal
            (endSkimInternalMinLeft evm I outIlks cur.rdata hleSource)
            ExecBlock.nil
        have hsourcePrefix :
            ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
              (endSkimPostUrnsTailStmts)
              (.ok (endSkimAfterWadFrame evm I outIlks cur.rdata) evm) := by
          simpa [endSkimPostUrnsTailStmts, endSkimPostUrnsRmul1MinStmts,
            List.append_assoc] using
            (Reasoning.Theory.execBlock_append hsource01 hsourceMin)
        obtain ⟨aw7113, k7113, C7113, rd7113⟩ :=
          endX_skim_min_left
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw7099)
            (outIlks := outIlks) (outUrns := cur.rdata) (k := k7099)
            (C := C7099) (world := cur.world) hleMin rd7099
        have htailProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endSkimAfterWadFrame evm I outIlks cur.rdata) evm
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab")
              (runtimeExit (.abi [])) :=
          endSkimAfterWadSuffixThenGrabRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw7113)
            (outIlks := outIlks) (outUrns := cur.rdata)
            hperm hsz68 houtIlks h160 houtUrns
            { pc := ⟨7113⟩,
              stack :=
                [endSkimWadWorldWord cur.world.2 I outIlks cur.rdata, ⟨0⟩,
                  endSkimOweWorldWord cur.world.2 I outIlks cur.rdata,
                  endSkimArtWord cur.rdata, endSkimInkWord cur.rdata,
                  endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
                  ⟨562⟩, sel],
              mem := endSkimTagHashMem I outIlks cur.rdata,
              aw := aw7113,
              rdata := cur.rdata,
              world := cur.world }
            k7113 C7113 (endSkimAfterWadFrame evm I outIlks cur.rdata) evm
            rfl
            (by simpa [endSkimWadWorldWord, hleMin] using rd7113)
            ⟨rfl, hrel, rfl, rfl, rfl, rfl⟩
        simpa [endSkimPostUrnsTailStmts, endSkimPostUrnsRmul1MinStmts,
          List.append_assoc] using
          BlockProgress.prepend hsourcePrefix htailProgress
      · have hltMin :
            (endSkimOweWorldWord cur.world.2 I outIlks cur.rdata).toNat <
              (endSkimInkWord cur.rdata).toNat := by
          omega
        have hltSource :
            (endSkimOweWord evm I outIlks cur.rdata).toNat <
              (endSkimInkWord cur.rdata).toNat := by
          simpa [howeEq] using hltMin
        have hsourceMin :
            ExecBlock config (endSkimAfterOweFrame evm I outIlks cur.rdata) evm
              [ .internalCall "min" [.var "ink", .var "owe"] "wad" ]
              (.ok (endSkimAfterWadFrame evm I outIlks cur.rdata) evm) :=
          ExecBlock.consNormal
            (endSkimInternalMinRight evm I outIlks cur.rdata hltSource)
            ExecBlock.nil
        have hsourcePrefix :
            ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
              (endSkimPostUrnsTailStmts)
              (.ok (endSkimAfterWadFrame evm I outIlks cur.rdata) evm) := by
          simpa [endSkimPostUrnsTailStmts, endSkimPostUrnsRmul1MinStmts,
            List.append_assoc] using
            (Reasoning.Theory.execBlock_append hsource01 hsourceMin)
        obtain ⟨aw7113, k7113, C7113, rd7113⟩ :=
          endX_skim_min_right
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw7099)
            (outIlks := outIlks) (outUrns := cur.rdata) (k := k7099)
            (C := C7099) (world := cur.world) hltMin rd7099
        have htailProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endSkimAfterWadFrame evm I outIlks cur.rdata) evm
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab")
              (runtimeExit (.abi [])) :=
          endSkimAfterWadSuffixThenGrabRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (sel := sel) (aw := aw7113)
            (outIlks := outIlks) (outUrns := cur.rdata)
            hperm hsz68 houtIlks h160 houtUrns
            { pc := ⟨7113⟩,
              stack :=
                [endSkimWadWorldWord cur.world.2 I outIlks cur.rdata, ⟨0⟩,
                  endSkimOweWorldWord cur.world.2 I outIlks cur.rdata,
                  endSkimArtWord cur.rdata, endSkimInkWord cur.rdata,
                  endFlowVatIlksRateWord outIlks, endArg1AddressWord I, endArg0Word I,
                  ⟨562⟩, sel],
              mem := endSkimTagHashMem I outIlks cur.rdata,
              aw := aw7113,
              rdata := cur.rdata,
              world := cur.world }
            k7113 C7113 (endSkimAfterWadFrame evm I outIlks cur.rdata) evm
            rfl
            (by simpa [endSkimWadWorldWord, hleMin] using rd7113)
            ⟨rfl, hrel, rfl, rfl, rfl, rfl⟩
        simpa [endSkimPostUrnsTailStmts, endSkimPostUrnsRmul1MinStmts,
          List.append_assoc] using
          BlockProgress.prepend hsourcePrefix htailProgress
    · have hover1 :
          UInt256.size ≤ (endSkimOwe0Word outIlks cur.rdata).toNat *
            (endSkimTagWorldWord cur.world.2 I).toNat := by
        omega
      have hover1Source :
          UInt256.size ≤ (endSkimOwe0Word outIlks cur.rdata).toNat *
            (endSkimTagWord evm I).toNat := by
        simpa [htagEq] using hover1
      have hsource1 :
          ExecBlock config (endSkimAfterOwe0Frame I outIlks cur.rdata) evm
            [ .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe" ]
            .reverted :=
        ExecBlock.consRevert
          (endSkimInternalRmul1Revert evm I outIlks cur.rdata hsz68 hover1Source)
      have hsource01 :
          ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
            (endSkimPostUrnsRmul0Stmts ++
              [ .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe" ])
            .reverted :=
        Reasoning.Theory.execBlock_append hsource0 hsource1
      have hsourceFull :
          ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
            (endSkimPostUrnsTailStmts ++
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab"))
            .reverted := by
        simpa [endSkimPostUrnsTailStmts, endSkimPostUrnsRmul1MinStmts,
          List.append_assoc] using
          (Reasoning.Theory.execBlock_append_term
            (s2 := [ .internalCall "min" [.var "ink", .var "owe"] "wad" ] ++
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab"))
            hsource01 (by intros; intro h; cases h))
      have hrev := endX_skim_rmul1_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw7079)
        (outIlks := outIlks) (outUrns := cur.rdata) (k := k7079)
        (C := C7079) (world := cur.world) hover1 rd7079
      exact BlockProgress.ofRDrev hsourceFull hrev
  · have hover0 :
        UInt256.size ≤ (endSkimArtWord cur.rdata).toNat *
          (endFlowVatIlksRateWord outIlks).toNat := by
      omega
    have hsource0 := endSkimPostUrnsRmul0Revert evm I outIlks cur.rdata hover0
    have hsourceFull :
        ExecBlock config (endSkimAfterUrnsFrame I outIlks cur.rdata) evm
          (endSkimPostUrnsTailStmts ++
            (endSkimAfterWadSuffixStmts ++
              checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))]
                "_grab"))
          .reverted := by
      simpa [endSkimPostUrnsTailStmts, List.append_assoc] using
        (Reasoning.Theory.execBlock_append_term
          (s2 := endSkimPostUrnsRmul1MinStmts ++
            (endSkimAfterWadSuffixStmts ++
              checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))]
                "_grab"))
          hsource0 (by intros; intro h; cases h))
    have hrev := endX_skim_rmul0_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outIlks := outIlks) (outUrns := cur.rdata) (k := k) (C := C)
      (world := cur.world) houtIlks h160 houtUrns h64 hover0 rd7050
    exact BlockProgress.ofRDrev hsourceFull hrev

set_option maxHeartbeats 12000000 in
theorem endSkimAfterVatIlksSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨6914⟩
      (fun cur frame e =>
        frame = endSkimAfterVatIlksFrame I cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        160 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I cur.rdata),
            ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endSkimVatIlksReturnMem I cur.rdata ∧
        cur.aw = endSkimAfterVatIlksAw aw)
      ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn" ++
          (endSkimPostUrnsTailStmts ++
            (endSkimAfterWadSuffixStmts ++
              checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))]
                "_grab"))))
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, houtIlks, h160, hstack, hmem, haw⟩
  cases hframe
  have rd6914 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6914⟩
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endSkimVatIlksReturnMem I cur.rdata),
          ⟨0⟩, endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]
        (endSkimVatIlksReturnMem I cur.rdata) (endSkimAfterVatIlksAw aw)
        cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hsourceRate :
      ExecBlock config (endSkimAfterVatIlksFrame I cur.rdata) evm
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok (endSkimAfterRateFrame I cur.rdata) evm) :=
    ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalSkimRateFromVatIlk evm I cur.rdata))
      ExecBlock.nil
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
    have hsourceChecked :
        ExecBlock config (endSkimAfterRateFrame I cur.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skimAfterRate_false evm I cur.rdata hsrcNoCode)))
    have hsourcePrefix :
        ExecBlock config (endSkimAfterVatIlksFrame I cur.rdata) evm
          ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
            checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
              [.var "ilk", .var "urn"] "vatUrn")
          .reverted :=
      Reasoning.Theory.execBlock_append hsourceRate hsourceChecked
    have hsourceFull :
        ExecBlock config (endSkimAfterVatIlksFrame I cur.rdata) evm
          ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
            (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
              [.var "ilk", .var "urn"] "vatUrn" ++
              (endSkimPostUrnsTailStmts ++
                (endSkimAfterWadSuffixStmts ++
                  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                    [.var "ilk", .var "urn", thisAddr, vowAddr,
                      .unary .neg (asInt256 (.var "wad")),
                      .unary .neg (asInt256 (.var "art"))]
                    "_grab"))))
          .reverted := by
      simpa [List.append_assoc] using
        (Reasoning.Theory.execBlock_append_term
          (s2 := endSkimPostUrnsTailStmts ++
            (endSkimAfterWadSuffixStmts ++
              checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "urn", thisAddr, vowAddr,
                  .unary .neg (asInt256 (.var "wad")),
                  .unary .neg (asInt256 (.var "art"))]
                "_grab"))
          hsourcePrefix (by intros; intro h; cases h))
    have hrev := endX_skim_urns_no_code
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (outIlks := cur.rdata)
      (k := k) (C := C) (world := cur.world) houtIlks h160 hvatNoCode rd6914
    exact BlockProgress.ofRDrev hsourceFull hrev
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hsourceRequire :
        ExecBlock config (endSkimAfterRateFrame I cur.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkimAfterRateFrame I cur.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skimAfterRate_true evm I cur.rdata hsrcCode))
        ExecBlock.nil
    obtain ⟨aw7010, k7010, C7010, rd7010⟩ :=
      endX_skim_to_urns_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outIlks := cur.rdata)
        (k := k) (C := C) (world := cur.world) houtIlks h160 hvatNoCode rd6914
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimUrnsCallCursor cur.world I sel aw7010 cur.rdata cur.rdata)
          k7010 C7010 (endSkimAfterRateFrame I cur.rdata) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          ([ .externalCall (.storage vatRef) "urns" (.intLit 0)
              [.var "ilk", .var "urn"] "vatUrn" ] ++
            (endSkimPostUrnsTailStmts ++
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab")))
          (runtimeExit (.abi [])) := by
      refine BlockRefinesFrom.seqOrExit
        (endSkimUrnsExternalCallRefines
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw7010)
          (outIlks := cur.rdata) (rdata := cur.rdata) (k := k7010)
          (C := C7010) (evm := evm) (world := cur.world)
          hperm hsz68 houtIlks h160) ?_
      exact endSkimPostUrnsSuffixRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw7010)
        (outIlks := cur.rdata) hperm hsz68 houtIlks h160
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimAfterRateFrame I cur.rdata) evm
          ([ .externalCall (.storage vatRef) "urns" (.intLit 0)
              [.var "ilk", .var "urn"] "vatUrn" ] ++
            (endSkimPostUrnsTailStmts ++
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab")))
          (runtimeExit (.abi [])) :=
      htail (by simpa [endSkimUrnsCallCursor] using rd7010) hrel
    have hcheckedProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkimAfterRateFrame I cur.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
            [.var "ilk", .var "urn"] "vatUrn" ++
            (endSkimPostUrnsTailStmts ++
              (endSkimAfterWadSuffixStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", .var "urn", thisAddr, vowAddr,
                    .unary .neg (asInt256 (.var "wad")),
                    .unary .neg (asInt256 (.var "art"))]
                  "_grab")))
          (runtimeExit (.abi [])) := by
      simpa [checkedExternalCallStmts, List.append_assoc] using
        BlockProgress.prepend hsourceRequire htailProgress
    simpa [List.append_assoc] using
      BlockProgress.prepend hsourceRate hcheckedProgress

set_option maxHeartbeats 12000000 in
theorem endSkimBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 26))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨851⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 26 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some skimTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 26 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some skimTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (skimTransition.params.map Param.name) (transitionSignature skimTransition).paramTypes
        I.calldata = some (endSkimStore I) := by
      simpa [config, skimTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_skim_ok (I := I) hsz68
    have hTagWord :
        endSkimTagWorldWord σ_evm I = endSkimTagWorldWord σ_solm I := by
      simpa [endSkimTagWorldWord, storageRead_eq] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSkimTagWorldSlot I)
          (default : UInt256)
    by_cases htagZeroEvm : endSkimTagWorldWord σ_evm I = ⟨0⟩
    · have htagZeroSolm : endSkimTagWorldWord σ_solm I = ⟨0⟩ :=
        hTagWord.symm.trans htagZeroEvm
      have htagSrc :
          endSkimTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
            ⟨0⟩ := by
        rw [endSkimTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagZeroSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endSkimStore I) skimTransition.body .reverted := by
        simpa [initState] using
          endSkimBodyTagFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc
      exact (endX_skim_tag_fail (g := Sat256.ofUInt256 g)
          hsz68 hsize htagZeroEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have htagNonzeroSolm : endSkimTagWorldWord σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact htagZeroEvm (hTagWord.trans hzero)
      have htagSrc :
          endSkimTagWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠
            ⟨0⟩ := by
        rw [endSkimTagWord_init_eq
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) hsz68]
        exact htagNonzeroSolm
      have hCodeEq :
          extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) =
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) :=
        endPackVatCodeSize_accountMapEquiv (I := I) hAccounts
      by_cases hvatNoCodeEvm :
          extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) = ⟨0⟩
      · have hvatNoCodeSolm :
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) = ⟨0⟩ :=
          hCodeEq.symm.trans hvatNoCodeEvm
        have hvatNoCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨1⟩)
                solcAddrMask) = ⟨0⟩ := by
          rw [endPackVatTarget_init_eq]
          simpa [initState] using hvatNoCodeSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endSkimStore I) skimTransition.body .reverted := by
          simpa [initState] using
            endSkimBodyVatNoCode
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz68 htagSrc hvatNoCodeSrc
        exact (endX_skim_vat_no_code (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hvatNoCodeEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hvatCodeSolm :
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) ≠ ⟨0⟩ := by
          intro hzero
          exact hvatNoCodeEvm (hCodeEq.trans hzero)
        have hvatCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨1⟩)
                solcAddrMask) ≠ ⟨0⟩ := by
          rw [endPackVatTarget_init_eq]
          simpa [initState] using hvatCodeSolm
        obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
          endX_skim_to_vat_ilks_call (g := Sat256.ofUInt256 g)
            hsz68 hsize htagZeroEvm hvatNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := endSkimStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++
                [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := endSkimStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
          endSkimBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 htagSrc hvatCodeSrc
        have hpostRel :
            CallStateRel
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
              (cA, σ_evm)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
          CallStateRel.initState hAccounts
        have htail :
            BlockRefinesFrom endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config
              (endSkimVatIlksCallCursor cA σ_evm I sel awCall ByteArray.empty)
              kCall CCall { contract := contract, locals := endSkimStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (fun cur _ e =>
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e)
              ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                  [.var "ilk"] "vatIlk" ] ++
                ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
                  (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                    [.var "ilk", .var "urn"] "vatUrn" ++
                    (endSkimPostUrnsTailStmts ++
                      (endSkimAfterWadSuffixStmts ++
                        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                          [.var "ilk", .var "urn", thisAddr, vowAddr,
                            .unary .neg (asInt256 (.var "wad")),
                            .unary .neg (asInt256 (.var "art"))]
                          "_grab")))))
              (runtimeExit (.abi [])) := by
          refine BlockRefinesFrom.seqOrExit
            (endSkimVatIlksExternalCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) (rdata := ByteArray.empty) (k := kCall) (C := CCall)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              hperm hsz68) ?_
          exact endSkimAfterVatIlksSuffixRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
            (aw := awCall) hperm hsz68
        have hprogress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endSkimStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((nonpayable ++
                [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                    [.var "ilk"] "vatIlk" ] ++
                  ([ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
                    (checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
                      [.var "ilk", .var "urn"] "vatUrn" ++
                      (endSkimPostUrnsTailStmts ++
                        (endSkimAfterWadSuffixStmts ++
                          checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                            [.var "ilk", .var "urn", thisAddr, vowAddr,
                              .unary .neg (asInt256 (.var "wad")),
                              .unary .neg (asInt256 (.var "art"))]
                            "_grab"))))))
              (runtimeExit (.abi [])) :=
          BlockProgress.seqOfRD
            (R := fun cur _ e =>
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I cur.world e)
            hprefix
            (by simpa [endSkimVatIlksCallCursor] using rdCall)
            hpostRel
            htail
        have hprogressBody :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endSkimStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              skimTransition.body (runtimeExit (.abi [])) := by
          simpa [skimTransition, checkedExternalCallStmts, endSkimPostUrnsTailStmts,
            endSkimPostUrnsRmul0Stmts, endSkimPostUrnsRmul1MinStmts,
            endSkimAfterWadSuffixStmts, List.append_assoc] using hprogress
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
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (skimTransition.params.map Param.name) (transitionSignature skimTransition).paramTypes
        I.calldata = none := by
      simpa [config, skimTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_skim_none_short (I := I) hsz4 hshort
    exact (endX_skim_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
