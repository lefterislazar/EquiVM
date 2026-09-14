import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.RuntimeBlocks_013
import Benchmarks.Dss.End.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Benchmarks.Dss.End

/-! ## `cage(bytes32)` -/

abbrev endCageIlkStore (I : ExecutionEnv) : Store :=
  endFreeStore I

abbrev endCageIlkUIntValue (w : UInt256) : Value :=
  .int (Int.ofNat w.toNat)

abbrev endCageIlkTagWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 12) (endArg0Word I)

abbrev endCageIlkArtWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 14) (endArg0Word I)

abbrev endCageIlkTagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tagSlot (endArg0Bytes32Key I))

abbrev endCageIlkTagWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endCageIlkTagWorldSlot I)

theorem endCageIlkTagHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 12).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endCageIlkTagWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 12) mem) =
    endCageIlkTagWorldSlot I
  simp [endCageIlkTagWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endCageIlkArtHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 14).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endCageIlkArtWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 14) mem) =
    endCageIlkArtWorldSlot I
  simp [endCageIlkArtWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

abbrev endCageIlkVatIlksSelectorWord : UInt256 := UInt256.ofNat 3647180086

abbrev endCageIlkVatIlksSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)

def endCageIlkVatIlksPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg0Word I)

def endCageIlkVatIlksEncodedCall (I : ExecutionEnv) : ByteArray :=
  ilksSelector ++ ⟨(endCageIlkVatIlksPayloadBytes I).toArray⟩

theorem endCageIlkEncodeABIValues_vatIlks (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    encodeABIValues? [bytes32] [endArg0Bytes32Value I] =
      some (endCageIlkVatIlksPayloadBytes I) := by
  have hhead : abiTupleHeadSize? [bytes32] = some 32 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I hsz36, hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endCageIlkVatIlksPayloadBytes]

theorem endCageIlkEncodeCallWithSelector_vatIlks (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    ABI.encodeCallWithSelector? ilksSelector [bytes32] [endArg0Bytes32Value I] =
      some (endCageIlkVatIlksEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endCageIlkEncodeABIValues_vatIlks I hsz36]
  simp [endCageIlkVatIlksEncodedCall, endCageIlkVatIlksPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endCageIlkExternalEncode_vatIlks_branch (args : List Value) :
    config.externalABI.encode? "vatIlks" args =
      ABI.encodeCallWithSelector? ilksSelector [bytes32] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  rfl

theorem endCageIlkExternalEncode_vatIlks (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "vatIlks" [endArg0Bytes32Value I] =
      some (endCageIlkVatIlksEncodedCall I) := by
  rw [endCageIlkExternalEncode_vatIlks_branch]
  exact endCageIlkEncodeCallWithSelector_vatIlks I hsz36

abbrev endCageIlkVatIlksWord0 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endCageIlkVatIlksWord1 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endCageIlkVatIlksWord2 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endCageIlkVatIlksWord3 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 96).take 32)

abbrev endCageIlkVatIlksWord4 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 128).take 32)

abbrev endCageIlkVatIlksValues (out : ByteArray) : List Value :=
  [endCageIlkUIntValue (endCageIlkVatIlksWord0 out),
    endCageIlkUIntValue (endCageIlkVatIlksWord1 out),
    endCageIlkUIntValue (endCageIlkVatIlksWord2 out),
    endCageIlkUIntValue (endCageIlkVatIlksWord3 out),
    endCageIlkUIntValue (endCageIlkVatIlksWord4 out)]

abbrev endCageIlkSpotIlksPipWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endCageIlkSpotIlksMatWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endCageIlkSpotIlksValues (out : ByteArray) : List Value :=
  [.address (AccountAddress.ofNat (endCageIlkSpotIlksPipWord out).toNat),
    endCageIlkUIntValue (endCageIlkSpotIlksMatWord out)]

theorem endCageIlkDecodeScalarWordsWithMode_legacy_uint256x5_ok {out : ByteArray}
    (h160 : 160 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out.toList 0 =
      some (endCageIlkVatIlksValues out) := by
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
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (endCageIlkUIntValue (endCageIlkVatIlksWord0 out), 0 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord0,
      endCageIlkUIntValue, List.drop_zero] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endCageIlkUIntValue (endCageIlkVatIlksWord1 out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord1,
      endCageIlkUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
        some (endCageIlkUIntValue (endCageIlkVatIlksWord2 out), 64 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord2,
      endCageIlkUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
        some (endCageIlkUIntValue (endCageIlkVatIlksWord3 out), 96 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord3,
      endCageIlkUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96)
  rw [hdec96]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
        some (endCageIlkUIntValue (endCageIlkVatIlksWord4 out), 128 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord4,
      endCageIlkUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 128) htake128)
  rw [hdec128]

theorem endCageIlkDecodeScalarWordsWithMode_legacy_uint256x5_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          some (endCageIlkUIntValue (endCageIlkVatIlksWord0 out), 0 + 32) := by
      simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord0,
        endCageIlkUIntValue, List.drop_zero] using
        (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endCageIlkUIntValue (endCageIlkVatIlksWord1 out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord1,
          endCageIlkUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind]
      by_cases h64 : ((out.toList.drop 64).take 32).length = 32
      · have hdec64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (endCageIlkUIntValue (endCageIlkVatIlksWord2 out), 64 + 32) := by
          simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord2,
            endCageIlkUIntValue] using
            (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) h64)
        rw [hdec64]
        simp only [Option.bind, bind, Nat.reduceAdd]
        by_cases h96 : ((out.toList.drop 96).take 32).length = 32
        · have hdec96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                some (endCageIlkUIntValue (endCageIlkVatIlksWord3 out), 96 + 32) := by
            simpa [uint256, uint256Int, abiUInt256, endCageIlkVatIlksWord3,
              endCageIlkUIntValue] using
              (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) h96)
          rw [hdec96]
          simp only [Option.bind, bind, Nat.reduceAdd]
          have h128 : ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hnone128 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
                none := by
            simpa [uint256, uint256Int, abiUInt256] using
              (decodeScalarWordWithMode_uint256_none_short
                (mode := DecodeMode.legacySolc05) (bytes := out.toList)
                (start := 128) h128)
          rw [hnone128]
        · have hnone96 :
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
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          none := by
      simpa [uint256, uint256Int, abiUInt256] using
        (decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (bytes := out.toList) (start := 0) h0)
    rw [hnone0]
    rfl

theorem endCageIlkDecodeReturnValues_legacy_uint256x5_ok {out : ByteArray}
    (h160 : 160 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out =
      some (endCageIlkVatIlksValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, uint256, uint256] =
      some 160 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 160)
    (by decide) (by decide)]
  rw [endCageIlkDecodeScalarWordsWithMode_legacy_uint256x5_ok h160]

theorem endCageIlkDecodeReturnValues_legacy_uint256x5_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, uint256, uint256] =
      some 160 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 160)
    (by decide) (by decide)]
  rw [endCageIlkDecodeScalarWordsWithMode_legacy_uint256x5_none_short hshort]

theorem endCageIlkExternalDecode_vatIlks_ok {out : ByteArray}
    (h160 : 160 ≤ out.size) :
    config.externalABI.decode? "vatIlks" out =
      some (endCageIlkVatIlksValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  exact endCageIlkDecodeReturnValues_legacy_uint256x5_ok h160

theorem endCageIlkExternalDecode_vatIlks_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    config.externalABI.decode? "vatIlks" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  exact endCageIlkDecodeReturnValues_legacy_uint256x5_none_short hshort

theorem endCageIlkDecodeScalarWordsWithMode_legacy_addr_uint256_ok {out : ByteArray}
    (h64 : 64 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [addr, uint256] out.toList 0 =
      some (endCageIlkSpotIlksValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
        some (.address (AccountAddress.ofNat (endCageIlkSpotIlksPipWord out).toNat),
          0 + 32) := by
    simpa [addr, abiAddress, endCageIlkSpotIlksPipWord, List.drop_zero] using
      (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endCageIlkUIntValue (endCageIlkSpotIlksMatWord out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endCageIlkSpotIlksMatWord,
      endCageIlkUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]

theorem endCageIlkDecodeScalarWordsWithMode_legacy_addr_uint256_none_short
    {out : ByteArray} (hshort : out.size < 64) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [addr, uint256] out.toList 0 =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          some (.address (AccountAddress.ofNat (endCageIlkSpotIlksPipWord out).toNat),
            0 + 32) := by
      simpa [addr, abiAddress, endCageIlkSpotIlksPipWord, List.drop_zero] using
        (decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    have h32 : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    have hnone32 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
          none := by
      simpa [uint256, uint256Int, abiUInt256] using
        (decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 32) h32)
    rw [hnone32]
  · have hnone0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          none := by
      simpa [addr, abiAddress] using
        (decodeScalarWord_legacyAddress_none_short (bytes := out.toList) (start := 0) h0)
    rw [hnone0]
    simp only [Option.bind, bind]

theorem endCageIlkDecodeReturnValues_legacy_spotIlks_ok {out : ByteArray}
    (h64 : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out =
      some (endCageIlkSpotIlksValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256]) (bytes := out.toList) (cursor := 0) (total := 64)
    (by decide) (by decide)]
  rw [endCageIlkDecodeScalarWordsWithMode_legacy_addr_uint256_ok h64]

theorem endCageIlkDecodeReturnValues_legacy_spotIlks_none_short {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [addr, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [addr, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256]) (bytes := out.toList) (cursor := 0) (total := 64)
    (by decide) (by decide)]
  rw [endCageIlkDecodeScalarWordsWithMode_legacy_addr_uint256_none_short hshort]

theorem endCageIlkExternalDecode_spotIlks_ok {out : ByteArray}
    (h64 : 64 ≤ out.size) :
    config.externalABI.decode? "spotIlks" out =
      some (endCageIlkSpotIlksValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "spotIlks" = "cage")]
  rw [if_neg (by decide : ¬ "spotIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "catIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "dogIlks")]
  rw [if_pos (by decide : "spotIlks" = "spotIlks")]
  exact endCageIlkDecodeReturnValues_legacy_spotIlks_ok h64

theorem endCageIlkExternalDecode_spotIlks_none_short {out : ByteArray}
    (hshort : out.size < 64) :
    config.externalABI.decode? "spotIlks" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "spotIlks" = "cage")]
  rw [if_neg (by decide : ¬ "spotIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "catIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "dogIlks")]
  rw [if_pos (by decide : "spotIlks" = "spotIlks")]
  exact endCageIlkDecodeReturnValues_legacy_spotIlks_none_short hshort

theorem endCageIlkVatIlksSelectorEncodedWord_prefix :
    (endCageIlkVatIlksSelectorEncodedWord.toByteArray).extract 0 4 = ilksSelector := by
  native_decide

abbrev endCageIlkVatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_8902_taken_memory
    (mem := solcFreePtrMem) (x0 := endArg0Word I)

abbrev endCageIlkVatIlksCallMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_8999_taken_memory
    (mem := endCageIlkVatIlksBaseMem I) (x0 := endArg0Word I)

abbrev endCageIlkVatIlksMemSel (I : ExecutionEnv) : ByteArray :=
  endCageIlkVatIlksSelectorEncodedWord.toByteArray.write 0
    (endCageIlkVatIlksBaseMem I) 128 32

abbrev endCageIlkVatIlksMemFull (I : ExecutionEnv) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endCageIlkVatIlksMemSel I) 132 32

theorem endCageIlkVatIlksBaseMem_eq_hashMem (I : ExecutionEnv) :
    endCageIlkVatIlksBaseMem I =
      twoWordHashMem (endArg0Word I) (UInt256.ofNat 12) solcFreePtrMem := by
  unfold endCageIlkVatIlksBaseMem twoWordHashMem wordAt0Mem wordAt32Mem
  dsimp [endRuntimeBlocks.endRuntime_block_8902_taken_memory]
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem endCageIlkVatIlksBaseMem_size (I : ExecutionEnv) :
    (endCageIlkVatIlksBaseMem I).size = 96 := by
  rw [endCageIlkVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_size_96 (endArg0Word I) (UInt256.ofNat 12) solcFreePtrMem_size

theorem endCageIlkVatIlksBaseMem_read64 (I : ExecutionEnv) :
    (endCageIlkVatIlksBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endCageIlkVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_read64 (endArg0Word I) (UInt256.ofNat 12)
    solcFreePtrMem_size solcFreePtrMem_read64

theorem endCageIlkVatIlksBaseMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endCageIlkVatIlksBaseMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkVatIlksBaseMem I)
    (by rw [endCageIlkVatIlksBaseMem_size I]; omega)
    (endCageIlkVatIlksBaseMem_read64 I)

theorem endCageIlkVatIlksCallMem_eq_full (I : ExecutionEnv) :
    endCageIlkVatIlksCallMem I = endCageIlkVatIlksMemFull I := by
  unfold endCageIlkVatIlksCallMem endCageIlkVatIlksMemFull
    endCageIlkVatIlksMemSel endCageIlkVatIlksSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_8999_taken_memory]
  rw [endCageIlkVatIlksBaseMem_mload64 I]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]

theorem endCageIlkVatIlksMemSel_size_ge160 (I : ExecutionEnv) :
    160 ≤ (endCageIlkVatIlksMemSel I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endCageIlkVatIlksSelectorEncodedWord (endCageIlkVatIlksBaseMem I) 128

theorem endCageIlkVatIlksCallMem_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endCageIlkVatIlksCallMem I).size := by
  rw [endCageIlkVatIlksCallMem_eq_full I]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I) (endCageIlkVatIlksMemSel I) 132

theorem endCageIlkVatIlksMemSel_size (I : ExecutionEnv) :
    (endCageIlkVatIlksMemSel I).size = 160 := by
  unfold endCageIlkVatIlksMemSel
  exact toByteArray_write32_size_of_ge (endCageIlkVatIlksBaseMem I)
    endCageIlkVatIlksSelectorEncodedWord 128 96 160
    (endCageIlkVatIlksBaseMem_size I) (by omega) (by native_decide) rfl

theorem endCageIlkVatIlksCallMem_size (I : ExecutionEnv) :
    (endCageIlkVatIlksCallMem I).size = 164 := by
  rw [endCageIlkVatIlksCallMem_eq_full I]
  unfold endCageIlkVatIlksMemFull
  exact toByteArray_write32_size_of_le (endCageIlkVatIlksMemSel I)
    (endArg0Word I) 132 160 164
    (endCageIlkVatIlksMemSel_size I)
    (by rw [endCageIlkVatIlksMemSel_size I]; omega)
    (by omega)

theorem endCageIlkVatIlksCallMem_read64 (I : ExecutionEnv) :
    (endCageIlkVatIlksCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endCageIlkVatIlksCallMem_eq_full I]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I) (endCageIlkVatIlksMemSel I) 132 64
    (by have := endCageIlkVatIlksMemSel_size_ge160 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endCageIlkVatIlksSelectorEncodedWord (endCageIlkVatIlksBaseMem I) 128 64
    (by rw [endCageIlkVatIlksBaseMem_size I]) (by omega)]
  exact endCageIlkVatIlksBaseMem_read64 I

theorem endCageIlkVatIlksCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endCageIlkVatIlksCallMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkVatIlksCallMem I)
    (by have := endCageIlkVatIlksCallMem_size_ge164 I; omega)
    (endCageIlkVatIlksCallMem_read64 I)

theorem endCageIlkVatIlksCallMem_readSelector (I : ExecutionEnv) :
    (endCageIlkVatIlksCallMem I).readWithPadding 128 4 = ilksSelector := by
  rw [endCageIlkVatIlksCallMem_eq_full I]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endCageIlkVatIlksMemSel_size_ge160 I; omega) (by omega)
    (by have := endCageIlkVatIlksMemSel_size_ge160 I; omega) (by decide) (by decide)]
  change ((endCageIlkVatIlksSelectorEncodedWord.toByteArray.write 0
      (endCageIlkVatIlksBaseMem I) 128 32).readWithPadding 128 4) = ilksSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endCageIlkVatIlksSelectorEncodedWord (endCageIlkVatIlksBaseMem I) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endCageIlkVatIlksSelectorEncodedWord_prefix]

theorem endCageIlkVatIlksCallMem_readIlk (I : ExecutionEnv) :
    (endCageIlkVatIlksCallMem I).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endCageIlkVatIlksCallMem_eq_full I]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I) (endCageIlkVatIlksMemSel I) 132

theorem endCageIlkVatIlksCallMem_readCallData (I : ExecutionEnv) :
    (endCageIlkVatIlksCallMem I).readWithPadding 128 36 =
      endCageIlkVatIlksEncodedCall I := by
  have hsize := endCageIlkVatIlksCallMem_size_ge164 I
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endCageIlkVatIlksCallMem I) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endCageIlkVatIlksCallMem_readSelector I, endCageIlkVatIlksCallMem_readIlk I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endCageIlkVatIlksEncodedCall, endCageIlkVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endCageIlkVatIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endCageIlkVatIlksSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel]

abbrev endCageIlkVatIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨160⟩] ++
    endCageIlkVatIlksCallRest σ I sel

abbrev endCageIlkVatIlksCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨9079⟩, stack := endCageIlkVatIlksCallStack σ I sel,
    mem := endCageIlkVatIlksCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endCageIlkVatIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat)

abbrev endCageIlkVatIlksReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endCageIlkVatIlksCallMem I) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endCageIlkAfterVatIlksAw (aw : UInt256) : UInt256 :=
  M (endCageIlkVatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endCageIlkAfterVatIlksFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endCageIlkStore I).insert "vatIlk" (collapseReturns (endCageIlkVatIlksValues out)) }

abbrev endCageIlkAfterArtState (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (ArtSlot (endArg0Bytes32Key I))
    (endCageIlkVatIlksWord0 out)

abbrev endCageIlkArtStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endCageIlkArtWorldSlot I)
    (endCageIlkVatIlksWord0 out))

abbrev endCageIlkSpotTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 6)) solcAddrMask

abbrev endCageIlkAfterVatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨9119⟩,
    stack := [UInt256.ofNat out.size,
      memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I out),
      endArg0Word I, ⟨562⟩, sel],
    mem := endCageIlkVatIlksReturnMem I out,
    aw := endCageIlkAfterVatIlksAw aw,
    rdata := out,
    world := world }

theorem endEvalCageIlkVatIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endCageIlkStore I } evm
      [.var "ilk"] = .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endCageIlkStore, endFreeStore_get_ilk]

theorem endCageIlkAfterVatIlksFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endCageIlkAfterVatIlksFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endCageIlkStore I).insert "vatIlk"
      (collapseReturns (endCageIlkVatIlksValues out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkStore I) (k := "vatIlk") (a := "ilk")
    (collapseReturns (endCageIlkVatIlksValues out)) (by decide)]
  exact endFreeStore_get_ilk I

theorem endEvalCageIlkIlkAfterVatIlks (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endCageIlkAfterVatIlksFrame I out) evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endCageIlkAfterVatIlksFrame_get_ilk]
  rfl

theorem endCageIlkAfterVatIlksFrame_get_Art_none (I : ExecutionEnv) (out : ByteArray) :
    (endCageIlkAfterVatIlksFrame I out).locals.get? "Art" = none := by
  change ((endCageIlkStore I).insert "vatIlk"
      (collapseReturns (endCageIlkVatIlksValues out))).get? "Art" = none
  rw [store_get_ne (endCageIlkStore I) (k := "vatIlk") (a := "Art")
    (collapseReturns (endCageIlkVatIlksValues out)) (by decide)]
  simp [endCageIlkStore, endFreeStore]

theorem endEvalCageIlkVatIlkWord0 (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endCageIlkAfterVatIlksFrame I out) evm
      (.tupleGet (.var "vatIlk") 0) =
      .ok (endCageIlkUIntValue (endCageIlkVatIlksWord0 out)) := by
  simp [evalExpr?, endCageIlkAfterVatIlksFrame, collapseReturns, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind, endCageIlkUIntValue]

theorem endAssignCageIlkArt (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config (endCageIlkAfterVatIlksFrame I out) evm
        .storage (ArtRef (.var "ilk"))
        (endCageIlkUIntValue (endCageIlkVatIlksWord0 out)) =
      .ok (endCageIlkAfterVatIlksFrame I out, endCageIlkAfterArtState evm I out) := by
  let er : EvaledStorageRef := { base := "Art", steps := [.mindex (endArg0Bytes32Key I)] }
  let loc : StorageLoc := wordLoc (ArtSlot (endArg0Bytes32Key I))
  have hdrop : 32 ≤ I.calldata.toList.length - 4 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    omega
  have her : evalStorageRef config (endCageIlkAfterVatIlksFrame I out) evm
      (ArtRef (.var "ilk")) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefStep, ArtRef, endArg0Bytes32Key,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      endEvalCageIlkIlkAfterVatIlks, bytes32Width, hdrop]
  have hty :
      storageTypeAt? (endCageIlkAfterVatIlksFrame I out).contract.storage er =
        some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simp [er, loc]
  have hstore :
      storageLocStore evm loc (endCageIlkUIntValue (endCageIlkVatIlksWord0 out)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (ArtSlot (endArg0Bytes32Key I)) (endCageIlkVatIlksWord0 out)) := by
    simpa [loc, wordLoc, uint256Loc, endCageIlkUIntValue] using
      storageLocStore_uint256 evm (ArtSlot (endArg0Bytes32Key I))
        (endCageIlkVatIlksWord0 out)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endCageIlkAfterVatIlksFrame I out) (evm := evm)
    (slot := ArtRef (.var "ilk")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endCageIlkVatIlksWord0 out).toNat)
    (endCageIlkAfterVatIlksFrame_get_Art_none I out)
    her hty hloc hstore
  simpa [endCageIlkUIntValue, endCageIlkAfterArtState, loc] using hassign

theorem endEvalSpotAddress_cageIlk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endCageIlkAfterVatIlksFrame I out) evm (.storage spotRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask).toNat)) := by
  have hbase :
      (endCageIlkAfterVatIlksFrame I out).locals.get? spotRef.base = none := by
    simp [endCageIlkAfterVatIlksFrame, endCageIlkStore, endFreeStore, spotRef]
  have her :
      evalStorageRef config (endCageIlkAfterVatIlksFrame I out) evm spotRef =
        .ok { base := "spot", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind]
  have hty :
      storageTypeAt? (endCageIlkAfterVatIlksFrame I out).contract.storage
          { base := "spot", steps := [] } =
        some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt]
  have hloc :
      config.storage.layout { base := "spot", steps := [] } =
        fun _ => some (addrLoc (UInt256.ofNat 6)) := by
    rw [show UInt256.ofNat 6 = (⟨6⟩ : UInt256) from by native_decide]
    exact endConfig_storage_spot
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc), endRuntimeStorageLocLoad_address_offset0]

theorem endCageIlkVatIlksReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkVatIlksReturnMem I out).size = 288 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endCageIlkVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endCageIlkVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endCageIlkVatIlksCallMem_size I]; omega)
    (by rw [endCageIlkVatIlksCallMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endCageIlkVatIlksCallMem_size I]
  omega

theorem endCageIlkVatIlksReturnMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkVatIlksReturnMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  have hread :
      (endCageIlkVatIlksReturnMem I out).readWithPadding 64 32 =
        (endCageIlkVatIlksCallMem I).readWithPadding 64 32 := by
    unfold endCageIlkVatIlksReturnMem
    rw [hcopy]
    exact write_read_below_gen_extend out (endCageIlkVatIlksCallMem I) 128 160 64
      (by decide) h160
      (by rw [endCageIlkVatIlksCallMem_size I]; omega)
      (by omega)
  rw [hread]
  exact endCageIlkVatIlksCallMem_read64 I

theorem endCageIlkVatIlksReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I out) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkVatIlksReturnMem I out)
    (by rw [endCageIlkVatIlksReturnMem_size I out hout h160]; omega)
    (endCageIlkVatIlksReturnMem_read64 I out hout h160)

theorem endCageIlkVatIlksReturnMem_read128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkVatIlksReturnMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endCageIlkVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endCageIlkVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endCageIlkVatIlksCallMem_size I]; omega)
    (by rw [endCageIlkVatIlksCallMem_size I]; omega)]
  have hpre : ((endCageIlkVatIlksCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endCageIlkVatIlksCallMem_size I]
    omega
  have hcopySize : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]), hpre]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 160 = 32 by omega]

theorem endCageIlkVatIlksReturnMem_mload128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (⟨128⟩ : UInt256) (endCageIlkVatIlksReturnMem I out) =
      endCageIlkVatIlksWord0 out := by
  unfold memLoad
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endCageIlkVatIlksReturnMem_size I out hout h160]
    omega)]
  rw [endCageIlkVatIlksReturnMem_read128 I out hout h160]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) =
    ABI.bytesToWord (out.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endCageIlkVatIlksArtWrite_eq (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    storageWrite I.codeOwner σ
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 14).toByteArray.write 0
            ((endArg0Word I).toByteArray.write 0 (endCageIlkVatIlksReturnMem I out)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32))
        (memLoad (memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I out))
          (endCageIlkVatIlksReturnMem I out)) =
      storageWrite I.codeOwner σ (endCageIlkArtWorldSlot I)
        (endCageIlkVatIlksWord0 out) := by
  rw [endCageIlkArtHashSlot (endCageIlkVatIlksReturnMem I out) I]
  rw [endCageIlkVatIlksReturnMem_mload64 I out hout h160]
  rw [endCageIlkVatIlksReturnMem_mload128 I out hout h160]

abbrev endCageIlkArtHashMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  twoWordHashMem (endArg0Word I) (UInt256.ofNat 14) (endCageIlkVatIlksReturnMem I out)

theorem endCageIlkArtHashMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkArtHashMem I out).size = 288 := by
  have hret := endCageIlkVatIlksReturnMem_size I out hout h160
  have h0 : (wordAt0Mem (endArg0Word I) (endCageIlkVatIlksReturnMem I out)).size = 288 := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le
      (endCageIlkVatIlksReturnMem I out) (endArg0Word I) 0 288 288
      hret (by rw [hret]; omega) (by native_decide)
  unfold endCageIlkArtHashMem twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le
    (wordAt0Mem (endArg0Word I) (endCageIlkVatIlksReturnMem I out))
    (UInt256.ofNat 14) 32 288 288 h0 (by rw [h0]; omega) (by native_decide)

theorem endCageIlkArtHashMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkArtHashMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hret := endCageIlkVatIlksReturnMem_size I out hout h160
  have h0 : (wordAt0Mem (endArg0Word I) (endCageIlkVatIlksReturnMem I out)).size = 288 := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le
      (endCageIlkVatIlksReturnMem I out) (endArg0Word I) 0 288 288
      hret (by rw [hret]; omega) (by native_decide)
  unfold endCageIlkArtHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [h0]; omega) (by omega) (by rw [h0]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hret]; omega) (by omega) (by rw [hret]; omega)]
  exact endCageIlkVatIlksReturnMem_read64 I out hout h160

theorem endCageIlkArtHashMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkArtHashMem I out) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkArtHashMem I out)
    (by rw [endCageIlkArtHashMem_size I out hout h160]; omega)
    (endCageIlkArtHashMem_read64 I out hout h160)

abbrev endCageIlkSpotIlksSelectorWord : UInt256 :=
  endCageIlkVatIlksSelectorWord

abbrev endCageIlkSpotIlksSelectorEncodedWord : UInt256 :=
  endCageIlkVatIlksSelectorEncodedWord

def endCageIlkSpotIlksPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  endCageIlkVatIlksPayloadBytes I

def endCageIlkSpotIlksEncodedCall (I : ExecutionEnv) : ByteArray :=
  endCageIlkVatIlksEncodedCall I

theorem endCageIlkExternalEncode_spotIlks (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "spotIlks" [endArg0Bytes32Value I] =
      some (endCageIlkSpotIlksEncodedCall I) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "spotIlks" = "cage")]
  rw [if_neg (by decide : ¬ "spotIlks" = "vatIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "catIlks")]
  rw [if_neg (by decide : ¬ "spotIlks" = "dogIlks")]
  rw [if_pos (by decide : "spotIlks" = "spotIlks")]
  change ABI.encodeCallWithSelector? ilksSelector [bytes32] [endArg0Bytes32Value I] =
    some (endCageIlkVatIlksEncodedCall I)
  exact endCageIlkEncodeCallWithSelector_vatIlks I hsz36

abbrev endCageIlkSpotIlksCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_9119_memory
    (mem := endCageIlkVatIlksReturnMem I out) (x2 := endArg0Word I)

abbrev endCageIlkSpotIlksMemSel (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endCageIlkSpotIlksSelectorEncodedWord.toByteArray.write 0
    (endCageIlkArtHashMem I out) 128 32

abbrev endCageIlkSpotIlksMemFull (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endCageIlkSpotIlksMemSel I out) 132 32

theorem endCageIlkSpotIlksCallMem_eq_full (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    endCageIlkSpotIlksCallMem I out = endCageIlkSpotIlksMemFull I out := by
  unfold endCageIlkSpotIlksCallMem endCageIlkSpotIlksMemFull
    endCageIlkSpotIlksMemSel
  dsimp [endRuntimeBlocks.endRuntime_block_9119_memory]
  rw [show (UInt256.ofNat 0).toNat = 0 from by native_decide,
    show (UInt256.ofNat 32).toNat = 32 from by native_decide]
  change (endArg0Word I).toByteArray.write 0
      (endCageIlkSpotIlksSelectorEncodedWord.toByteArray.write 0
        (endCageIlkArtHashMem I out)
        (memLoad (UInt256.ofNat 64) (endCageIlkArtHashMem I out)).toNat 32)
      (memLoad (UInt256.ofNat 64) (endCageIlkArtHashMem I out) + UInt256.ofNat 4).toNat 32 =
    (endArg0Word I).toByteArray.write 0
      (endCageIlkSpotIlksSelectorEncodedWord.toByteArray.write 0
        (endCageIlkArtHashMem I out) 128 32)
      132 32
  rw [endCageIlkArtHashMem_mload64 I out hout h160]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]

theorem endCageIlkSpotIlksMemSel_size_ge160 (I : ExecutionEnv) (out : ByteArray) :
    160 ≤ (endCageIlkSpotIlksMemSel I out).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endCageIlkSpotIlksSelectorEncodedWord (endCageIlkArtHashMem I out) 128

theorem endCageIlkSpotIlksCallMem_size_ge164 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    164 ≤ (endCageIlkSpotIlksCallMem I out).size := by
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I) (endCageIlkSpotIlksMemSel I out) 132

theorem endCageIlkSpotIlksCallMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I) (endCageIlkSpotIlksMemSel I out) 132 64
    (by have := endCageIlkSpotIlksMemSel_size_ge160 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endCageIlkSpotIlksSelectorEncodedWord (endCageIlkArtHashMem I out) 128 64
    (by rw [endCageIlkArtHashMem_size I out hout h160]; omega) (by omega)]
  exact endCageIlkArtHashMem_read64 I out hout h160

theorem endCageIlkSpotIlksCallMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksCallMem I out) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkSpotIlksCallMem I out)
    (by have := endCageIlkSpotIlksCallMem_size_ge164 I out hout h160; omega)
    (endCageIlkSpotIlksCallMem_read64 I out hout h160)

theorem endCageIlkSpotIlksCallMem_readSelector (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksCallMem I out).readWithPadding 128 4 = ilksSelector := by
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endCageIlkSpotIlksMemSel_size_ge160 I out; omega) (by omega)
    (by have := endCageIlkSpotIlksMemSel_size_ge160 I out; omega) (by decide) (by decide)]
  change ((endCageIlkSpotIlksSelectorEncodedWord.toByteArray.write 0
      (endCageIlkArtHashMem I out) 128 32).readWithPadding 128 4) = ilksSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endCageIlkSpotIlksSelectorEncodedWord (endCageIlkArtHashMem I out) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endCageIlkVatIlksSelectorEncodedWord_prefix]

theorem endCageIlkSpotIlksCallMem_readIlk (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksCallMem I out).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I) (endCageIlkSpotIlksMemSel I out) 132

theorem endCageIlkSpotIlksCallMem_readCallData (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksCallMem I out).readWithPadding 128 36 =
      endCageIlkSpotIlksEncodedCall I := by
  have hsize := endCageIlkSpotIlksCallMem_size_ge164 I out hout h160
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endCageIlkSpotIlksCallMem I out) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endCageIlkSpotIlksCallMem_readSelector I out hout h160,
    endCageIlkSpotIlksCallMem_readIlk I out hout h160]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endCageIlkSpotIlksEncodedCall, endCageIlkSpotIlksPayloadBytes,
    endCageIlkVatIlksEncodedCall, endCageIlkVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endCageIlkSpotIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endCageIlkSpotIlksSelectorWord, endCageIlkSpotTarget σ I, ⟨0⟩,
    endArg0Word I, ⟨562⟩, sel]

abbrev endCageIlkSpotIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endCageIlkSpotTarget σ I, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨64⟩] ++
    endCageIlkSpotIlksCallRest σ I sel

abbrev endCageIlkSpotIlksCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outVat rdata : ByteArray) : Cursor :=
  { pc := ⟨9215⟩, stack := endCageIlkSpotIlksCallStack world.2 I sel,
    mem := endCageIlkSpotIlksCallMem I outVat, aw := aw, rdata := rdata, world := world }

abbrev endCageIlkSpotIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat)

abbrev endCageIlkSpotIlksReturnMem (I : ExecutionEnv) (outVat outSpot : ByteArray) :
    ByteArray :=
  outSpot.write 0 (endCageIlkSpotIlksCallMem I outVat) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat outSpot.size)).toNat

abbrev endCageIlkAfterSpotIlksAw (aw : UInt256) : UInt256 :=
  M (endCageIlkSpotIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endCageIlkAfterSpotIlksFrame (I : ExecutionEnv) (outVat outSpot : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endCageIlkAfterVatIlksFrame I outVat).locals.insert "spotIlk"
      (collapseReturns (endCageIlkSpotIlksValues outSpot)) }

abbrev endCageIlkAfterSpotIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outVat outSpot : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨9255⟩,
    stack := [UInt256.ofNat outSpot.size,
      memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat outSpot),
      ⟨0⟩, endArg0Word I, ⟨562⟩, sel],
    mem := endCageIlkSpotIlksReturnMem I outVat outSpot,
    aw := endCageIlkAfterSpotIlksAw aw,
    rdata := outSpot,
    world := world }

theorem endCageIlkSpotIlksSetupStack_eq
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (out : ByteArray) (sel : UInt256)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    endRuntimeBlocks.endRuntime_block_9119_stack (ee := I)
        (mem := endCageIlkVatIlksReturnMem I out) (σ := world.2)
        (x1 := memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I out))
        (x2 := endArg0Word I) (R := [⟨562⟩, sel]) =
      extCodeSizeWord (endCageIlkArtStoredWorld world I out).2
          (endCageIlkSpotTarget (endCageIlkArtStoredWorld world I out).2 I) ::
        endCageIlkSpotIlksCallStack (endCageIlkArtStoredWorld world I out).2 I sel := by
  have hhashFree := endCageIlkArtHashMem_mload64 I out hout h160
  have hcallFree := endCageIlkSpotIlksCallMem_mload64 I out hout h160
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160] at hcallFree
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hhash :
      ((UInt256.ofNat 14).toByteArray.write 0
        ((endArg0Word I).toByteArray.write 0 (endCageIlkVatIlksReturnMem I out)
          (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) =
        endCageIlkArtHashMem I out := by
    rw [show (UInt256.ofNat 0).toNat = 0 from by native_decide,
      show (UInt256.ofNat 32).toNat = 32 from by native_decide]
    rfl
  dsimp [endRuntimeBlocks.endRuntime_block_9119_stack, endCageIlkSpotIlksCallStack,
    endCageIlkSpotIlksCallRest, endCageIlkSpotIlksSelectorWord, endCageIlkSpotTarget,
    endCageIlkArtStoredWorld]
  rw [endCageIlkVatIlksArtWrite_eq world.2 I out hout h160]
  rw [hhash, hhashFree]
  have hfull :
      (endArg0Word I).toByteArray.write 0
          (endCageIlkSpotIlksSelectorEncodedWord.toByteArray.write 0
            (endCageIlkArtHashMem I out) (⟨128⟩ : UInt256).toNat 32)
          (((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat) 32 =
        endCageIlkSpotIlksMemFull I out := by
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [hfull, hcallFree, hmaskGenerated, hlen, hend]
  rw [show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from by native_decide,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide]

theorem endX_cageIlk_after_vat_ilks_to_raw_spot_guard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (rd9119 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9119⟩
      (endCageIlkAfterVatIlksCursor I sel aw out world).stack
      (endCageIlkVatIlksReturnMem I out) (endCageIlkAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9202⟩
      (extCodeSizeWord (endCageIlkArtStoredWorld world I out).2
          (endCageIlkSpotTarget (endCageIlkArtStoredWorld world I out).2 I) ::
        endCageIlkSpotIlksCallStack (endCageIlkArtStoredWorld world I out).2 I sel)
      (endCageIlkSpotIlksCallMem I out) aw' out
      (endCageIlkArtStoredWorld world I out) k' C' := by
  obtain ⟨aw9202, k9202, C9202, rd9202⟩ :=
    endRuntimeBlocks.endRuntime_block_9119_packed
      (x0 := UInt256.ofNat out.size)
      (x1 := memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I out))
      (x2 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hperm
      (by simpa [endCageIlkAfterVatIlksCursor] using rd9119)
  have hworld :=
    endCageIlkVatIlksArtWrite_eq world.2 I out hout h160
  rw [hworld] at rd9202
  exact ⟨aw9202, k9202, C9202, by
    simpa [endCageIlkSpotIlksCallMem,
      endCageIlkSpotIlksSetupStack_eq world I out sel hout h160,
      endCageIlkArtStoredWorld] using rd9202⟩

theorem endX_cageIlk_spot_ilks_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hspotNoCode :
      extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) = ⟨0⟩)
    (rd9202 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9202⟩
      (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) ::
        endCageIlkSpotIlksCallStack world.2 I sel)
      (endCageIlkSpotIlksCallMem I out) aw out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hspotNoCode]
    decide
  have rd9209 := endRuntimeBlocks.endRuntime_block_9202_fallthrough
    (x0 := extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))
    (R := endCageIlkSpotIlksCallStack world.2 I sel)
    (by simp [endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest])
    hcond rd9202
  exact endRuntimeBlocks.endRuntime_block_9209
    (R := endRuntimeBlocks.endRuntime_block_9202_fallthrough_stack
      (x0 := extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))
      (R := endCageIlkSpotIlksCallStack world.2 I sel))
    (by simp [endRuntimeBlocks.endRuntime_block_9202_fallthrough_stack,
      endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest])
    rd9209

theorem endX_cageIlk_spot_ilks_guard_to_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hspotCode :
      extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) ≠ ⟨0⟩)
    (rd9202 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9202⟩
      (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) ::
        endCageIlkSpotIlksCallStack world.2 I sel)
      (endCageIlkSpotIlksCallMem I out) aw out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9215⟩
      (endCageIlkSpotIlksCallStack world.2 I sel)
      (endCageIlkSpotIlksCallMem I out) aw' out world k' C' := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hspotCode]
    native_decide
  obtain ⟨aw9213, k9213, C9213, rd9213⟩ :=
    endRuntimeBlocks.endRuntime_block_9202_taken_packed
      (x0 := extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))
      (R := endCageIlkSpotIlksCallStack world.2 I sel)
      (by simp [endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest])
      hcond (by jump_dest) rd9202
  exact endRuntimeBlocks.endRuntime_block_9213_packed
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I)))
    (R := endCageIlkSpotIlksCallStack world.2 I sel)
    (by simp [endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest])
    rd9213

theorem endCageIlkVatIlksSetupStack_eq (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) :
    endRuntimeBlocks.endRuntime_block_8999_taken_stack (ee := I)
        (mem := endCageIlkVatIlksBaseMem I) (σ := σ) (x0 := endArg0Word I)
        (R := [⟨562⟩, sel]) =
      UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
        endCageIlkVatIlksCallStack σ I sel := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hbase : memLoad (UInt256.ofNat 64) (endCageIlkVatIlksBaseMem I) = ⟨128⟩ :=
    endCageIlkVatIlksBaseMem_mload64 I
  have hcallRaw := endCageIlkVatIlksCallMem_mload64 I
  dsimp [endCageIlkVatIlksCallMem, endRuntimeBlocks.endRuntime_block_8999_taken_memory] at hcallRaw
  rw [hbase] at hcallRaw
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  dsimp [endRuntimeBlocks.endRuntime_block_8999_taken_stack,
    endCageIlkVatIlksCallStack, endCageIlkVatIlksCallRest,
    endCageIlkVatIlksSelectorWord, endPackVatTarget]
  rw [hbase, hcallRaw, hlen, hend, hmaskGenerated]
  rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
    show UInt256.ofNat 160 = (⟨160⟩ : UInt256) from by native_decide]

theorem endEvalTag_cageIlk (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage (tagRef (.var "ilk"))) =
      .ok (endCageIlkUIntValue (endCageIlkTagWord evm I)) := by
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [evalExpr_storage_scalar
    (er := { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (tagSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := by simp [endCageIlkStore, endFreeStore, tagRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, tagRef, endCageIlkStore,
        endFreeStore, endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_tag (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endCageIlkTagWord, endCageIlkUIntValue]

theorem endEvalTagEqGuard_cageIlk_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (htag : endCageIlkTagWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_cageIlk evm I hsz36, htag]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endCageIlkUIntValue]

theorem endEvalTagEqGuard_cageIlk_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (htag : endCageIlkTagWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalTag_cageIlk evm I hsz36]
  simp only [EvalResult.bind, bind, pure, evalExpr?, endCageIlkUIntValue]
  have hnotNat : (endCageIlkTagWord evm I).toNat ≠ 0 := by
    intro hnat
    exact htag (uint256_toNat_eq_zero hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalCodeSizeGuard_cageIlk_true {locals : Store} {evm : EVM.State}
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
  have hpos : 0 < (extCodeSizeWord evm.accountMap target).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalCodeSizeGuard_cageIlk_false {locals : Store} {evm : EVM.State}
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

theorem endCageIlkBodyLiveFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (endCageIlkStore I)
      cageIlkTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageIlkTransition, endCageIlkStore, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveGuard_free_false evm I hlive)))

theorem endCageIlkBodyTagFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWord evm I ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (endCageIlkStore I)
      cageIlkTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageIlkTransition, endCageIlkStore, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_free_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalTagEqGuard_cageIlk_false evm I hsz36 htag)))

theorem endCageIlkBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWord evm I = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endCageIlkStore I)
      cageIlkTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageIlkTransition, endCageIlkStore, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_free_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagEqGuard_cageIlk_true evm I hsz36 htag)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_free_false evm I hvatNoCode)))

theorem endCageIlkBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWord evm I = ⟨0⟩)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCageIlkStore I } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endCageIlkStore I } evm) := by
  simpa [endCageIlkStore, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_free_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalTagEqGuard_cageIlk_true evm I hsz36 htag)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_free_true evm I hvatCode)) <|
      ExecBlock.nil)

theorem endX_cageIlk_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1189 := endRuntimeBlocks.endRuntime_block_1171_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1189
    (R := endRuntimeBlocks.endRuntime_block_1171_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1171_fallthrough_stack])
    (by simpa using rd1189)

theorem endX_cageIlk_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8832⟩
      [endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1193 := endRuntimeBlocks.endRuntime_block_1171_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd8832 := endRuntimeBlocks.endRuntime_block_1193
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1171_taken_stack] using rd1193)
  have hoff : (UInt256.ofNat 4).toNat = 4 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1193_stack, endArg0Word, calldataWord, hoff]
      using rd8832⟩

theorem endX_cageIlk_live_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_cageIlk_to_body (g := g) hsz36 hsize hreach
  have hcond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) = UInt256.ofNat 0 := by
    rw [storageRead_eq]
    exact Reasoning.Theory.isZero_eq_zero_of_ne (by simpa using hlive)
  obtain ⟨_, _, rd8841⟩ := endRuntimeBlocks.endRuntime_block_8832_fallthrough
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcond rdBody
  exact endRuntimeBlocks.endRuntime_block_8841
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) rd8841

theorem endX_cageIlk_tag_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWorldWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_cageIlk_to_body (g := g) hsz36 hsize hreach
  have hliveCond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hraw : storageRead I.codeOwner σ (UInt256.ofNat 8) = UInt256.ofNat 0 := by
      rw [storageRead_eq]
      simpa [solcSlotWord] using hlive
    rw [hraw]
    decide
  obtain ⟨_, _, rd8902⟩ := endRuntimeBlocks.endRuntime_block_8832_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hliveCond (by jump_dest) rdBody
  have hcond :
      UInt256.isZero
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 12).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = UInt256.ofNat 0 := by
    rw [endCageIlkTagHashSlot solcFreePtrMem I]
    exact Reasoning.Theory.isZero_eq_zero_of_ne (by simpa [endCageIlkTagWorldWord] using htag)
  obtain ⟨_, _, rd8923⟩ := endRuntimeBlocks.endRuntime_block_8902_fallthrough
    (x0 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) hcond rd8902
  exact endRuntimeBlocks.endRuntime_block_8923
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) rd8923

theorem endX_cageIlk_to_vat_ilks_setup {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8999⟩
      [endArg0Word I, ⟨562⟩, sel] (endCageIlkVatIlksBaseMem I) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_cageIlk_to_body (g := g) hsz36 hsize hreach
  have hliveCond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hraw : storageRead I.codeOwner σ (UInt256.ofNat 8) = UInt256.ofNat 0 := by
      rw [storageRead_eq]
      simpa [solcSlotWord] using hlive
    rw [hraw]
    decide
  obtain ⟨_, _, rd8902⟩ := endRuntimeBlocks.endRuntime_block_8832_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hliveCond (by jump_dest) rdBody
  have htagCond :
      UInt256.isZero
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 12).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ UInt256.ofNat 0 := by
    rw [endCageIlkTagHashSlot solcFreePtrMem I]
    change UInt256.isZero (endCageIlkTagWorldWord σ I) ≠ UInt256.ofNat 0
    rw [htag]
    decide
  obtain ⟨aw8999, k8999, C8999, rd8999⟩ :=
    endRuntimeBlocks.endRuntime_block_8902_taken_packed
      (x0 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) htagCond (by jump_dest) rd8902
  exact ⟨aw8999, k8999, C8999, by simpa [endCageIlkVatIlksBaseMem] using rd8999⟩

theorem endX_cageIlk_vat_ilks_setup_to_raw_call_guard {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel aw : UInt256} {k C : ℕ}
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (rd8999 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8999⟩
      [endArg0Word I, ⟨562⟩, sel] (endCageIlkVatIlksBaseMem I) aw
      ByteArray.empty (cA, σ) k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9077⟩
      (endRuntimeBlocks.endRuntime_block_8999_taken_stack (ee := I)
        (mem := endCageIlkVatIlksBaseMem I) (σ := σ) (x0 := endArg0Word I)
        (R := [⟨562⟩, sel]))
      (endRuntimeBlocks.endRuntime_block_8999_taken_memory
        (mem := endCageIlkVatIlksBaseMem I) (x0 := endArg0Word I))
      aw' ByteArray.empty (cA, σ) k' C' := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (storageRead I.codeOwner σ (UInt256.ofNat 1))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land
              (storageRead I.codeOwner σ (UInt256.ofNat 1))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hmaskGenerated]
      simpa [endPackVatTarget, u256_land_comm] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  exact endRuntimeBlocks.endRuntime_block_8999_taken_packed
    (mem := endCageIlkVatIlksBaseMem I) (x0 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCode (by jump_dest) rd8999

theorem endX_cageIlk_raw_call_guard_to_vat_ilks_call {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel aw : UInt256} {k C : ℕ}
    (rd9077 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9077⟩
      (endRuntimeBlocks.endRuntime_block_8999_taken_stack (ee := I)
        (mem := endCageIlkVatIlksBaseMem I) (σ := σ) (x0 := endArg0Word I)
        (R := [⟨562⟩, sel]))
      (endRuntimeBlocks.endRuntime_block_8999_taken_memory
        (mem := endCageIlkVatIlksBaseMem I) (x0 := endArg0Word I))
      aw ByteArray.empty (cA, σ) k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9079⟩
      (endCageIlkVatIlksCallStack σ I sel) (endCageIlkVatIlksCallMem I) aw'
      ByteArray.empty (cA, σ) k' C' := by
  have hstackTaken := endCageIlkVatIlksSetupStack_eq σ I sel
  have rd9077' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9077⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endCageIlkVatIlksCallStack σ I sel)
        (endCageIlkVatIlksCallMem I) aw ByteArray.empty (cA, σ) k C := by
    rw [hstackTaken] at rd9077
    simpa [endCageIlkVatIlksCallMem] using rd9077
  have rd9079 := endRuntimeBlocks.endRuntime_block_9077
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := endCageIlkVatIlksCallStack σ I sel)
    (by change 13 ≤ 1024; decide)
    rd9077'
  exact ⟨aw, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_9077_stack] using rd9079⟩

theorem endX_cageIlk_to_vat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWorldWord σ I = ⟨0⟩)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9079⟩
      (endCageIlkVatIlksCallStack σ I sel) (endCageIlkVatIlksCallMem I) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw8999, k8999, C8999, rd8999⟩ :=
    endX_cageIlk_to_vat_ilks_setup (g := g) hsz36 hsize hlive htag hreach
  obtain ⟨aw9077, k9077, C9077, rd9077⟩ :=
    endX_cageIlk_vat_ilks_setup_to_raw_call_guard
      (g := g) (sel := sel) hvatCode rd8999
  exact endX_cageIlk_raw_call_guard_to_vat_ilks_call
    (g := g) (sel := sel) rd9077

set_option maxHeartbeats 12000000 in
theorem endCageIlkVatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageIlkVatIlksCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endCageIlkStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
      (sequenceExit ⟨9119⟩
        (fun cur frame e =>
          frame = endCageIlkAfterVatIlksFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          160 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I cur.rdata),
              endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endCageIlkVatIlksReturnMem I cur.rdata ∧
          cur.aw = endCageIlkAfterVatIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨9079⟩ = some (.GAS, .none); decide)
    (by simp [endCageIlkVatIlksCallStack, endCageIlkVatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨9080⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCageIlkVatIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_free]
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
    exact endEvalCageIlkVatIlksArgs evm I
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endCageIlkExternalEncode_vatIlks I hsz36]
    change some (endCageIlkVatIlksEncodedCall I) =
      some ((endCageIlkVatIlksCallMem I).readWithPadding 128 36)
    rw [endCageIlkVatIlksCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h160 : 160 ≤ out.size
    · rw [endCageIlkExternalDecode_vatIlks_ok h160]
      intro rd hrel
      have rd9081 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
            ((⟨1⟩ : UInt256) :: endCageIlkVatIlksCallRest σ I sel)
            (endCageIlkVatIlksReturnMem I out) (endCageIlkVatIlksCallAw aw)
            out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkVatIlksCallStack,
          endCageIlkVatIlksCallRest, endCageIlkVatIlksCallAw,
          endCageIlkVatIlksReturnMem] using rd
      have rd9097 := endRuntimeBlocks.endRuntime_block_9081_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkVatIlksCallRest σ I sel)
        (by simp [endCageIlkVatIlksCallRest]) (by native_decide) (by jump_dest) rd9081
      have rd9097' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9097⟩
            [⟨0⟩, ⟨164⟩, endCageIlkVatIlksSelectorWord, endPackVatTarget σ I,
              endArg0Word I, ⟨562⟩, sel]
            (endCageIlkVatIlksReturnMem I out) (endCageIlkVatIlksCallAw aw)
            out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9081_taken_stack,
          endCageIlkVatIlksCallRest] using rd9097
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
      have rd9119 := endRuntimeBlocks.endRuntime_block_9097_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endCageIlkVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd9097'
      refine ⟨.ok (endCageIlkAfterVatIlksFrame I out) evm',
        Endpoint.reached (endCageIlkAfterVatIlksCursor I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endCageIlkAfterVatIlksCursor, endCageIlkAfterVatIlksAw,
            endRuntimeBlocks.endRuntime_block_9097_taken_stack] using rd9119⟩
      · exact ⟨rfl, rfl, hrel, hout, h160, rfl, rfl, rfl⟩
    · have hshort : out.size < 160 := by omega
      rw [endCageIlkExternalDecode_vatIlks_none_short hshort]
      intro rd
      have rd9081 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
            ((⟨1⟩ : UInt256) :: endCageIlkVatIlksCallRest σ I sel)
            (endCageIlkVatIlksReturnMem I out) (endCageIlkVatIlksCallAw aw)
            out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkVatIlksCallStack,
          endCageIlkVatIlksCallRest, endCageIlkVatIlksCallAw,
          endCageIlkVatIlksReturnMem] using rd
      have rd9097 := endRuntimeBlocks.endRuntime_block_9081_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkVatIlksCallRest σ I sel)
        (by simp [endCageIlkVatIlksCallRest]) (by native_decide) (by jump_dest) rd9081
      have rd9097' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9097⟩
            [⟨0⟩, ⟨164⟩, endCageIlkVatIlksSelectorWord, endPackVatTarget σ I,
              endArg0Word I, ⟨562⟩, sel]
            (endCageIlkVatIlksReturnMem I out) (endCageIlkVatIlksCallAw aw)
            out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9081_taken_stack,
          endCageIlkVatIlksCallRest] using rd9097
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
      have rd9115 := endRuntimeBlocks.endRuntime_block_9097_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endCageIlkVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd9097'
      exact endRuntimeBlocks.endRuntime_block_9115
        (R := endRuntimeBlocks.endRuntime_block_9097_fallthrough_stack
          (mem := endCageIlkVatIlksReturnMem I out) (rdata := out)
          (R := [endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_9097_fallthrough_stack])
        rd9115
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd9081 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9081⟩
          ((⟨0⟩ : UInt256) :: endCageIlkVatIlksCallRest σ I sel)
          (endCageIlkVatIlksReturnMem I out) (endCageIlkVatIlksCallAw aw)
          out world' k' C' := by
      simpa [gasCursor, callCursor, endCageIlkVatIlksCallStack,
        endCageIlkVatIlksCallRest, endCageIlkVatIlksCallAw,
        endCageIlkVatIlksReturnMem] using rd
    have rd9088 := endRuntimeBlocks.endRuntime_block_9081_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkVatIlksCallRest σ I sel)
      (by simp [endCageIlkVatIlksCallRest]) (by native_decide) rd9081
    exact endRuntimeBlocks.endRuntime_block_9088
      (R := endRuntimeBlocks.endRuntime_block_9081_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkVatIlksCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_9081_fallthrough_stack,
        endCageIlkVatIlksCallRest])
      rd9088

set_option maxHeartbeats 12000000 in
theorem endCageIlkSpotIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    {sel aw outVat rdata k C evm}
    (hsz36 : 36 ≤ I.calldata.size)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageIlkSpotIlksCallCursor world I sel aw outVat rdata)
      k C (endCageIlkAfterVatIlksFrame I outVat) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"] "spotIlk"
          (perm := false) ]
      (sequenceExit ⟨9255⟩
        (fun cur frame e =>
          frame = endCageIlkAfterSpotIlksFrame I outVat cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          64 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endCageIlkSpotIlksReturnMem I outVat cur.rdata),
              ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endCageIlkSpotIlksReturnMem I outVat cur.rdata ∧
          cur.aw = endCageIlkAfterSpotIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨9215⟩ = some (.GAS, .none); decide)
    (by simp [endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endCageIlkSpotTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨9216⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endCageIlkSpotIlksCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 6)
    rw [h.env] at hload
    rw [endEvalSpotAddress_cageIlk]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 6))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageIlkSpotTarget world.2 I).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rw [evalExprs?]
    rw [endEvalCageIlkIlkAfterVatIlks]
    rfl
  · intro _
    apply Fin.ext
    show (endCageIlkSpotTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endCageIlkSpotTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endCageIlkExternalEncode_spotIlks I hsz36]
    change some (endCageIlkSpotIlksEncodedCall I) =
      some ((endCageIlkSpotIlksCallMem I outVat).readWithPadding 128 36)
    rw [endCageIlkSpotIlksCallMem_readCallData I outVat houtVat h160Vat]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h64 : 64 ≤ out.size
    · rw [endCageIlkExternalDecode_spotIlks_ok h64]
      intro rd hrel
      have rd9217 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
            ((⟨1⟩ : UInt256) :: endCageIlkSpotIlksCallRest world.2 I sel)
            (endCageIlkSpotIlksReturnMem I outVat out)
            (endCageIlkSpotIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkSpotIlksCallCursor,
          endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest,
          endCageIlkSpotIlksCallAw, endCageIlkSpotIlksReturnMem] using rd
      have rd9233 := endRuntimeBlocks.endRuntime_block_9217_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkSpotIlksCallRest world.2 I sel)
        (by simp [endCageIlkSpotIlksCallRest]) (by native_decide) (by jump_dest) rd9217
      have rd9233' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9233⟩
            [⟨0⟩, ⟨164⟩, endCageIlkSpotIlksSelectorWord,
              endCageIlkSpotTarget world.2 I, ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkSpotIlksReturnMem I outVat out)
            (endCageIlkSpotIlksCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9217_taken_stack,
          endCageIlkSpotIlksCallRest] using rd9233
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
      have rd9255 := endRuntimeBlocks.endRuntime_block_9233_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endCageIlkSpotIlksSelectorWord)
        (x3 := endCageIlkSpotTarget world.2 I)
        (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd9233'
      refine ⟨.ok (endCageIlkAfterSpotIlksFrame I outVat out) evm',
        Endpoint.reached (endCageIlkAfterSpotIlksCursor I sel aw outVat out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endCageIlkAfterSpotIlksCursor, endCageIlkAfterSpotIlksAw,
            endRuntimeBlocks.endRuntime_block_9233_taken_stack] using rd9255⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h64, rfl, rfl, rfl⟩
    · have hshort : out.size < 64 := by omega
      rw [endCageIlkExternalDecode_spotIlks_none_short hshort]
      intro rd
      have rd9217 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
            ((⟨1⟩ : UInt256) :: endCageIlkSpotIlksCallRest world.2 I sel)
            (endCageIlkSpotIlksReturnMem I outVat out)
            (endCageIlkSpotIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkSpotIlksCallCursor,
          endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest,
          endCageIlkSpotIlksCallAw, endCageIlkSpotIlksReturnMem] using rd
      have rd9233 := endRuntimeBlocks.endRuntime_block_9217_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkSpotIlksCallRest world.2 I sel)
        (by simp [endCageIlkSpotIlksCallRest]) (by native_decide) (by jump_dest) rd9217
      have rd9233' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9233⟩
            [⟨0⟩, ⟨164⟩, endCageIlkSpotIlksSelectorWord,
              endCageIlkSpotTarget world.2 I, ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkSpotIlksReturnMem I outVat out)
            (endCageIlkSpotIlksCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9217_taken_stack,
          endCageIlkSpotIlksCallRest] using rd9233
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
      have rd9251 := endRuntimeBlocks.endRuntime_block_9233_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endCageIlkSpotIlksSelectorWord)
        (x3 := endCageIlkSpotTarget world.2 I)
        (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd9233'
      exact endRuntimeBlocks.endRuntime_block_9251
        (R := endRuntimeBlocks.endRuntime_block_9233_fallthrough_stack
          (mem := endCageIlkSpotIlksReturnMem I outVat out) (rdata := out)
          (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_9233_fallthrough_stack])
        rd9251
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd9217 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9217⟩
          ((⟨0⟩ : UInt256) :: endCageIlkSpotIlksCallRest world.2 I sel)
          (endCageIlkSpotIlksReturnMem I outVat out)
          (endCageIlkSpotIlksCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endCageIlkSpotIlksCallCursor,
        endCageIlkSpotIlksCallStack, endCageIlkSpotIlksCallRest,
        endCageIlkSpotIlksCallAw, endCageIlkSpotIlksReturnMem] using rd
    have rd9224 := endRuntimeBlocks.endRuntime_block_9217_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkSpotIlksCallRest world.2 I sel)
      (by simp [endCageIlkSpotIlksCallRest]) (by native_decide) rd9217
    exact endRuntimeBlocks.endRuntime_block_9224
      (R := endRuntimeBlocks.endRuntime_block_9217_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkSpotIlksCallRest world.2 I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_9217_fallthrough_stack,
        endCageIlkSpotIlksCallRest])
      rd9224

/-! ## `spot.par()` after `spot.ilks` -/

abbrev endCageIlkPipValue (outSpot : ByteArray) : Value :=
  .address (AccountAddress.ofNat (endCageIlkSpotIlksPipWord outSpot).toNat)

abbrev endCageIlkAfterPipFrame (I : ExecutionEnv) (outVat outSpot : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endCageIlkAfterSpotIlksFrame I outVat outSpot).locals.insert "pip"
      (endCageIlkPipValue outSpot) }

theorem endEvalCageIlkSpotIlkPip (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot : ByteArray) :
    evalExpr? config (endCageIlkAfterSpotIlksFrame I outVat outSpot) evm
      (.tupleGet (.var "spotIlk") 0) =
      .ok (endCageIlkPipValue outSpot) := by
  simp [evalExpr?, endCageIlkAfterSpotIlksFrame, collapseReturns, tupleGetValue?,
    endCageIlkSpotIlksValues, endCageIlkPipValue, EvalResult.ofOption,
    EvalResult.bind, bind]

theorem endLetCageIlkPip (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot : ByteArray) :
    ExecStmt config (endCageIlkAfterSpotIlksFrame I outVat outSpot) evm
      (.letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0))
      (.ok (endCageIlkAfterPipFrame I outVat outSpot) evm) := by
  simpa [endCageIlkAfterPipFrame] using
    ExecStmt.letDecl (endEvalCageIlkSpotIlkPip evm I outVat outSpot)

theorem endEvalSpotAddress_cageIlk_afterPip (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot : ByteArray) :
    evalExpr? config (endCageIlkAfterPipFrame I outVat outSpot) evm (.storage spotRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask).toNat)) := by
  have hbase :
      (endCageIlkAfterPipFrame I outVat outSpot).locals.get? spotRef.base = none := by
    simp [endCageIlkAfterPipFrame, endCageIlkAfterSpotIlksFrame,
      endCageIlkAfterVatIlksFrame, endCageIlkStore, endFreeStore, spotRef]
  have her :
      evalStorageRef config (endCageIlkAfterPipFrame I outVat outSpot) evm spotRef =
        .ok { base := "spot", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind]
  have hty :
      storageTypeAt? (endCageIlkAfterPipFrame I outVat outSpot).contract.storage
          { base := "spot", steps := [] } =
        some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt]
  have hloc :
      config.storage.layout { base := "spot", steps := [] } =
        fun _ => some (addrLoc (UInt256.ofNat 6)) := by
    rw [show UInt256.ofNat 6 = (⟨6⟩ : UInt256) from by native_decide]
    exact endConfig_storage_spot
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc), endRuntimeStorageLocLoad_address_offset0]

theorem endEvalSpotExtCodeSize_cageIlk_afterPip (evm : EVM.State)
    (I : ExecutionEnv) (outVat outSpot : ByteArray) :
    evalExpr? config (endCageIlkAfterPipFrame I outVat outSpot) evm
        (.extCodeSize (.storage spotRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalSpotAddress_cageIlk_afterPip evm I outVat outSpot]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases hacc : evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask).toNat) with
  | none =>
      simp [extCodeSizeWord, State.lookupAccount,
        accountAddress_ofUInt256_eq_ofNat_toNat, hacc]
      change EvalResult.ok (Value.int 0) = EvalResult.ok (Value.int 0)
      rfl
  | some acc =>
      simp [extCodeSizeWord, State.lookupAccount,
        accountAddress_ofUInt256_eq_ofNat_toNat, hacc]
      change EvalResult.ok
          (Value.int (Int.ofNat (UInt256.ofNat acc.code.size).toNat)) =
        EvalResult.ok
          (Value.int (Int.ofNat (UInt256.ofNat acc.code.size).toNat))
      rfl

theorem endEvalSpotCodeGuard_cageIlk_afterPip_true (evm : EVM.State)
    (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endCageIlkAfterPipFrame I outVat outSpot) evm
      (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSpotExtCodeSize_cageIlk_afterPip evm I outVat outSpot]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalSpotCodeGuard_cageIlk_afterPip_false (evm : EVM.State)
    (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 6))
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endCageIlkAfterPipFrame I outVat outSpot) evm
      (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalSpotExtCodeSize_cageIlk_afterPip evm I outVat outSpot, hnocode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endCageIlkSpotIlksMemSel_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksMemSel I out).size = 288 := by
  unfold endCageIlkSpotIlksMemSel
  exact toByteArray_write32_size_of_le (endCageIlkArtHashMem I out)
    endCageIlkSpotIlksSelectorEncodedWord 128 288 288
    (endCageIlkArtHashMem_size I out hout h160)
    (by rw [endCageIlkArtHashMem_size I out hout h160]; omega)
    (by omega)

theorem endCageIlkSpotIlksCallMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endCageIlkSpotIlksCallMem I out).size = 288 := by
  rw [endCageIlkSpotIlksCallMem_eq_full I out hout h160]
  unfold endCageIlkSpotIlksMemFull
  exact toByteArray_write32_size_of_le (endCageIlkSpotIlksMemSel I out)
    (endArg0Word I) 132 288 288
    (endCageIlkSpotIlksMemSel_size I out hout h160)
    (by rw [endCageIlkSpotIlksMemSel_size I out hout h160]; omega)
    (by omega)

theorem endCageIlkSpotIlksOutputFacts (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    CallOutputFacts (endCageIlkSpotIlksCallMem I outVat) outSpot
      (⟨128⟩ : UInt256) (⟨64⟩ : UInt256) := by
  exact callOutputFacts (endCageIlkSpotIlksCallMem I outVat) outSpot
    (⟨128⟩ : UInt256) (⟨64⟩ : UInt256) houtSpot
    (by rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat]; decide)

theorem endCageIlkSpotIlksReturnMem_size (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    (endCageIlkSpotIlksReturnMem I outVat outSpot).size =
      (endCageIlkSpotIlksCallMem I outVat).size := by
  have hf := endCageIlkSpotIlksOutputFacts I outVat outSpot houtVat h160Vat houtSpot
  simpa [endCageIlkSpotIlksReturnMem] using hf.size

theorem endCageIlkSpotIlksReturnMem_read64 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    (endCageIlkSpotIlksReturnMem I outVat outSpot).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hf := endCageIlkSpotIlksOutputFacts I outVat outSpot houtVat h160Vat houtSpot
  simpa [endCageIlkSpotIlksReturnMem,
    endCageIlkSpotIlksCallMem_read64 I outVat houtVat h160Vat] using
    hf.readBelow 64 (by decide)

theorem endCageIlkSpotIlksReturnMem_mload64 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat outSpot) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkSpotIlksReturnMem I outVat outSpot)
    (by
      rw [endCageIlkSpotIlksReturnMem_size I outVat outSpot houtVat h160Vat houtSpot]
      rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat]
      omega)
    (endCageIlkSpotIlksReturnMem_read64 I outVat outSpot houtVat h160Vat houtSpot)

theorem endCageIlkSpotIlksReturnMem_read128 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (h64Spot : 64 ≤ outSpot.size) :
    (endCageIlkSpotIlksReturnMem I outVat outSpot).readWithPadding 128 32 =
      outSpot.extract 0 32 := by
  have hf := endCageIlkSpotIlksOutputFacts I outVat outSpot houtVat h160Vat houtSpot
  simpa [endCageIlkSpotIlksReturnMem] using
    hf.readWord (by decide) (by omega)

theorem endCageIlkSpotIlksReturnMem_mload128 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (h64Spot : 64 ≤ outSpot.size) :
    memLoad (⟨128⟩ : UInt256) (endCageIlkSpotIlksReturnMem I outVat outSpot) =
      endCageIlkSpotIlksPipWord outSpot := by
  unfold memLoad
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endCageIlkSpotIlksReturnMem_size I outVat outSpot houtVat h160Vat houtSpot]
    rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat]
    omega)]
  rw [endCageIlkSpotIlksReturnMem_read128 I outVat outSpot houtVat h160Vat houtSpot h64Spot]
  change UInt256.ofNat (fromByteArrayBigEndian (outSpot.extract 0 32)) =
    ABI.bytesToWord (outSpot.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

abbrev endCageIlkParWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endCageIlkParValues (out : ByteArray) : List Value :=
  [endCageIlkUIntValue (endCageIlkParWord out)]

abbrev endCageIlkParSelectorWord : UInt256 := UInt256.ofNat 1230844619

abbrev endCageIlkParSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft endCageIlkParSelectorWord (UInt256.ofNat 224)

abbrev endCageIlkParCallMem (I : ExecutionEnv) (outVat outSpot : ByteArray) :
    ByteArray :=
  endRuntimeBlocks.endRuntime_block_9255_taken_memory
    (mem := endCageIlkSpotIlksReturnMem I outVat outSpot)

theorem endCageIlkParSelectorEncodedWord_prefix :
    (endCageIlkParSelectorEncodedWord.toByteArray).extract 0 4 = parSelector := by
  native_decide

theorem endCageIlkExternalEncode_par :
    config.externalABI.encode? "par" [] = some parSelector := by
  simp [config, externalABI]

theorem endCageIlkExternalDecode_par_ok {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "par" out =
      some (endCageIlkParValues out) := by
  simp [config, externalABI, decodeReturn?, endCageIlkParValues, endCageIlkParWord,
    endCageIlkUIntValue, uint256, uint256Int, abiUInt256,
    decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) h32]
  rw [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt h32)]

theorem endCageIlkExternalDecode_par_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "par" out = none := by
  simp [config, externalABI, decodeReturn?, uint256, uint256Int, abiUInt256,
    decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]

theorem endCageIlkParCallMem_size_ge160 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    160 ≤ (endCageIlkParCallMem I outVat outSpot).size := by
  unfold endCageIlkParCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9255_taken_memory]
  rw [endCageIlkSpotIlksReturnMem_mload64 I outVat outSpot houtVat h160Vat houtSpot]
  exact toByteArray_write_size_ge_off_add32_unbounded
    endCageIlkParSelectorEncodedWord (endCageIlkSpotIlksReturnMem I outVat outSpot) 128

theorem endCageIlkParCallMem_read64 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    (endCageIlkParCallMem I outVat outSpot).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkParCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9255_taken_memory]
  rw [endCageIlkSpotIlksReturnMem_mload64 I outVat outSpot houtVat h160Vat houtSpot]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endCageIlkParSelectorEncodedWord
    (endCageIlkSpotIlksReturnMem I outVat outSpot) 128 64
    (by
      rw [endCageIlkSpotIlksReturnMem_size I outVat outSpot houtVat h160Vat houtSpot]
      rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat]
      omega)
    (by omega)]
  exact endCageIlkSpotIlksReturnMem_read64 I outVat outSpot houtVat h160Vat houtSpot

theorem endCageIlkParCallMem_mload64 (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkParCallMem I outVat outSpot) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkParCallMem I outVat outSpot)
    (by have := endCageIlkParCallMem_size_ge160 I outVat outSpot houtVat h160Vat houtSpot; omega)
    (endCageIlkParCallMem_read64 I outVat outSpot houtVat h160Vat houtSpot)

theorem endCageIlkParCallMem_readCallData (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    (endCageIlkParCallMem I outVat outSpot).readWithPadding 128 4 = parSelector := by
  unfold endCageIlkParCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9255_taken_memory]
  rw [endCageIlkSpotIlksReturnMem_mload64 I outVat outSpot houtVat h160Vat houtSpot]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endCageIlkParSelectorEncodedWord
    (endCageIlkSpotIlksReturnMem I outVat outSpot) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endCageIlkParSelectorEncodedWord_prefix]

abbrev endCageIlkParCallRest (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outSpot : ByteArray) : List UInt256 :=
  [⟨132⟩, endCageIlkParSelectorWord, endCageIlkSpotTarget σ I, ⟨9490⟩,
    endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]

abbrev endCageIlkParCallStack (σ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outSpot : ByteArray) : List UInt256 :=
  [endCageIlkSpotTarget σ I, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩] ++
    endCageIlkParCallRest σ I sel outSpot

abbrev endCageIlkParCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outVat outSpot rdata : ByteArray) : Cursor :=
  { pc := ⟨9335⟩, stack := endCageIlkParCallStack world.2 I sel outSpot,
    mem := endCageIlkParCallMem I outVat outSpot, aw := aw, rdata := rdata,
    world := world }

abbrev endCageIlkParCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev endCageIlkParReturnMem (I : ExecutionEnv) (outVat outSpot outPar : ByteArray) :
    ByteArray :=
  outPar.write 0 (endCageIlkParCallMem I outVat outSpot) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat outPar.size)).toNat

abbrev endCageIlkAfterParAw (aw : UInt256) : UInt256 :=
  M (endCageIlkParCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endCageIlkAfterParFrame (I : ExecutionEnv) (outVat outSpot outPar : ByteArray) :
    Frame :=
  { contract := contract,
    locals := (endCageIlkAfterPipFrame I outVat outSpot).locals.insert "parV"
      (collapseReturns (endCageIlkParValues outPar)) }

abbrev endCageIlkAfterParCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outVat outSpot outPar : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨9375⟩,
    stack := [UInt256.ofNat outPar.size,
      memLoad (UInt256.ofNat 64) (endCageIlkParReturnMem I outVat outSpot outPar),
      ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel],
    mem := endCageIlkParReturnMem I outVat outSpot outPar,
    aw := endCageIlkAfterParAw aw,
    rdata := outPar,
    world := world }

theorem endCageIlkParSetupStack_eq
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (outVat outSpot : ByteArray) (sel : UInt256)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (h64Spot : 64 ≤ outSpot.size) :
    endRuntimeBlocks.endRuntime_block_9255_taken_stack (ee := I)
        (mem := endCageIlkSpotIlksReturnMem I outVat outSpot) (σ := world.2)
        (x1 := memLoad (UInt256.ofNat 64)
          (endCageIlkSpotIlksReturnMem I outVat outSpot))
        (R := [endArg0Word I, ⟨562⟩, sel]) =
      UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I)) ::
        endCageIlkParCallStack world.2 I sel outSpot := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hretFree :=
    endCageIlkSpotIlksReturnMem_mload64 I outVat outSpot houtVat h160Vat houtSpot
  have hparFree :=
    endCageIlkParCallMem_mload64 I outVat outSpot houtVat h160Vat houtSpot
  have hparFreeRaw :
      memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 1230844619).shiftLeft (UInt256.ofNat 224)).toByteArray.write
            0 (endCageIlkSpotIlksReturnMem I outVat outSpot)
            (⟨128⟩ : UInt256).toNat 32) =
        ⟨128⟩ := by
    simpa [endCageIlkParCallMem, endCageIlkParSelectorEncodedWord,
      endCageIlkParSelectorWord, endRuntimeBlocks.endRuntime_block_9255_taken_memory,
      hretFree] using hparFree
  have hpip :=
    endCageIlkSpotIlksReturnMem_mload128 I outVat outSpot houtVat h160Vat
      houtSpot h64Spot
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 4 = ⟨4⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 4 = ⟨132⟩ := by
    native_decide
  dsimp [endRuntimeBlocks.endRuntime_block_9255_taken_stack,
    endCageIlkParCallStack, endCageIlkParCallRest, endCageIlkParCallMem,
    endCageIlkParSelectorWord, endCageIlkParSelectorEncodedWord, endCageIlkSpotTarget]
  rw [hretFree, hparFreeRaw, hpip, hmaskGenerated, hlen, hend]
  rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from by native_decide,
    show UInt256.ofNat 9490 = (⟨9490⟩ : UInt256) from by native_decide]

theorem endX_cageIlk_par_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hspotNoCode :
      extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) = ⟨0⟩)
    (rd9255 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9255⟩
      (endCageIlkAfterSpotIlksCursor I sel aw outVat outSpot world).stack
      (endCageIlkSpotIlksReturnMem I outVat outSpot) (endCageIlkAfterSpotIlksAw aw)
      outSpot world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hspotNoCode]
    decide
  obtain ⟨_, _, rd9329⟩ := endRuntimeBlocks.endRuntime_block_9255_fallthrough
    (x0 := UInt256.ofNat outSpot.size)
    (x1 := memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat outSpot))
    (x2 := (⟨0⟩ : UInt256)) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hcond
    (by simpa [endCageIlkAfterSpotIlksCursor] using rd9255)
  exact endRuntimeBlocks.endRuntime_block_9329
    (R := endRuntimeBlocks.endRuntime_block_9255_fallthrough_stack (ee := I)
      (mem := endCageIlkSpotIlksReturnMem I outVat outSpot) (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat outSpot))
      (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_9255_fallthrough_stack])
    rd9329

theorem endX_cageIlk_to_par_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hspotCode :
      extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I) ≠ ⟨0⟩)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (h64Spot : 64 ≤ outSpot.size)
    (rd9255 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9255⟩
      (endCageIlkAfterSpotIlksCursor I sel aw outVat outSpot world).stack
      (endCageIlkSpotIlksReturnMem I outVat outSpot) (endCageIlkAfterSpotIlksAw aw)
      outSpot world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9335⟩
      (endCageIlkParCallStack world.2 I sel outSpot)
      (endCageIlkParCallMem I outVat outSpot) aw' outSpot world k' C' := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hspotCode]
    native_decide
  obtain ⟨aw9333, k9333, C9333, rd9333⟩ :=
    endRuntimeBlocks.endRuntime_block_9255_taken_packed
      (x0 := UInt256.ofNat outSpot.size)
      (x1 := memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat outSpot))
      (x2 := (⟨0⟩ : UInt256)) (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest)
      (by simpa [endCageIlkAfterSpotIlksCursor] using rd9255)
  have rd9333' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9333⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I)) ::
          endCageIlkParCallStack world.2 I sel outSpot)
        (endCageIlkParCallMem I outVat outSpot) aw9333 outSpot world k9333 C9333 := by
    simpa [endCageIlkParCallMem,
      endCageIlkParSetupStack_eq world I outVat outSpot sel houtVat h160Vat
        houtSpot h64Spot] using rd9333
  exact endRuntimeBlocks.endRuntime_block_9333_packed
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endCageIlkSpotTarget world.2 I)))
    (R := endCageIlkParCallStack world.2 I sel outSpot)
    (by simp [endCageIlkParCallStack, endCageIlkParCallRest])
    rd9333'

set_option maxHeartbeats 12000000 in
theorem endCageIlkParExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    {sel aw outVat outSpot rdata k C evm}
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageIlkParCallCursor world I sel aw outVat outSpot rdata)
      k C (endCageIlkAfterPipFrame I outVat outSpot) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV" (perm := false) ]
      (sequenceExit ⟨9375⟩
        (fun cur frame e =>
          frame = endCageIlkAfterParFrame I outVat outSpot cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endCageIlkParReturnMem I outVat outSpot cur.rdata),
              ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endCageIlkParReturnMem I outVat outSpot cur.rdata ∧
          cur.aw = endCageIlkAfterParAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨9335⟩ = some (.GAS, .none); decide)
    (by simp [endCageIlkParCallStack, endCageIlkParCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endCageIlkSpotTarget world.2 I).toNat)
    (argVals := [])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨9336⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endCageIlkParCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 6)
    rw [h.env] at hload
    rw [endEvalSpotAddress_cageIlk_afterPip]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 6))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endCageIlkSpotTarget world.2 I).toNat))
    rw [hload]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rw [evalExprs?]
    rfl
  · intro _
    apply Fin.ext
    show (endCageIlkSpotTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endCageIlkSpotTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endCageIlkExternalEncode_par]
    change some parSelector =
      some ((endCageIlkParCallMem I outVat outSpot).readWithPadding 128 4)
    rw [endCageIlkParCallMem_readCallData I outVat outSpot houtVat h160Vat houtSpot]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h32 : 32 ≤ out.size
    · rw [endCageIlkExternalDecode_par_ok h32]
      intro rd hrel
      have rd9337 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
            ((⟨1⟩ : UInt256) :: endCageIlkParCallRest world.2 I sel outSpot)
            (endCageIlkParReturnMem I outVat outSpot out)
            (endCageIlkParCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkParCallCursor,
          endCageIlkParCallStack, endCageIlkParCallRest,
          endCageIlkParCallAw, endCageIlkParReturnMem] using rd
      have rd9353 := endRuntimeBlocks.endRuntime_block_9337_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkParCallRest world.2 I sel outSpot)
        (by simp [endCageIlkParCallRest]) (by native_decide) (by jump_dest) rd9337
      have rd9353' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9353⟩
            [⟨0⟩, ⟨132⟩, endCageIlkParSelectorWord,
              endCageIlkSpotTarget world.2 I, ⟨9490⟩,
              endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkParReturnMem I outVat outSpot out)
            (endCageIlkParCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9337_taken_stack,
          endCageIlkParCallRest] using rd9353
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact h32
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd9375 := endRuntimeBlocks.endRuntime_block_9353_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨132⟩)
        (x2 := endCageIlkParSelectorWord)
        (x3 := endCageIlkSpotTarget world.2 I)
        (R := [⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
          endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd9353'
      refine ⟨.ok (endCageIlkAfterParFrame I outVat outSpot out) evm',
        Endpoint.reached (endCageIlkAfterParCursor I sel aw outVat outSpot out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endCageIlkAfterParCursor, endCageIlkAfterParAw,
            endRuntimeBlocks.endRuntime_block_9353_taken_stack] using rd9375⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h32, rfl, rfl, rfl⟩
    · have hshort : out.size < 32 := by omega
      rw [endCageIlkExternalDecode_par_none_short hshort]
      intro rd
      have rd9337 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
            ((⟨1⟩ : UInt256) :: endCageIlkParCallRest world.2 I sel outSpot)
            (endCageIlkParReturnMem I outVat outSpot out)
            (endCageIlkParCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkParCallCursor,
          endCageIlkParCallStack, endCageIlkParCallRest,
          endCageIlkParCallAw, endCageIlkParReturnMem] using rd
      have rd9353 := endRuntimeBlocks.endRuntime_block_9337_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkParCallRest world.2 I sel outSpot)
        (by simp [endCageIlkParCallRest]) (by native_decide) (by jump_dest) rd9337
      have rd9353' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9353⟩
            [⟨0⟩, ⟨132⟩, endCageIlkParSelectorWord,
              endCageIlkSpotTarget world.2 I, ⟨9490⟩,
              endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkParReturnMem I outVat outSpot out)
            (endCageIlkParCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9337_taken_stack,
          endCageIlkParCallRest] using rd9353
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd9371 := endRuntimeBlocks.endRuntime_block_9353_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨132⟩)
        (x2 := endCageIlkParSelectorWord)
        (x3 := endCageIlkSpotTarget world.2 I)
        (R := [⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
          endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd9353'
      exact endRuntimeBlocks.endRuntime_block_9371
        (R := endRuntimeBlocks.endRuntime_block_9353_fallthrough_stack
          (mem := endCageIlkParReturnMem I outVat outSpot out) (rdata := out)
          (R := [⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
            endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_9353_fallthrough_stack])
        rd9371
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd9337 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9337⟩
          ((⟨0⟩ : UInt256) :: endCageIlkParCallRest world.2 I sel outSpot)
          (endCageIlkParReturnMem I outVat outSpot out)
          (endCageIlkParCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endCageIlkParCallCursor,
        endCageIlkParCallStack, endCageIlkParCallRest,
        endCageIlkParCallAw, endCageIlkParReturnMem] using rd
    have rd9344 := endRuntimeBlocks.endRuntime_block_9337_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkParCallRest world.2 I sel outSpot)
      (by simp [endCageIlkParCallRest]) (by native_decide) rd9337
    exact endRuntimeBlocks.endRuntime_block_9344
      (R := endRuntimeBlocks.endRuntime_block_9337_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkParCallRest world.2 I sel outSpot))
      (by simp [endRuntimeBlocks.endRuntime_block_9337_fallthrough_stack,
        endCageIlkParCallRest])
      rd9344

/-! ## `pip.read()` after `spot.par()` -/

abbrev endCageIlkReadTarget (outSpot : ByteArray) : UInt256 :=
  UInt256.land (endCageIlkSpotIlksPipWord outSpot) solcAddrMask

abbrev endCageIlkReadValue (out : ByteArray) : Value :=
  .fixedBytes bytes32Width (out.toList.take 32)

abbrev endCageIlkReadValues (out : ByteArray) : List Value :=
  [endCageIlkReadValue out]

abbrev endCageIlkReadSelectorWord : UInt256 := UInt256.ofNat 1474176676

abbrev endCageIlkReadSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 368544169) (UInt256.ofNat 226)

theorem endCageIlkPipValue_eq_masked (outSpot : ByteArray) :
    endCageIlkPipValue outSpot =
      .address (AccountAddress.ofNat (endCageIlkReadTarget outSpot).toNat) := by
  unfold endCageIlkPipValue endCageIlkReadTarget
  exact congrArg Value.address (by
    apply Fin.ext
    change (endCageIlkSpotIlksPipWord outSpot).toNat % AccountAddress.size =
      (UInt256.land (endCageIlkSpotIlksPipWord outSpot) solcAddrMask).toNat %
        AccountAddress.size
    rw [u256_land_toNat]
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    change (endCageIlkSpotIlksPipWord outSpot).toNat % AccountAddress.size =
      (endCageIlkSpotIlksPipWord outSpot).toNat % AccountAddress.size %
        UInt256.size % AccountAddress.size
    have hltAddr :
        (endCageIlkSpotIlksPipWord outSpot).toNat % AccountAddress.size <
          AccountAddress.size :=
      Nat.mod_lt _ (by native_decide)
    have hltWord :
        (endCageIlkSpotIlksPipWord outSpot).toNat % AccountAddress.size <
          UInt256.size :=
      lt_trans hltAddr (by native_decide)
    rw [Nat.mod_eq_of_lt hltWord, Nat.mod_eq_of_lt hltAddr])

theorem endCageIlkAfterParFrame_get_pip (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray) :
    (endCageIlkAfterParFrame I outVat outSpot outPar).locals.get? "pip" =
      some (endCageIlkPipValue outSpot) := by
  change ((endCageIlkAfterPipFrame I outVat outSpot).locals.insert "parV"
      (collapseReturns (endCageIlkParValues outPar))).get? "pip" =
    some (endCageIlkPipValue outSpot)
  rw [store_get_ne (endCageIlkAfterPipFrame I outVat outSpot).locals
    (k := "parV") (a := "pip") (collapseReturns (endCageIlkParValues outPar))
    (by decide)]
  exact store_get_self (endCageIlkAfterSpotIlksFrame I outVat outSpot).locals
    "pip" (endCageIlkPipValue outSpot)

theorem endEvalCageIlkPip_afterPar (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray) :
    evalExpr? config (endCageIlkAfterParFrame I outVat outSpot outPar) evm
      (.var "pip") = .ok (endCageIlkPipValue outSpot) := by
  rw [evalExpr?]
  rw [endCageIlkAfterParFrame_get_pip]
  rfl

theorem endCageIlkDecodeReturnValue_read_ok {out : ByteArray} (h32 : 32 ≤ out.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 bytes32 out =
      some (endCageIlkReadValue out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlist : 32 ≤ out.toList.length := by omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  simp [abiTupleHeadSize?, bytes32, bytes32Width, decodeABIValues?,
    isDynamicABIType, staticABIEncodedSize?, decodeABIValue?, readBytes?,
    endCageIlkReadValue, hlist, List.take_take]

theorem endCageIlkDecodeReturnValue_read_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 bytes32 out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlist : ¬ 32 ≤ out.toList.length := by omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  simp [abiTupleHeadSize?, bytes32, bytes32Width, decodeABIValues?,
    isDynamicABIType, staticABIEncodedSize?, decodeABIValue?, readBytes?, hlist]

theorem endCageIlkExternalEncode_read :
    config.externalABI.encode? "read" [] = some readSelector := by
  simp [config, externalABI]

theorem endCageIlkExternalDecode_read_ok {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "read" out =
      some (endCageIlkReadValues out) := by
  simp [config, externalABI, decodeReturn?, endCageIlkReadValues,
    endCageIlkDecodeReturnValue_read_ok h32]

theorem endCageIlkExternalDecode_read_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "read" out = none := by
  simp [config, externalABI, decodeReturn?,
    endCageIlkDecodeReturnValue_read_none_short hshort]

theorem endCageIlkParCallMem_size (I : ExecutionEnv) (outVat outSpot : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) :
    (endCageIlkParCallMem I outVat outSpot).size = 288 := by
  unfold endCageIlkParCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9255_taken_memory]
  rw [endCageIlkSpotIlksReturnMem_mload64 I outVat outSpot houtVat h160Vat houtSpot]
  exact toByteArray_write32_size_of_le (endCageIlkSpotIlksReturnMem I outVat outSpot)
    endCageIlkParSelectorEncodedWord 128 288 288
    (by
      rw [endCageIlkSpotIlksReturnMem_size I outVat outSpot houtVat h160Vat houtSpot]
      rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat])
    (by
      rw [endCageIlkSpotIlksReturnMem_size I outVat outSpot houtVat h160Vat houtSpot]
      rw [endCageIlkSpotIlksCallMem_size I outVat houtVat h160Vat]
      omega)
    (by omega)

theorem endCageIlkParOutputFacts (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size) :
    CallOutputFacts (endCageIlkParCallMem I outVat outSpot) outPar
      (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) := by
  exact callOutputFacts (endCageIlkParCallMem I outVat outSpot) outPar
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) houtPar
    (by rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot]; decide)

theorem endCageIlkParReturnMem_size (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size) :
    (endCageIlkParReturnMem I outVat outSpot outPar).size =
      (endCageIlkParCallMem I outVat outSpot).size := by
  have hf := endCageIlkParOutputFacts I outVat outSpot outPar
    houtVat h160Vat houtSpot houtPar
  simpa [endCageIlkParReturnMem] using hf.size

theorem endCageIlkParReturnMem_read64 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size) :
    (endCageIlkParReturnMem I outVat outSpot outPar).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hf := endCageIlkParOutputFacts I outVat outSpot outPar
    houtVat h160Vat houtSpot houtPar
  simpa [endCageIlkParReturnMem,
    endCageIlkParCallMem_read64 I outVat outSpot houtVat h160Vat houtSpot] using
    hf.readBelow 64 (by decide)

theorem endCageIlkParReturnMem_mload64 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkParReturnMem I outVat outSpot outPar) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkParReturnMem I outVat outSpot outPar)
    (by
      rw [endCageIlkParReturnMem_size I outVat outSpot outPar houtVat h160Vat
        houtSpot houtPar]
      rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot]
      omega)
    (endCageIlkParReturnMem_read64 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar)

theorem endCageIlkParReturnMem_read128 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    (endCageIlkParReturnMem I outVat outSpot outPar).readWithPadding 128 32 =
      outPar.extract 0 32 := by
  have hf := endCageIlkParOutputFacts I outVat outSpot outPar
    houtVat h160Vat houtSpot houtPar
  simpa [endCageIlkParReturnMem] using
    hf.readWord (by decide) h32Par

theorem endCageIlkParReturnMem_mload128 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    memLoad (⟨128⟩ : UInt256) (endCageIlkParReturnMem I outVat outSpot outPar) =
      endCageIlkParWord outPar := by
  unfold memLoad
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endCageIlkParReturnMem_size I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar]
    rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot]
    omega)]
  rw [endCageIlkParReturnMem_read128 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar h32Par]

abbrev endCageIlkReadCallMem (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_9375_taken_memory
    (mem := endCageIlkParReturnMem I outVat outSpot outPar)

theorem endCageIlkReadSelectorEncodedWord_prefix :
    (endCageIlkReadSelectorEncodedWord.toByteArray).extract 0 4 = readSelector := by
  native_decide

theorem endCageIlkReadCallMem_size_ge160 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    160 ≤ (endCageIlkReadCallMem I outVat outSpot outPar).size := by
  unfold endCageIlkReadCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9375_taken_memory]
  rw [endCageIlkParReturnMem_mload64 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar]
  exact toByteArray_write_size_ge_off_add32_unbounded
    endCageIlkReadSelectorEncodedWord (endCageIlkParReturnMem I outVat outSpot outPar) 128

theorem endCageIlkReadCallMem_read64 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    (endCageIlkReadCallMem I outVat outSpot outPar).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageIlkReadCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9375_taken_memory]
  rw [endCageIlkParReturnMem_mload64 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endCageIlkReadSelectorEncodedWord
    (endCageIlkParReturnMem I outVat outSpot outPar) 128 64
    (by
      rw [endCageIlkParReturnMem_size I outVat outSpot outPar houtVat h160Vat
        houtSpot houtPar]
      rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot]
      omega)
    (by omega)]
  exact endCageIlkParReturnMem_read64 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar

theorem endCageIlkReadCallMem_mload64 (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkReadCallMem I outVat outSpot outPar) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkReadCallMem I outVat outSpot outPar)
    (by
      have hge := endCageIlkReadCallMem_size_ge160 I outVat outSpot outPar
        houtVat h160Vat houtSpot houtPar h32Par
      omega)
    (endCageIlkReadCallMem_read64 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar h32Par)

theorem endCageIlkReadCallMem_readCallData (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    (endCageIlkReadCallMem I outVat outSpot outPar).readWithPadding 128 4 =
      readSelector := by
  unfold endCageIlkReadCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9375_taken_memory]
  rw [endCageIlkParReturnMem_mload64 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endCageIlkReadSelectorEncodedWord
    (endCageIlkParReturnMem I outVat outSpot outPar) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endCageIlkReadSelectorEncodedWord_prefix]

abbrev endCageIlkReadCallRest (I : ExecutionEnv) (sel : UInt256)
    (outSpot outPar : ByteArray) : List UInt256 :=
  [⟨132⟩, endCageIlkReadSelectorWord, endCageIlkReadTarget outSpot,
    endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
    endArg0Word I, ⟨562⟩, sel]

abbrev endCageIlkReadCallStack (I : ExecutionEnv) (sel : UInt256)
    (outSpot outPar : ByteArray) : List UInt256 :=
  [endCageIlkReadTarget outSpot, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩] ++
    endCageIlkReadCallRest I sel outSpot outPar

abbrev endCageIlkReadCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outVat outSpot outPar rdata : ByteArray) : Cursor :=
  { pc := ⟨9443⟩, stack := endCageIlkReadCallStack I sel outSpot outPar,
    mem := endCageIlkReadCallMem I outVat outSpot outPar, aw := aw, rdata := rdata,
    world := world }

abbrev endCageIlkReadCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨4⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev endCageIlkReadReturnMem (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) : ByteArray :=
  outRead.write 0 (endCageIlkReadCallMem I outVat outSpot outPar) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat outRead.size)).toNat

abbrev endCageIlkAfterReadAw (aw : UInt256) : UInt256 :=
  M (endCageIlkReadCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endCageIlkAfterReadFrame (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) : Frame :=
  { contract := contract,
    locals := (endCageIlkAfterParFrame I outVat outSpot outPar).locals.insert "pipRead"
      (collapseReturns (endCageIlkReadValues outRead)) }

abbrev endCageIlkAfterReadCursor (I : ExecutionEnv) (sel aw : UInt256)
    (outVat outSpot outPar outRead : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨9483⟩,
    stack := [UInt256.ofNat outRead.size,
      memLoad (UInt256.ofNat 64) (endCageIlkReadReturnMem I outVat outSpot outPar outRead),
      endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
      endArg0Word I, ⟨562⟩, sel],
    mem := endCageIlkReadReturnMem I outVat outSpot outPar outRead,
    aw := endCageIlkAfterReadAw aw,
    rdata := outRead,
    world := world }

theorem endCageIlkReadSetupStack_eq
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (outVat outSpot outPar : ByteArray) (sel : UInt256)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    endRuntimeBlocks.endRuntime_block_9375_taken_stack
        (mem := endCageIlkParReturnMem I outVat outSpot outPar) (σ := world.2)
        (x1 := memLoad (UInt256.ofNat 64)
          (endCageIlkParReturnMem I outVat outSpot outPar))
        (x2 := ⟨9490⟩) (x3 := endCageIlkSpotIlksPipWord outSpot)
        (R := [endArg0Word I, ⟨562⟩, sel]) =
      UInt256.isZero (extCodeSizeWord world.2 (endCageIlkReadTarget outSpot)) ::
        endCageIlkReadCallStack I sel outSpot outPar := by
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hparFree :=
    endCageIlkParReturnMem_mload64 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar
  have hreadFree :=
    endCageIlkReadCallMem_mload64 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar h32Par
  have hreadFreeRaw :
      memLoad (UInt256.ofNat 64)
          (((UInt256.ofNat 368544169).shiftLeft (UInt256.ofNat 226)).toByteArray.write
            0 (endCageIlkParReturnMem I outVat outSpot outPar)
            (⟨128⟩ : UInt256).toNat 32) =
        ⟨128⟩ := by
    simpa [endCageIlkReadCallMem, endCageIlkReadSelectorEncodedWord,
      endRuntimeBlocks.endRuntime_block_9375_taken_memory, hparFree] using hreadFree
  have hparWord :=
    endCageIlkParReturnMem_mload128 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar h32Par
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 4 = ⟨4⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 4 = ⟨132⟩ := by
    native_decide
  dsimp [endRuntimeBlocks.endRuntime_block_9375_taken_stack,
    endCageIlkReadCallStack, endCageIlkReadCallRest, endCageIlkReadCallMem,
    endCageIlkReadSelectorWord, endCageIlkReadSelectorEncodedWord, endCageIlkReadTarget]
  rw [hparFree, hreadFreeRaw, hparWord, hmaskGenerated, hlen, hend]
  rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from by native_decide]

theorem endX_cageIlk_read_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hreadNoCode :
      extCodeSizeWord world.2 (endCageIlkReadTarget outSpot) = ⟨0⟩)
    (rd9375 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9375⟩
      (endCageIlkAfterParCursor I sel aw outVat outSpot outPar world).stack
      (endCageIlkParReturnMem I outVat outSpot outPar) (endCageIlkAfterParAw aw)
      outPar world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkReadTarget outSpot))) =
        UInt256.ofNat 0 := by
    rw [hreadNoCode]
    decide
  obtain ⟨_, _, rd9437⟩ := endRuntimeBlocks.endRuntime_block_9375_fallthrough
    (x0 := UInt256.ofNat outPar.size)
    (x1 := memLoad (UInt256.ofNat 64) (endCageIlkParReturnMem I outVat outSpot outPar))
    (x2 := (⟨9490⟩ : UInt256)) (x3 := endCageIlkSpotIlksPipWord outSpot)
    (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hcond
    (by simpa [endCageIlkAfterParCursor] using rd9375)
  exact endRuntimeBlocks.endRuntime_block_9437
    (R := endRuntimeBlocks.endRuntime_block_9375_fallthrough_stack
      (mem := endCageIlkParReturnMem I outVat outSpot outPar) (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64) (endCageIlkParReturnMem I outVat outSpot outPar))
      (x2 := (⟨9490⟩ : UInt256)) (x3 := endCageIlkSpotIlksPipWord outSpot)
      (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_9375_fallthrough_stack])
    rd9437

theorem endX_cageIlk_to_read_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hreadCode :
      extCodeSizeWord world.2 (endCageIlkReadTarget outSpot) ≠ ⟨0⟩)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size)
    (rd9375 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9375⟩
      (endCageIlkAfterParCursor I sel aw outVat outSpot outPar world).stack
      (endCageIlkParReturnMem I outVat outSpot outPar) (endCageIlkAfterParAw aw)
      outPar world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9443⟩
      (endCageIlkReadCallStack I sel outSpot outPar)
      (endCageIlkReadCallMem I outVat outSpot outPar) aw' outPar world k' C' := by
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkReadTarget outSpot))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hreadCode]
    native_decide
  obtain ⟨aw9441, k9441, C9441, rd9441⟩ :=
    endRuntimeBlocks.endRuntime_block_9375_taken_packed
      (x0 := UInt256.ofNat outPar.size)
      (x1 := memLoad (UInt256.ofNat 64) (endCageIlkParReturnMem I outVat outSpot outPar))
      (x2 := (⟨9490⟩ : UInt256)) (x3 := endCageIlkSpotIlksPipWord outSpot)
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest)
      (by simpa [endCageIlkAfterParCursor] using rd9375)
  have rd9441' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9441⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endCageIlkReadTarget outSpot)) ::
          endCageIlkReadCallStack I sel outSpot outPar)
        (endCageIlkReadCallMem I outVat outSpot outPar) aw9441 outPar world k9441 C9441 := by
    simpa [endCageIlkReadCallMem,
      endCageIlkReadSetupStack_eq world I outVat outSpot outPar sel
        houtVat h160Vat houtSpot houtPar h32Par] using rd9441
  exact endRuntimeBlocks.endRuntime_block_9441_packed
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endCageIlkReadTarget outSpot)))
    (R := endCageIlkReadCallStack I sel outSpot outPar)
    (by simp [endCageIlkReadCallStack, endCageIlkReadCallRest])
    rd9441'

set_option maxHeartbeats 12000000 in
theorem endCageIlkReadExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    {sel aw outVat outSpot outPar rdata k C evm}
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size)
    (houtPar : outPar.size < UInt256.size) (h32Par : 32 ≤ outPar.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCageIlkReadCallCursor world I sel aw outVat outSpot outPar rdata)
      k C (endCageIlkAfterParFrame I outVat outSpot outPar) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead" (perm := false) ]
      (sequenceExit ⟨9483⟩
        (fun cur frame e =>
          frame = endCageIlkAfterReadFrame I outVat outSpot outPar cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endCageIlkReadReturnMem I outVat outSpot outPar cur.rdata),
              endCageIlkParWord outPar, ⟨9490⟩,
              endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endCageIlkReadReturnMem I outVat outSpot outPar cur.rdata ∧
          cur.aw = endCageIlkAfterReadAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨9443⟩ = some (.GAS, .none); decide)
    (by simp [endCageIlkReadCallStack, endCageIlkReadCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endCageIlkReadTarget outSpot).toNat)
    (argVals := [])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨9444⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endCageIlkReadCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro _
    rw [endEvalCageIlkPip_afterPar]
    rw [endCageIlkPipValue_eq_masked]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    rw [evalExprs?]
    rfl
  · intro _
    apply Fin.ext
    show (endCageIlkReadTarget outSpot).toNat % EVM.addressModulus % AccountAddress.size =
      (endCageIlkReadTarget outSpot).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endCageIlkExternalEncode_read]
    change some readSelector =
      some ((endCageIlkReadCallMem I outVat outSpot outPar).readWithPadding 128 4)
    rw [endCageIlkReadCallMem_readCallData I outVat outSpot outPar
      houtVat h160Vat houtSpot houtPar h32Par]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h32 : 32 ≤ out.size
    · rw [endCageIlkExternalDecode_read_ok h32]
      intro rd hrel
      have rd9445 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
            ((⟨1⟩ : UInt256) :: endCageIlkReadCallRest I sel outSpot outPar)
            (endCageIlkReadReturnMem I outVat outSpot outPar out)
            (endCageIlkReadCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkReadCallCursor,
          endCageIlkReadCallStack, endCageIlkReadCallRest,
          endCageIlkReadCallAw, endCageIlkReadReturnMem] using rd
      have rd9461 := endRuntimeBlocks.endRuntime_block_9445_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkReadCallRest I sel outSpot outPar)
        (by simp [endCageIlkReadCallRest]) (by native_decide) (by jump_dest) rd9445
      have rd9461' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9461⟩
            [⟨0⟩, ⟨132⟩, endCageIlkReadSelectorWord,
              endCageIlkReadTarget outSpot, endCageIlkParWord outPar, ⟨9490⟩,
              endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkReadReturnMem I outVat outSpot outPar out)
            (endCageIlkReadCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9445_taken_stack,
          endCageIlkReadCallRest] using rd9461
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact h32
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd9483 := endRuntimeBlocks.endRuntime_block_9461_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨132⟩)
        (x2 := endCageIlkReadSelectorWord)
        (x3 := endCageIlkReadTarget outSpot)
        (R := [endCageIlkParWord outPar, ⟨9490⟩,
          endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd9461'
      refine ⟨.ok (endCageIlkAfterReadFrame I outVat outSpot outPar out) evm',
        Endpoint.reached (endCageIlkAfterReadCursor I sel aw outVat outSpot outPar out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endCageIlkAfterReadCursor, endCageIlkAfterReadAw,
            endRuntimeBlocks.endRuntime_block_9461_taken_stack] using rd9483⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h32, rfl, rfl, rfl⟩
    · have hshort : out.size < 32 := by omega
      rw [endCageIlkExternalDecode_read_none_short hshort]
      intro rd
      have rd9445 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
            ((⟨1⟩ : UInt256) :: endCageIlkReadCallRest I sel outSpot outPar)
            (endCageIlkReadReturnMem I outVat outSpot outPar out)
            (endCageIlkReadCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endCageIlkReadCallCursor,
          endCageIlkReadCallStack, endCageIlkReadCallRest,
          endCageIlkReadCallAw, endCageIlkReadReturnMem] using rd
      have rd9461 := endRuntimeBlocks.endRuntime_block_9445_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endCageIlkReadCallRest I sel outSpot outPar)
        (by simp [endCageIlkReadCallRest]) (by native_decide) (by jump_dest) rd9445
      have rd9461' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9461⟩
            [⟨0⟩, ⟨132⟩, endCageIlkReadSelectorWord,
              endCageIlkReadTarget outSpot, endCageIlkParWord outPar, ⟨9490⟩,
              endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]
            (endCageIlkReadReturnMem I outVat outSpot outPar out)
            (endCageIlkReadCallAw aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_9445_taken_stack,
          endCageIlkReadCallRest] using rd9461
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd9479 := endRuntimeBlocks.endRuntime_block_9461_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨132⟩)
        (x2 := endCageIlkReadSelectorWord)
        (x3 := endCageIlkReadTarget outSpot)
        (R := [endCageIlkParWord outPar, ⟨9490⟩,
          endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd9461'
      exact endRuntimeBlocks.endRuntime_block_9479
        (R := endRuntimeBlocks.endRuntime_block_9461_fallthrough_stack
          (mem := endCageIlkReadReturnMem I outVat outSpot outPar out) (rdata := out)
          (R := [endCageIlkParWord outPar, ⟨9490⟩,
            endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_9461_fallthrough_stack])
        rd9479
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd9445 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9445⟩
          ((⟨0⟩ : UInt256) :: endCageIlkReadCallRest I sel outSpot outPar)
          (endCageIlkReadReturnMem I outVat outSpot outPar out)
          (endCageIlkReadCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endCageIlkReadCallCursor,
        endCageIlkReadCallStack, endCageIlkReadCallRest,
        endCageIlkReadCallAw, endCageIlkReadReturnMem] using rd
    have rd9452 := endRuntimeBlocks.endRuntime_block_9445_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkReadCallRest I sel outSpot outPar)
      (by simp [endCageIlkReadCallRest]) (by native_decide) rd9445
    exact endRuntimeBlocks.endRuntime_block_9452
      (R := endRuntimeBlocks.endRuntime_block_9445_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endCageIlkReadCallRest I sel outSpot outPar))
      (by simp [endRuntimeBlocks.endRuntime_block_9445_fallthrough_stack,
        endCageIlkReadCallRest])
      rd9452

/-! ## `wdiv(parV, uint256(pipRead))` and final `tag[ilk]` storage -/

abbrev endWadNat : Nat := 1000000000000000000

abbrev endWadWord : UInt256 := UInt256.ofNat endWadNat

theorem endWadWord_toNat : endWadWord.toNat = endWadNat := by
  native_decide

theorem endWad_int_eq : WAD = Int.ofNat endWadNat := by
  native_decide

abbrev endCageIlkReadWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endGenericWdivMStore (x y : UInt256) : Store :=
  (endGenericMulStore x y).insert "m" (endUIntValue (endGenericMulProduct x endWadWord))

abbrev endGenericWdivResult (x y : UInt256) : UInt256 :=
  UInt256.div (endGenericMulProduct x endWadWord) y

abbrev endCageIlkWdivWord (outPar outRead : ByteArray) : UInt256 :=
  endGenericWdivResult (endCageIlkParWord outPar) (endCageIlkReadWord outRead)

abbrev endCageIlkAfterTagVFrame (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) : Frame :=
  { contract := contract,
    locals := (endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals.insert
      "tagV" (endUIntValue (endCageIlkWdivWord outPar outRead)) }

abbrev endCageIlkFinalState (evm : EVM.State) (I : ExecutionEnv)
    (outPar outRead : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tagSlot (endArg0Bytes32Key I))
    (endCageIlkWdivWord outPar outRead)

theorem endCageIlkCastPipRead (out : ByteArray) (h32 : 32 ≤ out.size) :
    castValue? (endCageIlkReadValue out) uint256St =
      some (endUIntValue (endCageIlkReadWord out)) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake : (out.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hlt : fromBytesBigEndian (out.toList.take 32) < UInt256.size := by
    unfold fromBytesBigEndian
    have hle := fromBytes'_le (bs := (out.toList.take 32).reverse)
    rw [List.length_reverse, htake] at hle
    simpa [UInt256.size] using hle
  simp [endCageIlkReadValue, uint256St, uint256Int, castValue?, fixedBytesToNat?,
    fixedBytesValid, fixedBytesSize, bytes32Width, endCageIlkReadWord, ABI.bytesToWord,
    fromByteArrayBigEndian, byteArray_toList_eq]
  rw [if_pos h32]
  simp only
  simp [endUIntValue]
  simpa [byteArray_toList_eq] using (UInt256.toNat_ofNat_of_lt hlt).symm

theorem endCageIlkAfterReadFrame_get_parV (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    (endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals.get? "parV" =
      some (endUIntValue (endCageIlkParWord outPar)) := by
  change (((endCageIlkAfterParFrame I outVat outSpot outPar).locals.insert "pipRead"
      (collapseReturns (endCageIlkReadValues outRead))).get? "parV") =
    some (endUIntValue (endCageIlkParWord outPar))
  rw [store_get_ne (endCageIlkAfterParFrame I outVat outSpot outPar).locals
    (k := "pipRead") (a := "parV") (collapseReturns (endCageIlkReadValues outRead))
    (by decide)]
  change (((endCageIlkAfterPipFrame I outVat outSpot).locals.insert "parV"
      (collapseReturns (endCageIlkParValues outPar))).get? "parV") =
    some (endUIntValue (endCageIlkParWord outPar))
  rw [store_get_self (endCageIlkAfterPipFrame I outVat outSpot).locals "parV"
    (collapseReturns (endCageIlkParValues outPar))]
  simp [endCageIlkParValues, endCageIlkUIntValue, endUIntValue, collapseReturns]

theorem endCageIlkAfterReadFrame_get_pipRead (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    (endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals.get? "pipRead" =
      some (endCageIlkReadValue outRead) := by
  change (((endCageIlkAfterParFrame I outVat outSpot outPar).locals.insert "pipRead"
      (collapseReturns (endCageIlkReadValues outRead))).get? "pipRead") =
    some (endCageIlkReadValue outRead)
  rw [store_get_self (endCageIlkAfterParFrame I outVat outSpot outPar).locals
    "pipRead" (collapseReturns (endCageIlkReadValues outRead))]
  simp [endCageIlkReadValues, collapseReturns]

theorem endEvalCageIlkParV_afterRead (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    evalExpr? config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.var "parV") = .ok (endUIntValue (endCageIlkParWord outPar)) := by
  rw [evalExpr?]
  rw [endCageIlkAfterReadFrame_get_parV]
  rfl

theorem endEvalCageIlkPipRead_afterRead (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    evalExpr? config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.var "pipRead") = .ok (endCageIlkReadValue outRead) := by
  rw [evalExpr?]
  rw [endCageIlkAfterReadFrame_get_pipRead]
  rfl

theorem endEvalCageIlkPipReadCast (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size) :
    evalExpr? config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.cast (.var "pipRead") uint256St) =
      .ok (endUIntValue (endCageIlkReadWord outRead)) := by
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config
        (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
        (.var "pipRead")
      EvalResult.ofOption EvalError.typeError (castValue? value uint256St)) =
    .ok (endUIntValue (endCageIlkReadWord outRead))
  rw [endEvalCageIlkPipRead_afterRead]
  simp [EvalResult.bind, bind, EvalResult.ofOption, endCageIlkCastPipRead outRead h32]

theorem endEvalCageIlkWdivArgs (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size) :
    evalExprs? config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      [.var "parV", .cast (.var "pipRead") uint256St] =
      .ok [endUIntValue (endCageIlkParWord outPar),
        endUIntValue (endCageIlkReadWord outRead)] := by
  rw [evalExprs?]
  rw [endEvalCageIlkParV_afterRead]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalCageIlkPipReadCast evm I outVat outSpot outPar outRead h32]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endBindParams_wdiv_cageIlk (outPar outRead : ByteArray) :
    bindParams? wdivFunction.params
      [endUIntValue (endCageIlkParWord outPar), endUIntValue (endCageIlkReadWord outRead)] =
      some (endGenericMulStore (endCageIlkParWord outPar) (endCageIlkReadWord outRead)) := by
  simp [bindParams?, wdivFunction, endGenericMulStore, endUIntValue]

theorem endGenericWdivMStore_get_m (x y : UInt256) :
    (endGenericWdivMStore x y).get? "m" =
      some (endUIntValue (endGenericMulProduct x endWadWord)) := by
  exact store_get_self (endGenericMulStore x y) "m"
    (endUIntValue (endGenericMulProduct x endWadWord))

theorem endGenericWdivMStore_get_y (x y : UInt256) :
    (endGenericWdivMStore x y).get? "y" = some (endUIntValue y) := by
  unfold endGenericWdivMStore
  rw [store_get_ne (endGenericMulStore x y) (k := "m") (a := "y")
    (endUIntValue (endGenericMulProduct x endWadWord)) (by decide)]
  exact endGenericMulStore_get_y x y

theorem endEvalGenericWdivMulArgs (evm : EVM.State) (x y : UInt256) :
    evalExprs? config { contract := contract, locals := endGenericMulStore x y } evm
      [.var "x", .intLit WAD] =
      .ok [endUIntValue x, endUIntValue endWadWord] := by
  simp [evalExprs?, evalExpr?, endGenericMulStore_get_x, EvalResult.ofOption,
    EvalResult.bind, bind, pure, endUIntValue, endWadWord_toNat, endWad_int_eq]

theorem endBindParams_mul_wdiv (x y : UInt256) :
    bindParams? mulFunction.params [endUIntValue x, endUIntValue endWadWord] =
      some (endGenericMulStore x endWadWord) := by
  simp [bindParams?, mulFunction, endGenericMulStore, endUIntValue]

theorem endGenericWdivInternalMulOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * endWadNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endGenericMulStore x y } evm
      (.internalCall "mul" [.var "x", .intLit WAD] "m")
      (.ok { contract := contract, locals := endGenericWdivMStore x y } evm) := by
  have hfit' : x.toNat * endWadWord.toNat < UInt256.size := by
    simpa [endWadWord_toNat] using hfit
  simpa [resumeAfterInternalCall, collapseReturns, endGenericWdivMStore,
    endGenericMulProduct] using
    internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endGenericMulStore x y })
      (evm := evm) (calleeEvm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [endUIntValue x, endUIntValue endWadWord])
      (callee := mulFunction) (locals := endGenericMulStore x endWadWord)
      (calleeSolm := { contract := contract, locals := endGenericMulZStore x endWadWord })
      (value := some [endUIntValue (endGenericMulProduct x endWadWord)])
      (endEvalGenericWdivMulArgs evm x y)
      (by
        change lookupCallable? contract "mul" = some mulFunction.toCallable
        rfl)
      (endBindParams_mul_wdiv x y)
      (endGenericMulFunctionOk evm x endWadWord hfit')

theorem endGenericWdivInternalMulRevert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * endWadNat) :
    ExecStmt config { contract := contract, locals := endGenericMulStore x y } evm
      (.internalCall "mul" [.var "x", .intLit WAD] "m") .reverted := by
  have hover' : UInt256.size ≤ x.toNat * endWadWord.toNat := by
    simpa [endWadWord_toNat] using hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endGenericMulStore x y })
    (evm := evm) (name := "mul") (retVar := "m")
    (args := [.var "x", .intLit WAD])
    (argVals := [endUIntValue x, endUIntValue endWadWord])
    (callee := mulFunction) (locals := endGenericMulStore x endWadWord)
    (endEvalGenericWdivMulArgs evm x y)
    (by
      change lookupCallable? contract "mul" = some mulFunction.toCallable
      rfl)
    (endBindParams_mul_wdiv x y)
    (endGenericMulFunctionRevert evm x endWadWord hover')

theorem endEvalGenericWdivReturn (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * endWadNat < UInt256.size) (hy : y ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endGenericWdivMStore x y } evm
      (.binary .div (.var "m") (.var "y")) =
      .ok (endUIntValue (endGenericWdivResult x y)) := by
  have hfit' : x.toNat * endWadWord.toNat < UInt256.size := by
    simpa [endWadWord_toNat] using hfit
  have hprod := endGenericMulProduct_toNat x endWadWord hfit'
  have hres :
      (endGenericWdivResult x y).toNat =
        (endGenericMulProduct x endWadWord).toNat / y.toNat := by
    unfold endGenericWdivResult
    rw [udiv_toNat]
  have hdiv :
      Int.ofNat (endGenericMulProduct x endWadWord).toNat / Int.ofNat y.toNat =
        Int.ofNat (endGenericWdivResult x y).toNat := by
    rw [hres]
    change (((endGenericMulProduct x endWadWord).toNat : Nat) : Int) /
        ((y.toNat : Nat) : Int) =
      ((((endGenericMulProduct x endWadWord).toNat / y.toNat : Nat) : Int))
    rw [← Int.natCast_div]
  have hyNatNe : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  have hyIntNe : Int.ofNat y.toNat ≠ 0 := by
    intro hzero
    exact hyNatNe (Int.ofNat_eq_zero.mp hzero)
  simp only [evalExpr?, endGenericWdivMStore_get_m, endGenericWdivMStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hdiv]
  simp [hyIntNe, hyNatNe]

theorem endEvalGenericWdivReturn_revert (evm : EVM.State) (x y : UInt256)
    (hy : y = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endGenericWdivMStore x y } evm
      (.binary .div (.var "m") (.var "y")) = .revert := by
  have hyInt : Int.ofNat y.toNat = 0 := by
    rw [hy]
    decide
  have hyNat : y.toNat = 0 := by
    rw [hy]
    decide
  simp only [evalExpr?, endGenericWdivMStore_get_m, endGenericWdivMStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  simp [hyInt, hyNat]

theorem endGenericWdivFunctionOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * endWadNat < UInt256.size) (hy : y ≠ ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      wdivFunction.body
      (.returned { contract := contract, locals := endGenericWdivMStore x y } evm
        (some [endUIntValue (endGenericWdivResult x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [wdivFunction] using
    (ExecBlock.consNormal
      (endGenericWdivInternalMulOk evm x y hfit) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.binary .div (.var "m") (.var "y")])
          (values := [endUIntValue (endGenericWdivResult x y)])
          (by
            simp [evalExprs?, endEvalGenericWdivReturn evm x y hfit hy,
              EvalResult.bind, bind, pure])))

theorem endGenericWdivFunctionRevertMul (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * endWadNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      wdivFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [wdivFunction] using
    (ExecBlock.consRevert
      (endGenericWdivInternalMulRevert evm x y hover))

theorem endGenericWdivFunctionRevertDen (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * endWadNat < UInt256.size) (hy : y = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      wdivFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [wdivFunction] using
    (ExecBlock.consNormal
      (endGenericWdivInternalMulOk evm x y hfit) <|
      ExecBlock.consRevert
        (ExecStmt.returnRevert
          (exprs := [.binary .div (.var "m") (.var "y")])
          (by
            simp [evalExprs?, endEvalGenericWdivReturn_revert evm x y hy,
              EvalResult.bind, bind, pure])))

theorem endCageIlkInternalWdivOk (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead ≠ ⟨0⟩) :
    ExecStmt config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      (.ok (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endCageIlkAfterTagVFrame,
    endCageIlkWdivWord, endGenericWdivResult, endUIntValue] using
    internalCallFunctionReturn
      (cfg := config) (caller := endCageIlkAfterReadFrame I outVat outSpot outPar outRead)
      (evm := evm) (calleeEvm := evm) (name := "wdiv") (retVar := "tagV")
      (args := [.var "parV", .cast (.var "pipRead") uint256St])
      (argVals := [endUIntValue (endCageIlkParWord outPar),
        endUIntValue (endCageIlkReadWord outRead)])
      (callee := wdivFunction)
      (locals := endGenericMulStore (endCageIlkParWord outPar) (endCageIlkReadWord outRead))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericWdivMStore (endCageIlkParWord outPar)
            (endCageIlkReadWord outRead) })
      (value := some [endUIntValue (endCageIlkWdivWord outPar outRead)])
      (endEvalCageIlkWdivArgs evm I outVat outSpot outPar outRead h32)
      (by
        change lookupCallable? contract "wdiv" = some wdivFunction.toCallable
        rfl)
      (endBindParams_wdiv_cageIlk outPar outRead)
      (endGenericWdivFunctionOk evm (endCageIlkParWord outPar)
        (endCageIlkReadWord outRead) hfit hden)

theorem endCageIlkInternalWdivMulRevert (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hover : UInt256.size ≤ (endCageIlkParWord outPar).toNat * endWadNat) :
    ExecStmt config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endCageIlkAfterReadFrame I outVat outSpot outPar outRead)
    (evm := evm) (name := "wdiv") (retVar := "tagV")
    (args := [.var "parV", .cast (.var "pipRead") uint256St])
    (argVals := [endUIntValue (endCageIlkParWord outPar),
      endUIntValue (endCageIlkReadWord outRead)])
    (callee := wdivFunction)
    (locals := endGenericMulStore (endCageIlkParWord outPar) (endCageIlkReadWord outRead))
    (endEvalCageIlkWdivArgs evm I outVat outSpot outPar outRead h32)
    (by
      change lookupCallable? contract "wdiv" = some wdivFunction.toCallable
      rfl)
    (endBindParams_wdiv_cageIlk outPar outRead)
    (endGenericWdivFunctionRevertMul evm (endCageIlkParWord outPar)
      (endCageIlkReadWord outRead) hover)

theorem endCageIlkInternalWdivDenRevert (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead = ⟨0⟩) :
    ExecStmt config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      (.internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endCageIlkAfterReadFrame I outVat outSpot outPar outRead)
    (evm := evm) (name := "wdiv") (retVar := "tagV")
    (args := [.var "parV", .cast (.var "pipRead") uint256St])
    (argVals := [endUIntValue (endCageIlkParWord outPar),
      endUIntValue (endCageIlkReadWord outRead)])
    (callee := wdivFunction)
    (locals := endGenericMulStore (endCageIlkParWord outPar) (endCageIlkReadWord outRead))
    (endEvalCageIlkWdivArgs evm I outVat outSpot outPar outRead h32)
    (by
      change lookupCallable? contract "wdiv" = some wdivFunction.toCallable
      rfl)
    (endBindParams_wdiv_cageIlk outPar outRead)
    (endGenericWdivFunctionRevertDen evm (endCageIlkParWord outPar)
      (endCageIlkReadWord outRead) hfit hden)

theorem endCageIlkAfterTagVFrame_get_tagV (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead).locals.get? "tagV" =
      some (endUIntValue (endCageIlkWdivWord outPar outRead)) := by
  exact store_get_self
    (endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals "tagV"
    (endUIntValue (endCageIlkWdivWord outPar outRead))

theorem endCageIlkAfterTagVFrame_get_ilk (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals.insert
      "tagV" (endUIntValue (endCageIlkWdivWord outPar outRead))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkAfterReadFrame I outVat outSpot outPar outRead).locals
    (k := "tagV") (a := "ilk") (endUIntValue (endCageIlkWdivWord outPar outRead))
    (by decide)]
  change (((endCageIlkAfterParFrame I outVat outSpot outPar).locals.insert "pipRead"
      (collapseReturns (endCageIlkReadValues outRead))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkAfterParFrame I outVat outSpot outPar).locals
    (k := "pipRead") (a := "ilk") (collapseReturns (endCageIlkReadValues outRead))
    (by decide)]
  change (((endCageIlkAfterPipFrame I outVat outSpot).locals.insert "parV"
      (collapseReturns (endCageIlkParValues outPar))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkAfterPipFrame I outVat outSpot).locals
    (k := "parV") (a := "ilk") (collapseReturns (endCageIlkParValues outPar))
    (by decide)]
  change (((endCageIlkAfterSpotIlksFrame I outVat outSpot).locals.insert "pip"
      (endCageIlkPipValue outSpot)).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkAfterSpotIlksFrame I outVat outSpot).locals
    (k := "pip") (a := "ilk") (endCageIlkPipValue outSpot) (by decide)]
  change (((endCageIlkAfterVatIlksFrame I outVat).locals.insert "spotIlk"
      (collapseReturns (endCageIlkSpotIlksValues outSpot))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCageIlkAfterVatIlksFrame I outVat).locals
    (k := "spotIlk") (a := "ilk") (collapseReturns (endCageIlkSpotIlksValues outSpot))
    (by decide)]
  exact endCageIlkAfterVatIlksFrame_get_ilk I outVat

theorem endEvalCageIlkTagV (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    evalExpr? config (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead) evm
      (.var "tagV") = .ok (endUIntValue (endCageIlkWdivWord outPar outRead)) := by
  rw [evalExpr?]
  rw [endCageIlkAfterTagVFrame_get_tagV]
  rfl

theorem endEvalCageIlkIlkAfterTagV (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) :
    evalExpr? config (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead) evm
      (.var "ilk") = .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endCageIlkAfterTagVFrame_get_ilk]
  rfl

theorem endAssignCageIlkTag (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead) evm
        .storage (tagRef (.var "ilk")) (endUIntValue (endCageIlkWdivWord outPar outRead)) =
      .ok (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead,
        endCageIlkFinalState evm I outPar outRead) := by
  let er : EvaledStorageRef := { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] }
  let loc : StorageLoc := wordLoc (tagSlot (endArg0Bytes32Key I))
  have hdrop : 32 ≤ I.calldata.toList.length - 4 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    omega
  have her : evalStorageRef config (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead)
      evm (tagRef (.var "ilk")) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefStep, tagRef, endArg0Bytes32Key,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      endEvalCageIlkIlkAfterTagV, bytes32Width, hdrop]
  have hty :
      storageTypeAt? (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead).contract.storage
          er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simp [er, loc]
  have hstore :
      storageLocStore evm loc (endUIntValue (endCageIlkWdivWord outPar outRead)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (tagSlot (endArg0Bytes32Key I)) (endCageIlkWdivWord outPar outRead)) := by
    simpa [loc, wordLoc, uint256Loc, endUIntValue] using
      storageLocStore_uint256 evm (tagSlot (endArg0Bytes32Key I))
        (endCageIlkWdivWord outPar outRead)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endCageIlkAfterTagVFrame I outVat outSpot outPar outRead)
    (evm := evm) (slot := tagRef (.var "ilk")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endCageIlkWdivWord outPar outRead).toNat)
    (by
      simp [endCageIlkAfterTagVFrame, endCageIlkAfterReadFrame,
        endCageIlkAfterParFrame, endCageIlkAfterPipFrame,
        endCageIlkAfterSpotIlksFrame, endCageIlkAfterVatIlksFrame,
        endCageIlkStore, endFreeStore, tagRef])
    her hty hloc hstore
  simpa [endCageIlkFinalState, loc, endUIntValue] using hassign

theorem endCageIlkAfterReadSuffixOk (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead ≠ ⟨0⟩) :
    ExecBlock config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      (.ok (endCageIlkAfterTagVFrame I outVat outSpot outPar outRead)
        (endCageIlkFinalState evm I outPar outRead)) := by
  exact ExecBlock.consNormal
    (endCageIlkInternalWdivOk evm I outVat outSpot outPar outRead h32 hfit hden) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalCageIlkTagV evm I outVat outSpot outPar outRead)
        (endAssignCageIlkTag evm I outVat outSpot outPar outRead hsz36))
      ExecBlock.nil

theorem endCageIlkAfterReadSuffixMulRevert (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hover : UInt256.size ≤ (endCageIlkParWord outPar).toNat * endWadNat) :
    ExecBlock config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      .reverted := by
  exact ExecBlock.consRevert
    (endCageIlkInternalWdivMulRevert evm I outVat outSpot outPar outRead h32 hover)

theorem endCageIlkAfterReadSuffixDenRevert (evm : EVM.State) (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray) (h32 : 32 ≤ outRead.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead = ⟨0⟩) :
    ExecBlock config (endCageIlkAfterReadFrame I outVat outSpot outPar outRead) evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      .reverted := by
  exact ExecBlock.consRevert
    (endCageIlkInternalWdivDenRevert evm I outVat outSpot outPar outRead h32 hfit hden)

theorem endCageIlkReadCallMem_size (I : ExecutionEnv)
    (outVat outSpot outPar : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) :
    (endCageIlkReadCallMem I outVat outSpot outPar).size = 288 := by
  unfold endCageIlkReadCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_9375_taken_memory]
  rw [endCageIlkParReturnMem_mload64 I outVat outSpot outPar houtVat h160Vat
    houtSpot houtPar]
  exact toByteArray_write32_size_of_le (endCageIlkParReturnMem I outVat outSpot outPar)
    endCageIlkReadSelectorEncodedWord 128 288 288
    (by
      rw [endCageIlkParReturnMem_size I outVat outSpot outPar houtVat h160Vat
        houtSpot houtPar]
      rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot])
    (by
      rw [endCageIlkParReturnMem_size I outVat outSpot outPar houtVat h160Vat
        houtSpot houtPar]
      rw [endCageIlkParCallMem_size I outVat outSpot houtVat h160Vat houtSpot]
      omega)
    (by omega)

theorem endCageIlkReadOutputFacts (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size) :
    CallOutputFacts (endCageIlkReadCallMem I outVat outSpot outPar) outRead
      (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) := by
  exact callOutputFacts (endCageIlkReadCallMem I outVat outSpot outPar) outRead
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) houtRead
    (by
      rw [endCageIlkReadCallMem_size I outVat outSpot outPar
        houtVat h160Vat houtSpot houtPar h32Par]
      decide)

theorem endCageIlkReadReturnMem_size (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size) :
    (endCageIlkReadReturnMem I outVat outSpot outPar outRead).size =
      (endCageIlkReadCallMem I outVat outSpot outPar).size := by
  have hf := endCageIlkReadOutputFacts I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead
  simpa [endCageIlkReadReturnMem] using hf.size

theorem endCageIlkReadReturnMem_read64 (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size) :
    (endCageIlkReadReturnMem I outVat outSpot outPar outRead).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hf := endCageIlkReadOutputFacts I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead
  simpa [endCageIlkReadReturnMem,
    endCageIlkReadCallMem_read64 I outVat outSpot outPar houtVat h160Vat
      houtSpot houtPar h32Par] using
    hf.readBelow 64 (by decide)

theorem endCageIlkReadReturnMem_mload64 (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endCageIlkReadReturnMem I outVat outSpot outPar outRead) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endCageIlkReadReturnMem I outVat outSpot outPar outRead)
    (by
      rw [endCageIlkReadReturnMem_size I outVat outSpot outPar outRead
        houtVat h160Vat houtSpot houtPar h32Par houtRead]
      rw [endCageIlkReadCallMem_size I outVat outSpot outPar
        houtVat h160Vat houtSpot houtPar h32Par]
      omega)
    (endCageIlkReadReturnMem_read64 I outVat outSpot outPar outRead
      houtVat h160Vat houtSpot houtPar h32Par houtRead)

theorem endCageIlkReadReturnMem_read128 (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size) :
    (endCageIlkReadReturnMem I outVat outSpot outPar outRead).readWithPadding 128 32 =
      outRead.extract 0 32 := by
  have hf := endCageIlkReadOutputFacts I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead
  simpa [endCageIlkReadReturnMem] using
    hf.readWord (by decide) h32Read

theorem endCageIlkReadReturnMem_mload128 (I : ExecutionEnv)
    (outVat outSpot outPar outRead : ByteArray)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size) :
    memLoad (⟨128⟩ : UInt256) (endCageIlkReadReturnMem I outVat outSpot outPar outRead) =
      endCageIlkReadWord outRead := by
  unfold memLoad
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endCageIlkReadReturnMem_size I outVat outSpot outPar outRead
      houtVat h160Vat houtSpot houtPar h32Par houtRead]
    rw [endCageIlkReadCallMem_size I outVat outSpot outPar
      houtVat h160Vat houtSpot houtPar h32Par]
    omega)]
  rw [endCageIlkReadReturnMem_read128 I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read]
  change UInt256.ofNat (fromByteArrayBigEndian (outRead.extract 0 32)) =
    ABI.bytesToWord (outRead.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endX_cageIlk_to_wdiv {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar outRead k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size)
    (rd9483 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9483⟩
      (endCageIlkAfterReadCursor I sel aw outVat outSpot outPar outRead world).stack
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
      (endCageIlkAfterReadAw aw) outRead world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endWadWord, endCageIlkParWord outPar, ⟨10139⟩,
        endCageIlkReadWord outRead, ⟨0⟩, endCageIlkReadWord outRead,
        endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
        endArg0Word I, ⟨562⟩, sel]
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead) aw' outRead world k' C' := by
  have hfree := endCageIlkReadReturnMem_mload64 I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead
  have hread := endCageIlkReadReturnMem_mload128 I outVat outSpot outPar outRead
    houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read
  have rd9483' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9483⟩
        (UInt256.ofNat outRead.size ::
          memLoad (UInt256.ofNat 64)
            (endCageIlkReadReturnMem I outVat outSpot outPar outRead) ::
          [endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
            endArg0Word I, ⟨562⟩, sel])
        (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
        (endCageIlkAfterReadAw aw) outRead world k C := by
    simpa [endCageIlkAfterReadCursor] using rd9483
  have rd10231 := endRuntimeBlocks.endRuntime_block_9483
    (x0 := UInt256.ofNat outRead.size)
    (x1 := memLoad (UInt256.ofNat 64)
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead))
    (R := [endCageIlkParWord outPar, ⟨9490⟩,
      endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest) rd9483'
  have rd10231' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10231⟩
        [endCageIlkReadWord outRead, endCageIlkParWord outPar, ⟨9490⟩,
          endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel]
        (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
        (M (endCageIlkAfterReadAw aw)
          (memLoad (UInt256.ofNat 64)
            (endCageIlkReadReturnMem I outVat outSpot outPar outRead))
          (⟨32⟩ : UInt256)) outRead world (k + 5)
        (C + ((17) + memExpansionCost (endCageIlkAfterReadAw aw)
          (memLoad (UInt256.ofNat 64)
            (endCageIlkReadReturnMem I outVat outSpot outPar outRead))
          (⟨32⟩ : UInt256))) := by
    simpa [endRuntimeBlocks.endRuntime_block_9483_stack, hfree, hread] using rd10231
  have rd10170 := endRuntimeBlocks.endRuntime_block_10231
    (x0 := endCageIlkReadWord outRead) (x1 := endCageIlkParWord outPar)
    (R := [⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest) rd10231'
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10231_stack, endWadWord] using rd10170⟩

theorem endX_cageIlk_wdiv_mul_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar outRead k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size)
    (hover : UInt256.size ≤ (endCageIlkParWord outPar).toNat * endWadNat)
    (rd9483 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9483⟩
      (endCageIlkAfterReadCursor I sel aw outVat outSpot outPar outRead world).stack
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
      (endCageIlkAfterReadAw aw) outRead world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hover' :
      UInt256.size ≤ (endCageIlkParWord outPar).toNat * endWadWord.toNat := by
    simpa [endWadWord_toNat] using hover
  obtain ⟨aw10170, k10170, C10170, rd10170⟩ :=
    endX_cageIlk_to_wdiv (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outVat := outVat) (outSpot := outSpot) (outPar := outPar) (outRead := outRead)
      (k := k) (C := C) (world := world)
      houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read rd9483
  exact endX_flow_checkedMul_fail
    (x := endCageIlkParWord outPar) (y := endWadWord)
    (ret := (⟨10139⟩ : UInt256))
    (R := [endCageIlkReadWord outRead, ⟨0⟩, endCageIlkReadWord outRead,
      endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
      endArg0Word I, ⟨562⟩, sel])
    hover' (by simp)
    (by simpa using rd10170)

theorem endX_cageIlk_wdiv_den_invalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar outRead k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead = ⟨0⟩)
    (rd9483 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9483⟩
      (endCageIlkAfterReadCursor I sel aw outVat outSpot outPar outRead world).stack
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
      (endCageIlkAfterReadAw aw) outRead world k C) :
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hfit' :
      (endCageIlkParWord outPar).toNat * endWadWord.toNat < UInt256.size := by
    simpa [endWadWord_toNat] using hfit
  obtain ⟨aw10170, k10170, C10170, rd10170⟩ :=
    endX_cageIlk_to_wdiv (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outVat := outVat) (outSpot := outSpot) (outPar := outPar) (outRead := outRead)
      (k := k) (C := C) (world := world)
      houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read rd9483
  obtain ⟨aw10139, k10139, C10139, rd10139⟩ :=
    endX_flow_checkedMul_ok
      (x := endCageIlkParWord outPar) (y := endWadWord)
      (ret := (⟨10139⟩ : UInt256))
      (R := [endCageIlkReadWord outRead, ⟨0⟩, endCageIlkReadWord outRead,
        endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
        endArg0Word I, ⟨562⟩, sel])
      hfit' (by jump_dest) (by simp)
      (by simpa using rd10170)
  have rd10145 := endRuntimeBlocks.endRuntime_block_10139_fallthrough
    (x0 := endGenericMulProduct (endCageIlkParWord outPar) endWadWord)
    (x1 := endCageIlkReadWord outRead)
    (R := [⟨0⟩, endCageIlkReadWord outRead, endCageIlkParWord outPar,
      ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
    (by simp) hden
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd10139)
  exact endRuntimeBlocks.endRuntime_block_10145
    (R := [endGenericMulProduct (endCageIlkParWord outPar) endWadWord,
      endCageIlkReadWord outRead, ⟨0⟩, endCageIlkReadWord outRead,
      endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
      endArg0Word I, ⟨562⟩, sel])
    rd10145

theorem endX_cageIlk_after_read_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outVat outSpot outPar outRead k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size) (houtRead : outRead.size < UInt256.size)
    (h32Read : 32 ≤ outRead.size)
    (hfit : (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size)
    (hden : endCageIlkReadWord outRead ≠ ⟨0⟩)
    (rd9483 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9483⟩
      (endCageIlkAfterReadCursor I sel aw outVat outSpot outPar outRead world).stack
      (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
      (endCageIlkAfterReadAw aw) outRead world k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (world.1, storageWrite I.codeOwner world.2 (endCageIlkTagWorldSlot I)
        (endCageIlkWdivWord outPar outRead))
      ByteArray.empty := by
  have hfit' :
      (endCageIlkParWord outPar).toNat * endWadWord.toNat < UInt256.size := by
    simpa [endWadWord_toNat] using hfit
  obtain ⟨aw10170, k10170, C10170, rd10170⟩ :=
    endX_cageIlk_to_wdiv (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) (aw := aw)
      (outVat := outVat) (outSpot := outSpot) (outPar := outPar) (outRead := outRead)
      (k := k) (C := C) (world := world)
      houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read rd9483
  obtain ⟨aw10139, k10139, C10139, rd10139⟩ :=
    endX_flow_checkedMul_ok
      (x := endCageIlkParWord outPar) (y := endWadWord)
      (ret := (⟨10139⟩ : UInt256))
      (R := [endCageIlkReadWord outRead, ⟨0⟩, endCageIlkReadWord outRead,
        endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
        endArg0Word I, ⟨562⟩, sel])
      hfit' (by jump_dest) (by simp)
      (by simpa using rd10170)
  have rd10146 := endRuntimeBlocks.endRuntime_block_10139_taken
    (x0 := endGenericMulProduct (endCageIlkParWord outPar) endWadWord)
    (x1 := endCageIlkReadWord outRead)
    (R := [⟨0⟩, endCageIlkReadWord outRead, endCageIlkParWord outPar,
      ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
    (by simp) hden (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd10139)
  have rd9490 := endRuntimeBlocks.endRuntime_block_10146
    (x0 := endGenericMulProduct (endCageIlkParWord outPar) endWadWord)
    (x1 := endCageIlkReadWord outRead)
    (x2 := (⟨0⟩ : UInt256)) (x3 := endCageIlkReadWord outRead)
    (x4 := endCageIlkParWord outPar) (x5 := (⟨9490⟩ : UInt256))
    (R := [endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa using rd10146)
  have rd9490' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9490⟩
        [endCageIlkWdivWord outPar outRead, endCageIlkSpotIlksPipWord outSpot,
          endArg0Word I, ⟨562⟩, sel]
        (endCageIlkReadReturnMem I outVat outSpot outPar outRead) aw10139 outRead world
        (k10139 + 4 + 8) (C10139 + 17 + 26) := by
    simpa [endRuntimeBlocks.endRuntime_block_10146_stack, endCageIlkWdivWord,
      endGenericWdivResult] using rd9490
  obtain ⟨k562, C562, rd562⟩ := endRuntimeBlocks.endRuntime_block_9490
    (x0 := endCageIlkWdivWord outPar outRead)
    (x1 := endCageIlkSpotIlksPipWord outSpot)
    (x2 := endArg0Word I) (x3 := (⟨562⟩ : UInt256)) (R := [sel])
    (by simp) hperm (by jump_dest) rd9490'
  have rd562' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩ [sel]
        (endRuntimeBlocks.endRuntime_block_9490_memory
          (mem := endCageIlkReadReturnMem I outVat outSpot outPar outRead)
          (x2 := endArg0Word I))
        (M (M (M (M (M aw10139 (UInt256.ofNat 0) (⟨32⟩ : UInt256))
          (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0)
          (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            ((UInt256.ofNat 12).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0
                (endCageIlkReadReturnMem I outVat outSpot outPar outRead)
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32))
          (UInt256.ofNat 0))
        outRead
        (world.1, storageWrite I.codeOwner world.2 (endCageIlkTagWorldSlot I)
          (endCageIlkWdivWord outPar outRead)) k562 C562 := by
    simpa [endRuntimeBlocks.endRuntime_block_9490_stack,
      endRuntimeBlocks.endRuntime_block_9490_memory,
      endCageIlkTagHashSlot (endCageIlkReadReturnMem I outVat outSpot outPar outRead) I]
      using rd562
  exact endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp) rd562'

theorem endCageIlkAfterReadSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outVat outSpot outPar : ByteArray}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size) (houtPar : outPar.size < UInt256.size)
    (h32Par : 32 ≤ outPar.size)
    (hpc : cur.pc = ⟨9483⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP :
      frame = endCageIlkAfterReadFrame I outVat outSpot outPar cur.rdata ∧
      CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world evm ∧
      cur.rdata.size < UInt256.size ∧
      32 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64)
            (endCageIlkReadReturnMem I outVat outSpot outPar cur.rdata),
          endCageIlkParWord outPar, ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot,
          endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endCageIlkReadReturnMem I outVat outSpot outPar cur.rdata ∧
      cur.aw = endCageIlkAfterReadAw aw) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      frame evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      (runtimeExit (.abi [])) ∨
    (ExecBlock config frame evm
      [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
        .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]
      .reverted ∧
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with ⟨hframe, hrel, houtRead, h32Read, hstack, hmem, haw⟩
  cases hframe
  by_cases hfit :
      (endCageIlkParWord outPar).toNat * endWadNat < UInt256.size
  · by_cases hden : endCageIlkReadWord cur.rdata = ⟨0⟩
    · have hsource := endCageIlkAfterReadSuffixDenRevert evm I outVat outSpot outPar
        cur.rdata h32Read hfit hden
      have hinv := endX_cageIlk_wdiv_den_invalid
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw)
        (outVat := outVat) (outSpot := outSpot) (outPar := outPar)
        (outRead := cur.rdata) (k := k) (C := C) (world := cur.world)
        houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read hfit hden
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterReadCursor] using rd)
      exact Or.inr ⟨hsource, hinv⟩
    · have hsource := endCageIlkAfterReadSuffixOk evm I outVat outSpot outPar
        cur.rdata h32Read hsz36 hfit hden
      have rdret := endX_cageIlk_after_read_ok
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw)
        (outVat := outVat) (outSpot := outSpot) (outPar := outPar)
        (outRead := cur.rdata) (k := k) (C := C) (world := cur.world)
        hperm houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read hfit hden
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterReadCursor] using rd)
      have hstored :=
        hrel.storageStore_codeOwner (tagSlot (endArg0Bytes32Key I))
          (endCageIlkWdivWord outPar cur.rdata)
      exact Or.inl <| BlockProgress.ofRDret hsource rdret
        (by
          simpa [endCageIlkFinalState] using hstored.created.symm)
        (by
          simpa [endCageIlkFinalState, storageWrite, endTagSlot_eq I hsz36,
            endCageIlkTagWorldSlot] using hstored.accounts)
        abiVoidFallthrough
  · have hover : UInt256.size ≤ (endCageIlkParWord outPar).toNat * endWadNat := by
      omega
    have hsource := endCageIlkAfterReadSuffixMulRevert evm I outVat outSpot outPar
      cur.rdata h32Read hover
    have hrev := endX_cageIlk_wdiv_mul_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw)
      (outVat := outVat) (outSpot := outSpot) (outPar := outPar)
      (outRead := cur.rdata) (k := k) (C := C) (world := cur.world)
      houtVat h160Vat houtSpot houtPar h32Par houtRead h32Read hover
      (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterReadCursor] using rd)
    exact Or.inl (BlockProgress.ofRDrev hsource hrev)

abbrev endCageIlkWdivTagStmts : List Stmt :=
  [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
    .assign .storage (tagRef (.var "ilk")) (.var "tagV") ]

set_option maxHeartbeats 12000000 in
theorem endCageIlkAfterParSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outVat outSpot : ByteArray}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (houtSpot : outSpot.size < UInt256.size)
    (hpc : cur.pc = ⟨9375⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP :
      frame = endCageIlkAfterParFrame I outVat outSpot cur.rdata ∧
      CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world evm ∧
      cur.rdata.size < UInt256.size ∧
      32 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64)
            (endCageIlkParReturnMem I outVat outSpot cur.rdata),
          ⟨9490⟩, endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endCageIlkParReturnMem I outVat outSpot cur.rdata ∧
      cur.aw = endCageIlkAfterParAw aw) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      frame evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      (runtimeExit (.abi [])) ∨
    (ExecBlock config frame evm
      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      .reverted ∧
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with ⟨hframe, hrel, houtPar, h32Par, hstack, hmem, haw⟩
  cases hframe
  have hreceiver :
      evalExpr? config (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
        (.var "pip") =
        .ok (.address (AccountAddress.ofNat (endCageIlkReadTarget outSpot).toNat)) := by
    rw [endEvalCageIlkPip_afterPar]
    rw [endCageIlkPipValue_eq_masked]
  by_cases hreadNoCode :
      extCodeSizeWord cur.world.2 (endCageIlkReadTarget outSpot) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap (endCageIlkReadTarget outSpot) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hreadNoCode
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_false
        (locals := (endCageIlkAfterParFrame I outVat outSpot cur.rdata).locals)
        (receiver := .var "pip") hreceiver hsrcNoCode
    have hsource :
        ExecBlock config (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
          (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
              (perm := false) ++
            endCageIlkWdivTagStmts)
          .reverted := by
      simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts] using
        (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
    have hrev :=
      endX_cageIlk_read_no_code
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outVat := outVat)
        (outSpot := outSpot) (outPar := cur.rdata) (k := k) (C := C)
        (world := cur.world) hreadNoCode
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterParCursor] using rd)
    exact Or.inl (BlockProgress.ofRDrev hsource hrev)
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endCageIlkReadTarget outSpot) ≠ ⟨0⟩ := by
      intro hz
      exact hreadNoCode (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_true
        (locals := (endCageIlkAfterParFrame I outVat outSpot cur.rdata).locals)
        (receiver := .var "pip") hreceiver hsrcCode
    have hguardBlock :
        ExecBlock config (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.var "pip")) (.intLit 0)) ]
          (.ok (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm) :=
      ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
    obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
      endX_cageIlk_to_read_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outVat := outVat)
        (outSpot := outSpot) (outPar := cur.rdata) (k := k) (C := C)
        (world := cur.world) hreadNoCode houtVat h160Vat houtSpot houtPar h32Par
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterParCursor] using rd)
    have hcallProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
          [ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
              (perm := false) ]
          (sequenceExit ⟨9483⟩
            (fun curAfter frameAfter evmAfter =>
              frameAfter =
                endCageIlkAfterReadFrame I outVat outSpot cur.rdata curAfter.rdata ∧
              CallStateRel (initState cA gh bl σ σ₀ g A I) I curAfter.world evmAfter ∧
              accountStaticStateEq evm.accountMap evmAfter.accountMap ∧
              curAfter.rdata.size < UInt256.size ∧
              32 ≤ curAfter.rdata.size ∧
              curAfter.stack =
                [UInt256.ofNat curAfter.rdata.size,
                  memLoad (UInt256.ofNat 64)
                    (endCageIlkReadReturnMem I outVat outSpot cur.rdata
                      curAfter.rdata),
                  endCageIlkParWord cur.rdata, ⟨9490⟩,
                  endCageIlkSpotIlksPipWord outSpot, endArg0Word I, ⟨562⟩, sel] ∧
              curAfter.mem =
                endCageIlkReadReturnMem I outVat outSpot cur.rdata curAfter.rdata ∧
              curAfter.aw = endCageIlkAfterReadAw awCall)
            (runtimeExit (.abi []))) :=
      (endCageIlkReadExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
        (outVat := outVat) (outSpot := outSpot) (outPar := cur.rdata)
        (rdata := cur.rdata) (k := kCall) (C := CCall) (evm := evm)
        houtVat h160Vat houtSpot houtPar h32Par)
        (by simpa [endCageIlkReadCallCursor] using rdCall)
        hrel
    rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
    cases result with
    | ok frameAfter evmAfter =>
        cases endpoint with
        | reached curAfter =>
            simp only [sequenceExit, fallthrough] at hQ
            rcases hQ with ⟨hpcAfter, hAfter⟩
            rcases hAfter with
              ⟨hframeAfter, hrelAfter, _hstaticAfter, houtRead, h32Read,
                hstackAfter, hmemAfter, hawAfter⟩
            rcases hreachEndpoint with ⟨kAfter, CAfter, rdAfter⟩
            have hsuffix :=
              endCageIlkAfterReadSuffixProgressOrInvalid
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
                (outVat := outVat) (outSpot := outSpot) (outPar := cur.rdata)
                (cur := curAfter) (k := kAfter) (C := CAfter)
                (frame := frameAfter) (evm := evmAfter)
                hperm hsz36 houtVat h160Vat houtSpot houtPar h32Par hpcAfter rdAfter
                ⟨hframeAfter, hrelAfter, houtRead, h32Read, hstackAfter, hmemAfter,
                  hawAfter⟩
            cases hsuffix with
            | inl hsuffixProgress =>
                have hcallSuffixProgress :
                    BlockProgress endBytecode I g
                      (initState cA gh bl σ σ₀ g A I) config
                      (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
                      ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                          (perm := false) ] ++
                        endCageIlkWdivTagStmts)
                      (runtimeExit (.abi [])) :=
                  BlockProgress.prepend hcallBlock
                    (by simpa [endCageIlkWdivTagStmts] using hsuffixProgress)
                have hprogress := BlockProgress.prepend hguardBlock hcallSuffixProgress
                exact Or.inl (by
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hprogress)
            | inr hinvalid =>
                rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                have hcallSuffixBlock :
                    ExecBlock config (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
                      ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                          (perm := false) ] ++
                        endCageIlkWdivTagStmts)
                      .reverted := by
                  exact Reasoning.Theory.execBlock_append hcallBlock
                    (by simpa [endCageIlkWdivTagStmts] using hsuffixBlock)
                have hfullBlock :
                    ExecBlock config (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
                      (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts)
                      .reverted := by
                  have hcombined :=
                    Reasoning.Theory.execBlock_append hguardBlock hcallSuffixBlock
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hcombined
                exact Or.inr ⟨hfullBlock, hinv⟩
        | returned world out =>
            simp [sequenceExit, fallthrough] at hQ
        | reverted =>
            simp [sequenceExit, fallthrough] at hQ
    | returned frameRet evmRet value =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
              ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ] ++
                endCageIlkWdivTagStmts)
              (runtimeExit (.abi [])) := by
          refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hguardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | reverted =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
              ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ] ++
                endCageIlkWdivTagStmts)
              (runtimeExit (.abi [])) := by
          refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hguardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «break» frameBreak evmBreak =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
              ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ] ++
                endCageIlkWdivTagStmts)
              (runtimeExit (.abi [])) := by
          refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hguardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «continue» frameContinue evmContinue =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterParFrame I outVat outSpot cur.rdata) evm
              ([ .externalCall (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ] ++
                endCageIlkWdivTagStmts)
              (runtimeExit (.abi [])) := by
          refine ⟨.continue frameContinue evmContinue, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hguardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)

set_option maxHeartbeats 12000000 in
theorem endCageIlkAfterSpotSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {outVat : ByteArray}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (houtVat : outVat.size < UInt256.size) (h160Vat : 160 ≤ outVat.size)
    (hpc : cur.pc = ⟨9255⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP :
      frame = endCageIlkAfterSpotIlksFrame I outVat cur.rdata ∧
      CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world evm ∧
      cur.rdata.size < UInt256.size ∧
      64 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endCageIlkSpotIlksReturnMem I outVat cur.rdata),
          ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endCageIlkSpotIlksReturnMem I outVat cur.rdata ∧
      cur.aw = endCageIlkAfterSpotIlksAw aw) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      frame evm
      ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      (runtimeExit (.abi [])) ∨
    (ExecBlock config frame evm
      ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      .reverted ∧
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with ⟨hframe, hrel, houtSpot, h64Spot, hstack, hmem, haw⟩
  cases hframe
  have hletStmt :=
    endLetCageIlkPip evm I outVat cur.rdata
  have hslotSpot := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 6)
  have hreceiver :
      evalExpr? config (endCageIlkAfterPipFrame I outVat cur.rdata) evm
        (.storage spotRef) =
        .ok (.address (AccountAddress.ofNat
          (endCageIlkSpotTarget cur.world.2 I).toNat)) := by
    rw [endEvalSpotAddress_cageIlk_afterPip]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (UInt256.ofNat 6)) solcAddrMask).toNat)) =
      EvalResult.ok (Value.address
        (AccountAddress.ofNat (endCageIlkSpotTarget cur.world.2 I).toNat))
    rw [hslotSpot]
  by_cases hspotNoCode :
      extCodeSizeWord cur.world.2 (endCageIlkSpotTarget cur.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap (endCageIlkSpotTarget cur.world.2 I) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrel.accounts]
      exact hspotNoCode
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_false
        (locals := (endCageIlkAfterPipFrame I outVat cur.rdata).locals)
        (receiver := .storage spotRef) hreceiver hsrcNoCode
    have hsource :
        ExecBlock config (endCageIlkAfterSpotIlksFrame I outVat cur.rdata) evm
          ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
            checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
              "parV" (perm := false) ++
            checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
              (perm := false) ++
            endCageIlkWdivTagStmts)
          .reverted := by
      simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts, List.append_assoc] using
        (ExecBlock.consNormal hletStmt
          (ExecBlock.consRevert (ExecStmt.requireFalse hguard)))
    have hrev :=
      endX_cageIlk_par_no_code
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outVat := outVat)
        (outSpot := cur.rdata) (k := k) (C := C) (world := cur.world)
        hspotNoCode
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterSpotIlksCursor] using rd)
    exact Or.inl (BlockProgress.ofRDrev hsource hrev)
  · have hsrcCode :
        extCodeSizeWord evm.accountMap (endCageIlkSpotTarget cur.world.2 I) ≠ ⟨0⟩ := by
      intro hz
      exact hspotNoCode (by
        rw [extCodeSizeWord_accountMapEquiv hrel.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_true
        (locals := (endCageIlkAfterPipFrame I outVat cur.rdata).locals)
        (receiver := .storage spotRef) hreceiver hsrcCode
    have hletGuardBlock :
        ExecBlock config (endCageIlkAfterSpotIlksFrame I outVat cur.rdata) evm
          [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0),
            .require (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) ]
          (.ok (endCageIlkAfterPipFrame I outVat cur.rdata) evm) :=
      ExecBlock.consNormal hletStmt <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
    obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
      endX_cageIlk_to_par_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (outVat := outVat)
        (outSpot := cur.rdata) (k := k) (C := C) (world := cur.world)
        hspotNoCode houtVat h160Vat houtSpot h64Spot
        (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterSpotIlksCursor] using rd)
    have hcallProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endCageIlkAfterPipFrame I outVat cur.rdata) evm
          [ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
              (perm := false) ]
          (sequenceExit ⟨9375⟩
            (fun curAfter frameAfter evmAfter =>
              frameAfter = endCageIlkAfterParFrame I outVat cur.rdata curAfter.rdata ∧
              CallStateRel (initState cA gh bl σ σ₀ g A I) I curAfter.world evmAfter ∧
              accountStaticStateEq evm.accountMap evmAfter.accountMap ∧
              curAfter.rdata.size < UInt256.size ∧
              32 ≤ curAfter.rdata.size ∧
              curAfter.stack =
                [UInt256.ofNat curAfter.rdata.size,
                  memLoad (UInt256.ofNat 64)
                    (endCageIlkParReturnMem I outVat cur.rdata curAfter.rdata),
                  ⟨9490⟩, endCageIlkSpotIlksPipWord cur.rdata, endArg0Word I,
                  ⟨562⟩, sel] ∧
              curAfter.mem = endCageIlkParReturnMem I outVat cur.rdata curAfter.rdata ∧
              curAfter.aw = endCageIlkAfterParAw awCall)
            (runtimeExit (.abi []))) :=
      (endCageIlkParExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
        (outVat := outVat) (outSpot := cur.rdata) (rdata := cur.rdata)
        (k := kCall) (C := CCall) (evm := evm)
        houtVat h160Vat houtSpot)
        (by simpa [endCageIlkParCallCursor] using rdCall)
        hrel
    rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
    cases result with
    | ok frameAfter evmAfter =>
        cases endpoint with
        | reached curAfter =>
            simp only [sequenceExit, fallthrough] at hQ
            rcases hQ with ⟨hpcAfter, hAfter⟩
            rcases hAfter with
              ⟨hframeAfter, hrelAfter, _hstaticAfter, houtPar, h32Par,
                hstackAfter, hmemAfter, hawAfter⟩
            rcases hreachEndpoint with ⟨kAfter, CAfter, rdAfter⟩
            have hsuffix :=
              endCageIlkAfterParSuffixProgressOrInvalid
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
                (outVat := outVat) (outSpot := cur.rdata)
                (cur := curAfter) (k := kAfter) (C := CAfter)
                (frame := frameAfter) (evm := evmAfter)
                hperm hsz36 houtVat h160Vat houtSpot hpcAfter rdAfter
                ⟨hframeAfter, hrelAfter, houtPar, h32Par, hstackAfter, hmemAfter,
                  hawAfter⟩
            cases hsuffix with
            | inl hsuffixProgress =>
                have hcallSuffixProgress :
                    BlockProgress endBytecode I g
                      (initState cA gh bl σ σ₀ g A I) config
                      (endCageIlkAfterPipFrame I outVat cur.rdata) evm
                      ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                          (perm := false) ] ++
                        (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                      (runtimeExit (.abi [])) :=
                  BlockProgress.prepend hcallBlock hsuffixProgress
                have hprogress := BlockProgress.prepend hletGuardBlock hcallSuffixProgress
                exact Or.inl (by
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hprogress)
            | inr hinvalid =>
                rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                have hcallSuffixBlock :
                    ExecBlock config (endCageIlkAfterPipFrame I outVat cur.rdata) evm
                      ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                          (perm := false) ] ++
                        (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                      .reverted :=
                  Reasoning.Theory.execBlock_append hcallBlock hsuffixBlock
                have hfullBlock :
                    ExecBlock config (endCageIlkAfterSpotIlksFrame I outVat cur.rdata) evm
                      ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts)
                      .reverted := by
                  have hcombined :=
                    Reasoning.Theory.execBlock_append hletGuardBlock hcallSuffixBlock
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hcombined
                exact Or.inr ⟨hfullBlock, hinv⟩
        | returned world out =>
            simp [sequenceExit, fallthrough] at hQ
        | reverted =>
            simp [sequenceExit, fallthrough] at hQ
    | returned frameRet evmRet value =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterPipFrame I outVat cur.rdata) evm
              ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                  (perm := false) ] ++
                (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ++
                endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hletGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | reverted =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterPipFrame I outVat cur.rdata) evm
              ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                  (perm := false) ] ++
                (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ++
                endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hletGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «break» frameBreak evmBreak =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterPipFrame I outVat cur.rdata) evm
              ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                  (perm := false) ] ++
                (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ++
                endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hletGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «continue» frameContinue evmContinue =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterPipFrame I outVat cur.rdata) evm
              ([ .externalCall (.storage spotRef) "par" (.intLit 0) [] "parV"
                  (perm := false) ] ++
                (checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                  (perm := false) ++
                endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.continue frameContinue evmContinue, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hletGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)

set_option maxHeartbeats 12000000 in
theorem endCageIlkAfterVatSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256}
    {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hpc : cur.pc = ⟨9119⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP :
      frame = endCageIlkAfterVatIlksFrame I cur.rdata ∧
      CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world evm ∧
      cur.rdata.size < UInt256.size ∧
      160 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I cur.rdata),
          endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endCageIlkVatIlksReturnMem I cur.rdata ∧
      cur.aw = endCageIlkAfterVatIlksAw aw) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      frame evm
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      (runtimeExit (.abi [])) ∨
    (ExecBlock config frame evm
      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        endCageIlkWdivTagStmts)
      .reverted ∧
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with ⟨hframe, hrel, houtVat, h160Vat, hstack, hmem, haw⟩
  cases hframe
  let evmArt := endCageIlkAfterArtState evm I cur.rdata
  let worldArt := endCageIlkArtStoredWorld cur.world I cur.rdata
  have hassignStmt :
      ExecStmt config (endCageIlkAfterVatIlksFrame I cur.rdata) evm
        (.assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0))
        (.ok (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt) := by
    simpa [evmArt] using
      ExecStmt.assign (endEvalCageIlkVatIlkWord0 evm I cur.rdata)
        (endAssignCageIlkArt evm I cur.rdata hsz36)
  have hstoredArt :=
    hrel.storageStore_codeOwner (ArtSlot (endArg0Bytes32Key I))
      (endCageIlkVatIlksWord0 cur.rdata)
  have hrelArt :
      CallStateRel (initState cA gh bl σ σ₀ g A I) I worldArt evmArt := by
    simpa [worldArt, evmArt, endCageIlkArtStoredWorld, endCageIlkAfterArtState,
      storageWrite, endCageIlkArtWorldSlot, endArtSlot_eq I hsz36] using hstoredArt
  obtain ⟨awGuard, kGuard, CGuard, rdGuard⟩ :=
    endX_cageIlk_after_vat_ilks_to_raw_spot_guard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
      (k := k) (C := C) (world := cur.world)
      hperm houtVat h160Vat
      (by simpa [hpc, hstack, hmem, haw, endCageIlkAfterVatIlksCursor] using rd)
  have hslotSpot := endPackSlotLoad_eq_of_callRel hrelArt (UInt256.ofNat 6)
  have hreceiver :
      evalExpr? config (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
        (.storage spotRef) =
        .ok (.address (AccountAddress.ofNat (endCageIlkSpotTarget worldArt.2 I).toNat)) := by
    rw [endEvalSpotAddress_cageIlk]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evmArt evmArt.executionEnv.codeOwner
        (UInt256.ofNat 6)) solcAddrMask).toNat)) =
      EvalResult.ok (Value.address
        (AccountAddress.ofNat (endCageIlkSpotTarget worldArt.2 I).toNat))
    rw [hslotSpot]
  by_cases hspotNoCode :
      extCodeSizeWord worldArt.2 (endCageIlkSpotTarget worldArt.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evmArt.accountMap (endCageIlkSpotTarget worldArt.2 I) = ⟨0⟩ := by
      rw [← extCodeSizeWord_accountMapEquiv hrelArt.accounts]
      exact hspotNoCode
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_false
        (locals := (endCageIlkAfterVatIlksFrame I cur.rdata).locals)
        (receiver := .storage spotRef) hreceiver hsrcNoCode
    have hsource :
        ExecBlock config (endCageIlkAfterVatIlksFrame I cur.rdata) evm
          ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
            checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
              [.var "ilk"] "spotIlk" (perm := false) ++
            [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
            checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
              (perm := false) ++
            checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
              (perm := false) ++
            endCageIlkWdivTagStmts)
          .reverted := by
      simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts, List.append_assoc] using
        (ExecBlock.consNormal hassignStmt
          (ExecBlock.consRevert (ExecStmt.requireFalse hguard)))
    have hrev :=
      endX_cageIlk_spot_ilks_no_code
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awGuard) (out := cur.rdata)
        (k := kGuard) (C := CGuard) (world := worldArt) hspotNoCode
        (by simpa [worldArt] using rdGuard)
    exact Or.inl (BlockProgress.ofRDrev hsource hrev)
  · have hsrcCode :
        extCodeSizeWord evmArt.accountMap (endCageIlkSpotTarget worldArt.2 I) ≠ ⟨0⟩ := by
      intro hz
      exact hspotNoCode (by
        rw [extCodeSizeWord_accountMapEquiv hrelArt.accounts]
        exact hz)
    have hguard :=
      endEvalCodeSizeGuard_cageIlk_true
        (locals := (endCageIlkAfterVatIlksFrame I cur.rdata).locals)
        (receiver := .storage spotRef) hreceiver hsrcCode
    have hassignGuardBlock :
        ExecBlock config (endCageIlkAfterVatIlksFrame I cur.rdata) evm
          [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0),
            .require (.binary .gt (.extCodeSize (.storage spotRef)) (.intLit 0)) ]
          (.ok (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt) :=
      ExecBlock.consNormal hassignStmt <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
    obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
      endX_cageIlk_spot_ilks_guard_to_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awGuard) (out := cur.rdata)
        (k := kGuard) (C := CGuard) (world := worldArt) hspotNoCode
        (by simpa [worldArt] using rdGuard)
    have hcallProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
          [ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
              "spotIlk" (perm := false) ]
          (sequenceExit ⟨9255⟩
            (fun curAfter frameAfter evmAfter =>
              frameAfter = endCageIlkAfterSpotIlksFrame I cur.rdata curAfter.rdata ∧
              CallStateRel (initState cA gh bl σ σ₀ g A I) I curAfter.world evmAfter ∧
              accountStaticStateEq evmArt.accountMap evmAfter.accountMap ∧
              curAfter.rdata.size < UInt256.size ∧
              64 ≤ curAfter.rdata.size ∧
              curAfter.stack =
                [UInt256.ofNat curAfter.rdata.size,
                  memLoad (UInt256.ofNat 64)
                    (endCageIlkSpotIlksReturnMem I cur.rdata curAfter.rdata),
                  ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
              curAfter.mem = endCageIlkSpotIlksReturnMem I cur.rdata curAfter.rdata ∧
              curAfter.aw = endCageIlkAfterSpotIlksAw awCall)
            (runtimeExit (.abi []))) :=
      (endCageIlkSpotIlksExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
        (outVat := cur.rdata) (rdata := cur.rdata) (k := kCall) (C := CCall)
        (evm := evmArt) (world := worldArt) hsz36 houtVat h160Vat)
        (by simpa [endCageIlkSpotIlksCallCursor] using rdCall)
        hrelArt
    rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
    cases result with
    | ok frameAfter evmAfter =>
        cases endpoint with
        | reached curAfter =>
            simp only [sequenceExit, fallthrough] at hQ
            rcases hQ with ⟨hpcAfter, hAfter⟩
            rcases hAfter with
              ⟨hframeAfter, hrelAfter, _hstaticAfter, houtSpot, h64Spot,
                hstackAfter, hmemAfter, hawAfter⟩
            rcases hreachEndpoint with ⟨kAfter, CAfter, rdAfter⟩
            have hsuffix :=
              endCageIlkAfterSpotSuffixProgressOrInvalid
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := sel) (aw := awCall)
                (outVat := cur.rdata) (cur := curAfter) (k := kAfter)
                (C := CAfter) (frame := frameAfter) (evm := evmAfter)
                hperm hsz36 houtVat h160Vat hpcAfter rdAfter
                ⟨hframeAfter, hrelAfter, houtSpot, h64Spot, hstackAfter, hmemAfter,
                  hawAfter⟩
            cases hsuffix with
            | inl hsuffixProgress =>
                have hcallSuffixProgress :
                    BlockProgress endBytecode I g
                      (initState cA gh bl σ σ₀ g A I) config
                      (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
                      ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ] ++
                        ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0)
                            [] "parV" (perm := false) ++
                          checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                            "pipRead" (perm := false) ++
                          endCageIlkWdivTagStmts))
                      (runtimeExit (.abi [])) :=
                  BlockProgress.prepend hcallBlock hsuffixProgress
                have hprogress := BlockProgress.prepend hassignGuardBlock hcallSuffixProgress
                exact Or.inl (by
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hprogress)
            | inr hinvalid =>
                rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                have hcallSuffixBlock :
                    ExecBlock config (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
                      ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ] ++
                        ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                          checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0)
                            [] "parV" (perm := false) ++
                          checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                            "pipRead" (perm := false) ++
                          endCageIlkWdivTagStmts))
                      .reverted :=
                  Reasoning.Theory.execBlock_append hcallBlock hsuffixBlock
                have hfullBlock :
                    ExecBlock config (endCageIlkAfterVatIlksFrame I cur.rdata) evm
                      ([ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts)
                      .reverted := by
                  have hcombined :=
                    Reasoning.Theory.execBlock_append hassignGuardBlock hcallSuffixBlock
                  simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
                    List.append_assoc] using hcombined
                exact Or.inr ⟨hfullBlock, hinv⟩
        | returned world out =>
            simp [sequenceExit, fallthrough] at hQ
        | reverted =>
            simp [sequenceExit, fallthrough] at hQ
    | returned frameRet evmRet value =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
              ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
                  "spotIlk" (perm := false) ] ++
                ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                  checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
                    (perm := false) ++
                  checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                    (perm := false) ++
                  endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hassignGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | reverted =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
              ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
                  "spotIlk" (perm := false) ] ++
                ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                  checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
                    (perm := false) ++
                  checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                    (perm := false) ++
                  endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hassignGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «break» frameBreak evmBreak =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
              ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
                  "spotIlk" (perm := false) ] ++
                ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                  checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
                    (perm := false) ++
                  checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                    (perm := false) ++
                  endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hassignGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)
    | «continue» frameContinue evmContinue =>
        have hcallSuffixProgress :
            BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
              (endCageIlkAfterVatIlksFrame I cur.rdata) evmArt
              ([ .externalCall (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
                  "spotIlk" (perm := false) ] ++
                ([ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                  checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
                    (perm := false) ++
                  checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
                    (perm := false) ++
                  endCageIlkWdivTagStmts))
              (runtimeExit (.abi [])) := by
          refine ⟨.continue frameContinue evmContinue, endpoint, ?_, hreachEndpoint, ?_⟩
          · exact Reasoning.Theory.execBlock_append_term hcallBlock
              (by intro f e h; cases h)
          · simpa [sequenceExit] using hQ
        have hprogress := BlockProgress.prepend hassignGuardBlock hcallSuffixProgress
        exact Or.inl (by
          simpa [checkedExternalCallStmts, endCageIlkWdivTagStmts,
            List.append_assoc] using hprogress)

theorem endCageIlkTagWord_init_eq (cA gh bl σ σ₀ A I) (g : Sat256)
    (hsz36 : 36 ≤ I.calldata.size) :
    endCageIlkTagWord (initState cA gh bl σ σ₀ g A I) I =
      endCageIlkTagWorldWord σ I := by
  unfold endCageIlkTagWord endCageIlkTagWorldWord endCageIlkTagWorldSlot
  change Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (tagSlot (endArg0Bytes32Key I)) =
    storageRead I.codeOwner σ (solcMappingSlot (UInt256.ofNat 12) (endArg0Word I))
  rw [endPackStorageLoad_init_eq]
  rw [endTagSlot_eq I hsz36]
  rw [storageRead_eq]
  rfl

theorem endX_cageIlk_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (htag : endCageIlkTagWorldWord σ I = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw8999, k8999, C8999, rd8999⟩ :=
    endX_cageIlk_to_vat_ilks_setup (g := g) hsz36 hsize hlive htag hreach
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (storageRead I.codeOwner σ (UInt256.ofNat 1))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) = UInt256.ofNat 0 := by
    rw [hmaskGenerated]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
    change UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
      UInt256.ofNat 0
    rw [hvatNoCode]
    decide
  obtain ⟨aw9073, k9073, C9073, rd9073⟩ :=
    endRuntimeBlocks.endRuntime_block_8999_fallthrough_packed
      (mem := endCageIlkVatIlksBaseMem I) (x0 := endArg0Word I)
      (R := [⟨562⟩, sel]) (by simp) hcond rd8999
  exact endRuntimeBlocks.endRuntime_block_9073
    (R := endRuntimeBlocks.endRuntime_block_8999_fallthrough_stack (ee := I)
      (mem := endCageIlkVatIlksBaseMem I) (σ := σ) (x0 := endArg0Word I)
      (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_8999_fallthrough_stack])
    rd9073

set_option maxHeartbeats 12000000 in
theorem endCageIlkBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 23))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1171⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 23 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some cageIlkTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 23 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some cageIlkTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (cageIlkTransition.params.map Param.name) (transitionSignature cageIlkTransition).paramTypes
        I.calldata = some (endCageIlkStore I) := by
      simpa [config, cageIlkTransition, transitionSignature, bytes32, endCageIlkStore]
        using endDecode_legacyBytes32_ilk_ok (I := I) hsz36
    have hLiveWord :
        solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hliveSolm : solcSlotWord σ_solm I ⟨8⟩ = ⟨0⟩
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ = ⟨0⟩ :=
        hLiveWord.trans hliveSolm
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ = ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hliveSolm
      have hTagWord :
          endCageIlkTagWorldWord σ_evm I = endCageIlkTagWorldWord σ_solm I := by
        unfold endCageIlkTagWorldWord
        simpa [storageRead_eq] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (endCageIlkTagWorldSlot I) ⟨0⟩
      by_cases htagSolm : endCageIlkTagWorldWord σ_solm I = ⟨0⟩
      · have htagEvm : endCageIlkTagWorldWord σ_evm I = ⟨0⟩ :=
          hTagWord.trans htagSolm
        have htagSrc :
            endCageIlkTagWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = ⟨0⟩ := by
          rw [endCageIlkTagWord_init_eq cA gh bl σ_solm σ₀ A I
            (Sat256.ofUInt256 g) hsz36]
          exact htagSolm
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
                (endCageIlkStore I) cageIlkTransition.body .reverted := by
            simpa [initState] using
              endCageIlkBodyVatNoCode
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hsz36 hliveSrc htagSrc
                hvatNoCodeSrc
          exact (endX_cageIlk_vat_no_code (g := Sat256.ofUInt256 g)
              hsz36 hsize hliveEvm htagEvm hvatNoCodeEvm hreach)
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
            endX_cageIlk_to_vat_ilks_call
              (g := Sat256.ofUInt256 g) hsz36 hsize hliveEvm htagEvm hvatNoCodeEvm
              hreach
          have hprefix :
              ExecBlock config { contract := contract, locals := endCageIlkStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (nonpayable ++
                  [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                    .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)),
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
                (.ok { contract := contract, locals := endCageIlkStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
            endCageIlkBodyPrefixOk
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz36 hliveSrc htagSrc hvatCodeSrc
          have hpostRel :
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
                (cA, σ_evm)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
            CallStateRel.initState hAccounts
          have finishProgress :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endCageIlkStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                cageIlkTransition.body (runtimeExit (.abi [])) →
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
                config { contract := contract, locals := endCageIlkStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
                    "vatIlk" ]
                (sequenceExit ⟨9119⟩
                  (fun cur frame e =>
                    frame = endCageIlkAfterVatIlksFrame I cur.rdata ∧
                    CallStateRel
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      I cur.world e ∧
                    cur.rdata.size < UInt256.size ∧
                    160 ≤ cur.rdata.size ∧
                    cur.stack =
                      [UInt256.ofNat cur.rdata.size,
                        memLoad (UInt256.ofNat 64) (endCageIlkVatIlksReturnMem I cur.rdata),
                        endArg0Word I, ⟨562⟩, sel] ∧
                    cur.mem = endCageIlkVatIlksReturnMem I cur.rdata ∧
                    cur.aw = endCageIlkAfterVatIlksAw awCall)
                  (runtimeExit (.abi []))) :=
            (endCageIlkVatIlksExternalCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) (rdata := ByteArray.empty) (k := kCall)
              (C := CCall)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              hperm hsz36)
              (by simpa [endCageIlkVatIlksCallCursor] using rdCall)
              hpostRel
          rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
          cases result with
          | ok frameAfter evmAfter =>
              cases endpoint with
              | reached curAfter =>
                  simp only [sequenceExit, fallthrough] at hQ
                  rcases hQ with ⟨hpcAfter, hAfter⟩
                  rcases hAfter with
                    ⟨hframeAfter, hrelAfter, houtVat, h160Vat, hstackAfter, hmemAfter,
                      hawAfter⟩
                  rcases hreachEndpoint with ⟨kAfter, CAfter, rdAfter⟩
                  have hsuffix :=
                    endCageIlkAfterVatSuffixProgressOrInvalid
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                      (aw := awCall) (cur := curAfter) (k := kAfter) (C := CAfter)
                      (frame := frameAfter) (evm := evmAfter)
                      hperm hsz36 hpcAfter rdAfter
                      ⟨hframeAfter, hrelAfter, houtVat, h160Vat, hstackAfter, hmemAfter,
                        hawAfter⟩
                  cases hsuffix with
                  | inl hsuffixProgress =>
                      have hcallSuffixProgress :
                          BlockProgress endBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            config { contract := contract, locals := endCageIlkStore I }
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                                [.var "ilk"] "vatIlk" ] ++
                              ([ .assign .storage (ArtRef (.var "ilk"))
                                  (.tupleGet (.var "vatIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "spotIlks"
                                  (.intLit 0) [.var "ilk"] "spotIlk" (perm := false) ++
                                [ .letDecl "pip" (some addr)
                                    (.tupleGet (.var "spotIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "par"
                                  (.intLit 0) [] "parV" (perm := false) ++
                                checkedExternalCallStmts (.var "pip") "read"
                                  (.intLit 0) [] "pipRead" (perm := false) ++
                                endCageIlkWdivTagStmts))
                            (runtimeExit (.abi [])) :=
                        BlockProgress.prepend hcallBlock hsuffixProgress
                      have hprogress :=
                        BlockProgress.prepend hprefix hcallSuffixProgress
                      exact finishProgress (by
                        simpa [cageIlkTransition, checkedExternalCallStmts,
                          endCageIlkWdivTagStmts, List.append_assoc] using hprogress)
                  | inr hinvalid =>
                      rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                      have hcallSuffixBlock :
                          ExecBlock config { contract := contract, locals := endCageIlkStore I }
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                                [.var "ilk"] "vatIlk" ] ++
                              ([ .assign .storage (ArtRef (.var "ilk"))
                                  (.tupleGet (.var "vatIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "spotIlks"
                                  (.intLit 0) [.var "ilk"] "spotIlk" (perm := false) ++
                                [ .letDecl "pip" (some addr)
                                    (.tupleGet (.var "spotIlk") 0) ] ++
                                checkedExternalCallStmts (.storage spotRef) "par"
                                  (.intLit 0) [] "parV" (perm := false) ++
                                checkedExternalCallStmts (.var "pip") "read"
                                  (.intLit 0) [] "pipRead" (perm := false) ++
                                endCageIlkWdivTagStmts))
                            .reverted :=
                        Reasoning.Theory.execBlock_append hcallBlock hsuffixBlock
                      have hfullBlock :=
                        Reasoning.Theory.execBlock_append hprefix hcallSuffixBlock
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (endCageIlkStore I) cageIlkTransition.body .reverted := by
                        have hblock :
                            ExecBlock config { contract := contract, locals := endCageIlkStore I }
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              cageIlkTransition.body .reverted := by
                          simpa [cageIlkTransition, checkedExternalCallStmts,
                            endCageIlkWdivTagStmts, List.append_assoc] using hfullBlock
                        simpa [ExecTransitionBody] using execFuncBody_of_execBlock hblock
                      exact endRDinvalidReEquivExecutionRevert hcode hinv hd hdec hbody rfl rfl
              | returned world out =>
                  simp [sequenceExit, fallthrough] at hQ
              | reverted =>
                  simp [sequenceExit, fallthrough] at hQ
          | returned frameRet evmRet value =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endCageIlkStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      ([ .assign .storage (ArtRef (.var "ilk"))
                          (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                    (runtimeExit (.abi [])) := by
                refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [cageIlkTransition, checkedExternalCallStmts,
                  endCageIlkWdivTagStmts, List.append_assoc] using hprogress)
          | reverted =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endCageIlkStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      ([ .assign .storage (ArtRef (.var "ilk"))
                          (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                    (runtimeExit (.abi [])) := by
                refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [cageIlkTransition, checkedExternalCallStmts,
                  endCageIlkWdivTagStmts, List.append_assoc] using hprogress)
          | «break» frameBreak evmBreak =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endCageIlkStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      ([ .assign .storage (ArtRef (.var "ilk"))
                          (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                    (runtimeExit (.abi [])) := by
                refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [cageIlkTransition, checkedExternalCallStmts,
                  endCageIlkWdivTagStmts, List.append_assoc] using hprogress)
          | «continue» frameContinue evmContinue =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endCageIlkStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      ([ .assign .storage (ArtRef (.var "ilk"))
                          (.tupleGet (.var "vatIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0)
                          [.var "ilk"] "spotIlk" (perm := false) ++
                        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
                        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) []
                          "parV" (perm := false) ++
                        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) []
                          "pipRead" (perm := false) ++
                        endCageIlkWdivTagStmts))
                    (runtimeExit (.abi [])) := by
                refine ⟨.continue frameContinue evmContinue, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [cageIlkTransition, checkedExternalCallStmts,
                  endCageIlkWdivTagStmts, List.append_assoc] using hprogress)
      · have htagEvm : endCageIlkTagWorldWord σ_evm I ≠ ⟨0⟩ := by
          intro hbad
          exact htagSolm (hTagWord.symm.trans hbad)
        have htagSrc :
            endCageIlkTagWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠ ⟨0⟩ := by
          rw [endCageIlkTagWord_init_eq cA gh bl σ_solm σ₀ A I
            (Sat256.ofUInt256 g) hsz36]
          exact htagSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endCageIlkStore I) cageIlkTransition.body .reverted := by
          simpa [initState] using
            endCageIlkBodyTagFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz36 hliveSrc htagSrc
        exact (endX_cageIlk_tag_fail (g := Sat256.ofUInt256 g)
            hsz36 hsize hliveEvm htagEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ ≠ ⟨0⟩ := by
        intro hbad
        exact hliveSolm (hLiveWord.symm.trans hbad)
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hliveSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endCageIlkStore I) cageIlkTransition.body .reverted := by
        simpa [initState] using
          endCageIlkBodyLiveFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hliveSrc
      exact (endX_cageIlk_live_fail (g := Sat256.ofUInt256 g)
          hsz36 hsize hliveEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (cageIlkTransition.params.map Param.name) (transitionSignature cageIlkTransition).paramTypes
        I.calldata = none := by
      simpa [config, cageIlkTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_ilk_none_short (I := I) hsz4 hshort
    exact (endX_cageIlk_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
