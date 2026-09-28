import Benchmarks.ActAmmToken.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmmToken

-- LIBRARY CANDIDATE: Reasoning.ABI, decoding a uint256 followed by an address.
theorem tokenDecodeScalarWords_uint256_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiUInt256, .elem .address] bytes 0 =
      some [.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon]
  rfl

theorem tokenDecodeScalarWords_uint256_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiUInt256, .elem .address] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc]

theorem tokenDecodeScalarWords_uint256_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeScalarWords? [abiUInt256, .elem .address] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_uint256_none_short (start := 0) htake0n]
    rfl
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]; omega
    rw [decodeScalarWord_uint256_ok (start := 0) htake0]
    simp only [Option.bind, bind]
    rw [decodeScalarWord_address_none_short (start := 32) htake32n]

theorem tokenDecodeCalldata_uint256_address_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert
        y (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [tokenDecodeScalarWords_uint256_address_ok (bytes := cd.toList.drop 4)
    htake4 htake36' (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hword36]
      exact hcanon)]
  change decodeCalldata.insertValues [x, y]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ = _
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem tokenDecodeCalldata_uint256_address_none_noncanon {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [tokenDecodeScalarWords_uint256_address_none_noncanon (bytes := cd.toList.drop 4)
    htake4 htake36' (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hword36]
      exact hnc)]

theorem tokenDecodeCalldata_uint256_address_none_short {cd : ByteArray} {x y : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [tokenDecodeScalarWords_uint256_address_none_short (bytes := cd.toList.drop 4)
    (by rw [List.length_drop, htlen]; omega)]

theorem tokenDecodeCalldata_uint256_address_none_huge {cd : ByteArray} {x y : Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

end Benchmarks.ActAmmToken
