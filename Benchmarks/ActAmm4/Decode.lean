import Benchmarks.ActAmm4.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

-- LIBRARY CANDIDATE: Reasoning.ABI, decoding a uint256 followed by an address.
theorem amm4DecodeScalarWords_uint256_address_ok {bytes : List UInt8}
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

theorem amm4DecodeScalarWords_uint256_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiUInt256, .elem .address] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc]

theorem amm4DecodeScalarWords_uint256_address_none_short {bytes : List UInt8}
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

theorem amm4DecodeCalldata_uint256_address_ok {cd : ByteArray} {x y : Ident}
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
  rw [amm4DecodeScalarWords_uint256_address_ok (bytes := cd.toList.drop 4)
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

theorem amm4DecodeCalldata_uint256_address_none_noncanon {cd : ByteArray} {x y : Ident}
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
  rw [amm4DecodeScalarWords_uint256_address_none_noncanon (bytes := cd.toList.drop 4)
    htake4 htake36' (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
        calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hword36]
      exact hnc)]

theorem amm4DecodeCalldata_uint256_address_none_short {cd : ByteArray} {x y : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [amm4DecodeScalarWords_uint256_address_none_short (bytes := cd.toList.drop 4)
    (by rw [List.length_drop, htlen]; omega)]

theorem amm4DecodeCalldata_uint256_address_none_huge {cd : ByteArray} {x y : Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y])
    (types := [abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

-- LIBRARY CANDIDATE: Reasoning.ABI, two uint256 arguments followed by an address.
theorem amm4DecodeScalarWords_uint256_uint256_address_ok {bytes : List UInt8}
    (h0 : (bytes.take 32).length = 32)
    (h32 : ((bytes.drop 32).take 32).length = 32)
    (h64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon : (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiUInt256, abiUInt256, .elem .address] bytes 0 =
      some [.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) h0]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) h32]
  rw [decodeScalarWord_address_ok (start := 64) h64 hcanon]
  rfl

theorem amm4DecodeScalarWords_uint256_uint256_address_none_noncanon
    {bytes : List UInt8}
    (h0 : (bytes.take 32).length = 32)
    (h32 : ((bytes.drop 32).take 32).length = 32)
    (h64 : ((bytes.drop 64).take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [abiUInt256, abiUInt256, .elem .address] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (start := 0) h0]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) h32]
  rw [decodeScalarWord_address_none_noncanon (start := 64) h64 hnc]

theorem amm4DecodeScalarWords_uint256_uint256_address_none_short
    {bytes : List UInt8} (hshort : bytes.length < 96) :
    decodeScalarWords? [abiUInt256, abiUInt256, .elem .address] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hn : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_uint256_none_short (start := 0) hn]
    simp only [Option.bind, bind]
  · have h0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]; omega
    rw [decodeScalarWord_uint256_ok (start := 0) h0]
    simp only [Option.bind, bind]
    by_cases h64 : bytes.length < 64
    · have hn : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      rw [decodeScalarWord_uint256_none_short (start := 32) hn]
    · have h32' : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      rw [decodeScalarWord_uint256_ok (start := 32) h32']
      have hn : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]; omega
      rw [decodeScalarWord_address_none_short (start := 64) hn]

theorem amm4DecodeCalldata_uint256_uint256_address_ok
    {cd : ByteArray} {x y z : Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 68).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [abiUInt256, abiUInt256, .elem .address] cd =
      some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [amm4DecodeScalarWords_uint256_uint256_address_ok (bytes := cd.toList.drop 4)
    htake4 htake36' htake68' (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
        calldataWord cd 68 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hword68]
      exact hcanon)]
  change decodeCalldata.insertValues [x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ = _
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68]

theorem amm4DecodeCalldata_uint256_uint256_address_none_noncanon
    {cd : ByteArray} {x y z : Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 68).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [abiUInt256, abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [amm4DecodeScalarWords_uint256_uint256_address_none_noncanon
    (bytes := cd.toList.drop 4) htake4 htake36' htake68' (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
        calldataWord cd 68 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hword68]
      exact hnc)]

theorem amm4DecodeCalldata_uint256_uint256_address_none_short
    {cd : ByteArray} {x y z : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [abiUInt256, abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [amm4DecodeScalarWords_uint256_uint256_address_none_short
    (bytes := cd.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]

theorem amm4DecodeCalldata_uint256_uint256_address_none_huge
    {cd : ByteArray} {x y z : Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [abiUInt256, abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, .elem .address]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

end Benchmarks.ActAmm4
