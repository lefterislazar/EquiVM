import Examples.NestedCaller.Common

namespace NestedCaller

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

abbrev runTargetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev runCountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev runTarget (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (runTargetWord I).toNat

abbrev runTargetValue (I : ExecutionEnv) : Value :=
  .address (runTarget I)

abbrev runCountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (runCountWord I).toNat)

abbrev runArgStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "target" (runTargetValue I)).insert "count" (runCountValue I)

def addrMask : UInt256 :=
  ⟨1461501637330902918203684832716283019655932542975⟩

theorem ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  show UInt256.fromBool (decide (a = a)) = ⟨1⟩
  rw [decide_eq_true rfl]
  rfl

theorem ueq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) :
    UInt256.eq a b = ⟨0⟩ := by
  by_cases hab : a = b
  · subst hab
    exact absurd (ueq_self a) h
  · show UInt256.fromBool (decide (a = b)) = ⟨0⟩
    rw [decide_eq_false hab]
    rfl

theorem uadd_zero_right (a : UInt256) : a + (⟨0⟩ : UInt256) = a := by
  apply u256_inj
  rw [uadd_toNat]
  change (a.toNat + 0) % UInt256.size = a.toNat
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem u256_ofNat_add_local (a b : ℕ) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat]
  show ((a % UInt256.size) + (b % UInt256.size)) % UInt256.size =
    (a + b) % UInt256.size
  rw [← Nat.add_mod]

theorem usub_uadd_word_ofNat_cancel (fp : UInt256) {n : ℕ} (hn : n < UInt256.size) :
    UInt256.sub (fp + UInt256.ofNat n) fp = UInt256.ofNat n := by
  have hfp : UInt256.ofNat fp.toNat = fp := by
    apply u256_inj
    rw [ulit_toNat' fp.toNat fp.val.isLt]
  simpa [hfp] using
    (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := n) fp.val.isLt hn)

theorem usub_uadd_word_36_cancel (fp : UInt256) :
    UInt256.sub (fp + UInt256.ofNat 36) fp = UInt256.ofNat 36 := by
  exact usub_uadd_word_ofNat_cancel fp (by decide)

theorem runTargetWord_canonical {I : ExecutionEnv}
    (hclean : UInt256.eq (runTargetWord I) (UInt256.land (runTargetWord I) addrMask) = ⟨1⟩) :
    (runTargetWord I).toNat < EVM.addressModulus := by
  have heq : runTargetWord I = UInt256.land (runTargetWord I) addrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  have hland : (runTargetWord I).toNat
      = Nat.land (runTargetWord I).toNat addrMask.toNat % EVM.twoPow 256 := by
    conv_lhs => rw [heq]
    rfl
  have hmod : Nat.land (runTargetWord I).toNat addrMask.toNat % EVM.twoPow 256
      = Nat.land (runTargetWord I).toNat addrMask.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (hlandle _ _) (by decide))
  have hmask : addrMask.toNat < EVM.addressModulus := by decide
  rw [hland, hmod]
  exact lt_of_le_of_lt (hlandle _ _) hmask

theorem runTargetWord_canon_eq {I : ExecutionEnv}
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus) :
    UInt256.eq (runTargetWord I) (UInt256.land (runTargetWord I) addrMask) = ⟨1⟩ := by
  have hland : UInt256.land (runTargetWord I) addrMask = runTargetWord I := by
    apply u256_inj
    show Nat.land (runTargetWord I).toNat addrMask.toNat % EVM.twoPow 256
      = (runTargetWord I).toNat
    rw [show addrMask.toNat = 2 ^ 160 - 1 from by decide,
      land_mask160 _ (by
        rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hcanon
        exact hcanon)]
    exact Nat.mod_eq_of_lt (by
      have hlt : (runTargetWord I).toNat < UInt256.size := (runTargetWord I).val.isLt
      simpa [UInt256.size, EVM.twoPow] using hlt)
  rw [hland]
  exact ueq_self (runTargetWord I)

theorem nestedCallerLand_target {I : ExecutionEnv}
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus) :
    UInt256.land addrMask (runTargetWord I) = runTargetWord I := by
  simpa [addrMask, solcAddrMask] using
    (solcAddrMask_clean_left (w := runTargetWord I) hcanon)

theorem nestedCallerTarget_eq {I : ExecutionEnv}
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus) :
    EVM.address (runTarget I)
      = AccountAddress.ofUInt256 (UInt256.land addrMask (runTargetWord I)) := by
  rw [nestedCallerLand_target hcanon]
  apply Fin.ext
  show (runTargetWord I).toNat % EVM.addressModulus % AccountAddress.size
      = (runTargetWord I).val % AccountAddress.size % AccountAddress.size
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  rfl

theorem nestedCallerDecode_run {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
      (transitionSignature runTransition).paramTypes I.calldata =
        some (runArgStore I) := by
  simpa [runTransition, addr, uint256, runArgStore, runTargetValue, runTarget,
    runTargetWord, runCountValue, runCountWord] using
    decodeCalldata_addr_uint256_ok (cd := I.calldata) (x := "target") (y := "count")
      hsz68 hbig hcanon

theorem nestedCallerDecode_run_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (runTransition.params.map Param.name)
      (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256] using
    decodeCalldata_addr_uint256_none_short (cd := I.calldata) (x := "target") (y := "count")
      hsz4 hshort

theorem nestedCallerDecode_run_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (runTransition.params.map Param.name)
      (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256] using
    decodeCalldata_addr_uint256_none_huge (cd := I.calldata) (x := "target") (y := "count")
      hbig

theorem nestedCallerDecode_run_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (runTargetWord I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
      (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256, runTargetWord] using
    decodeCalldata_addr_uint256_none_noncanon (cd := I.calldata) (x := "target") (y := "count")
      hsz68 hbig hnc

theorem nestedCallerDecodeReturn_uint256_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < (2 : Nat) ^ 255) :
    nestedCallerConfig.externalABI.decode? "probe" returndata =
      some [(.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))))] := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  show defaultDecodeReturn? "probe" returndata = _
  rw [defaultDecodeReturn?, decodeReturnValues_scalarWords_eq (types := [uint256])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_ok (bytes := returndata.toList) htake0]
  rw [hword]
  simp [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem nestedCallerDecodeReturn_uint256_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    nestedCallerConfig.externalABI.decode? "probe" returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  show defaultDecodeReturn? "probe" returndata = none
  rw [defaultDecodeReturn?, decodeReturnValues_scalarWords_eq (types := [uint256])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_none_short (bytes := returndata.toList) (by rw [hlen]; omega)]

theorem nestedCallerDecodeReturn_uint256_none_huge {returndata : ByteArray}
    (hhuge : (2 : Nat) ^ 255 ≤ returndata.size) :
    nestedCallerConfig.externalABI.decode? "probe" returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  show defaultDecodeReturn? "probe" returndata = none
  rw [defaultDecodeReturn?, decodeReturnValues_scalarWords_eq (types := [uint256])
    (returndata := returndata) (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

theorem nestedCallerEncodeProbe_eq (i : UInt256) :
    nestedCallerConfig.externalABI.encode? "probe" [.int (Int.ofNat i.toNat)]
      = some (probeSelector ++ i.toByteArray) := by
  simp [nestedCallerConfig, probeSelector]
  change UInt256.toByteArray (EVM.wordOfInt (Int.ofNat i.toNat)) = i.toByteArray
  rw [wordOfInt_ofNat_toNat]

def probeSelectorShifted : UInt256 :=
  solcLeftAlignedSelectorWord (UInt256.ofNat 3674743872)

def probeSelectorMem (mem : ByteArray) (fp : UInt256) : ByteArray :=
  probeSelectorShifted.toByteArray.write 0 mem fp.toNat 32

def probeCalldataMem (mem : ByteArray) (fp i : UInt256) : ByteArray :=
  i.toByteArray.write 0 (probeSelectorMem mem fp) (fp + UInt256.ofNat 4).toNat 32

def retAligned (o : ByteArray) : UInt256 :=
  UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31))

def callOutLen (o : ByteArray) : Nat :=
  (min (UInt256.ofNat 32) (UInt256.ofNat o.size)).toNat

theorem retAligned_toNat_lt_2pow139 (o : ByteArray) (ho : o.size < 2 ^ 138) :
    (retAligned o).toNat < 2 ^ 139 := by
  unfold retAligned
  rw [uland_toNat]
  have hsum : ((UInt256.ofNat o.size) + UInt256.ofNat 31).toNat = o.size + 31 := by
    have hosize : o.size < UInt256.size :=
      lt_size_of_lt_sign (lt_trans ho (by norm_num : (2 : Nat) ^ 138 < 2 ^ 255))
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hosize]
    rw [UInt256.toNat_ofNat_of_lt (by decide : 31 < UInt256.size)]
    rw [Nat.mod_eq_of_lt (by
      have hcap : (2 : Nat) ^ 138 + 31 < UInt256.size := by norm_num [UInt256.size]
      omega : o.size + 31 < UInt256.size)]
  rw [hsum]
  exact lt_of_le_of_lt Nat.and_le_left (by omega)

theorem retAligned_nonneg (o : ByteArray) : 0 ≤ (retAligned o).toNat := Nat.zero_le _

theorem retAligned_toNat_le_size_add31 (o : ByteArray) (ho : o.size < 2 ^ 138) :
    (retAligned o).toNat ≤ o.size + 31 := by
  unfold retAligned
  rw [uland_toNat]
  have hsum : ((UInt256.ofNat o.size) + UInt256.ofNat 31).toNat = o.size + 31 := by
    have hosize : o.size < UInt256.size :=
      lt_size_of_lt_sign (lt_trans ho (by norm_num : (2 : Nat) ^ 138 < 2 ^ 255))
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hosize]
    rw [UInt256.toNat_ofNat_of_lt (by decide : 31 < UInt256.size)]
    rw [Nat.mod_eq_of_lt (by
      have hcap : (2 : Nat) ^ 138 + 31 < UInt256.size := by norm_num [UInt256.size]
      omega : o.size + 31 < UInt256.size)]
  rw [hsum]
  exact Nat.and_le_left

theorem callOutLen_eq32 (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    callOutLen o = 32 := by
  unfold callOutLen
  exact umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi

theorem callOutLen_eq_size (o : ByteArray)
    (hlo : o.size < 32) (hhi : o.size < UInt256.size) :
    callOutLen o = o.size := by
  unfold callOutLen
  exact umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hlo hhi

theorem callOutLen_le32 (o : ByteArray) (hhi : o.size < UInt256.size) :
    callOutLen o ≤ 32 := by
  by_cases hlo : 32 ≤ o.size
  · rw [callOutLen_eq32 o hlo hhi]
  · have hlt : o.size < 32 := Nat.lt_of_not_ge hlo
    rw [callOutLen_eq_size o hlt hhi]
    omega

theorem callOutLen_le_size (o : ByteArray) (hhi : o.size < UInt256.size) :
    callOutLen o ≤ o.size := by
  by_cases hlo : 32 ≤ o.size
  · rw [callOutLen_eq32 o hlo hhi]
    exact hlo
  · have hlt : o.size < 32 := Nat.lt_of_not_ge hlo
    rw [callOutLen_eq_size o hlt hhi]

theorem uadd_toNat_of_lt {a b : UInt256} (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [uadd_toNat, Nat.mod_eq_of_lt h]

theorem active64_of_aw_toNat_ge3 {aw : UInt256}
    (hge : 3 ≤ aw.toNat) (hmul : aw.toNat * 32 < UInt256.size) :
    ¬ (UInt256.ofNat 64) ≥ aw * (⟨32⟩ : UInt256) := by
  intro h
  have hprod : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    exact umul_toNat aw (⟨32⟩ : UInt256)
      (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hmul)
  change (aw * (⟨32⟩ : UInt256)).toNat ≤ (UInt256.ofNat 64).toNat at h
  rw [hprod] at h
  change aw.toNat * 32 ≤ 64 at h
  omega

theorem readWithPadding_eq_toByteArray_ofNat (o : ByteArray) (readAddr : ℕ)
    (h : readAddr + 32 ≤ o.size) :
    o.readWithPadding readAddr 32 =
      UInt256.toByteArray (UInt256.ofNat
        (fromByteArrayBigEndian (o.extract readAddr (readAddr + 32)))) := by
  have hsize : (o.extract readAddr (readAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract o readAddr h]
  symm
  rw [← uInt256OfByteArray_eq (o.extract readAddr (readAddr + 32))]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray
    (uInt256OfByteArray (o.extract readAddr (readAddr + 32)))]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]
  simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize

theorem write_size_ge_base_extend (src base : ByteArray) (dest len : Nat)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hdest : dest ≤ base.size) :
    base.size ≤ (src.write 0 base dest len).size := by
  by_cases hin : dest + len ≤ base.size
  · rw [write_eq_gen src base dest len hlen hsrc hin, ByteArray.size_append,
      ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · rw [write_eq_gen_extend src base dest len hlen hsrc hdest (by omega),
      ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
    omega

theorem toByteArray_write_eq_no_gap (v : UInt256) (mem : ByteArray) (off : ℕ)
    (hoff : mem.size ≤ off) :
    (UInt256.toByteArray v).write 0 mem off 32
      = mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (off - mem.size)).data.size
          = (ffi.ByteArray.zeroes (off - mem.size)).size from rfl,
        ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32:ℕ) = 0)),
      if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
                rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]; show mem.size + (off - mem.size) = off; omega
  rw [hv, show (min 32 (32 - 0) : ℕ) = 32 from rfl,
      show min mem.size (off + 32) - (off + 32) = 0 from by omega,
      show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
        rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
      Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
      Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
      Array.append_empty]

theorem toByteArray_write_size_ge_off_add32_no_gap (b : UInt256) (mem : ByteArray) (off : ℕ) :
    off + 32 ≤ ((UInt256.toByteArray b).write 0 mem off 32).size := by
  by_cases hle : off ≤ mem.size
  · rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    rw [toByteArray_size]
    rw [Nat.min_eq_left hle]
    norm_num
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      toByteArray_size]
    omega

theorem toByteArray_write_read_back_no_gap (b : UInt256) (mem : ByteArray) (off : ℕ) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding off 32 =
      UInt256.toByteArray b := by
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact byteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray b) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
      rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]

theorem toByteArray_write_read_below_no_gap
    (b : UInt256) (mem : ByteArray) (off read : ℕ)
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below _ _ off read (by rw [toByteArray_size]) hle hbelow
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

theorem toByteArray_write_read_below_len_no_gap
    (b : UInt256) (mem : ByteArray) (off read len : ℕ)
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read len =
      mem.readWithPadding read len := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below_len _ _ off read len (by rw [toByteArray_size]) hle
      hbelow hread hpos hlen64
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract' _ read len hpos hlen64 hread).symm

theorem toByteArray_write_read_window_no_gap
    (b : UInt256) (mem : ByteArray) (off start len : Nat)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding (off + start) len =
      (UInt256.toByteArray b).extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · have hprefix : (mem.extract 0 off).size = off := by
      rw [ByteArray.size_extract]
      omega
    have hword : ((UInt256.toByteArray b).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, toByteArray_size]
      omega
    rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hword]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hprefix, hword]; omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]
    rw [extract_extract_BA]
    rw [show 0 + start = start by omega,
      show min (0 + (start + len)) 32 = start + len by omega]
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray b) (off + start) (off + start + len) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off + start - (mem.size + (off - mem.size)) = start by omega,
      show off + start + len - (mem.size + (off - mem.size)) = start + len by omega]

theorem probeSelectorShifted_extract :
    probeSelectorShifted.toByteArray.extract 0 4 = probeSelector := by
  native_decide

theorem probeCalldataMem_read_fp_4 {mem : ByteArray} {fp i : UInt256}
    (hfp4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4) :
    (probeCalldataMem mem fp i).readWithPadding fp.toNat 4 = probeSelector := by
  have hbelow : fp.toNat + 4 ≤ (fp + UInt256.ofNat 4).toNat := by
    rw [hfp4]
  unfold probeCalldataMem
  rw [toByteArray_write_read_below_len_no_gap
    (b := i) (mem := probeSelectorMem mem fp)
    (off := (fp + UInt256.ofNat 4).toNat) (read := fp.toNat) (len := 4)
    (hread := by
      unfold probeSelectorMem
      have hsize := toByteArray_write_size_ge_off_add32_no_gap probeSelectorShifted mem fp.toNat
      omega)
    (hbelow := hbelow)
    (hpos := by native_decide) (hlen64 := by native_decide)]
  unfold probeSelectorMem
  rw [show
    (probeSelectorShifted.toByteArray.write 0 mem fp.toNat 32).readWithPadding fp.toNat 4 =
      probeSelectorShifted.toByteArray.extract 0 4 from by
        simpa [Nat.add_zero] using
          (toByteArray_write_read_window_no_gap probeSelectorShifted mem fp.toNat 0 4
            (by omega) (by omega) (by omega))]
  exact probeSelectorShifted_extract

theorem probeCalldataMem_read_arg {mem : ByteArray} {fp i : UInt256}
    (hfp4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4) :
    (probeCalldataMem mem fp i).readWithPadding (fp.toNat + 4) 32 = i.toByteArray := by
  unfold probeCalldataMem
  rw [← hfp4]
  rw [toByteArray_write_read_back_no_gap
    (b := i) (mem := probeSelectorMem mem fp) (off := (fp + UInt256.ofNat 4).toNat)]

theorem probeCalldataMem_read {mem : ByteArray} {fp i : UInt256}
    (hfp4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4) :
    (probeCalldataMem mem fp i).readWithPadding fp.toNat 36 =
      probeSelector ++ i.toByteArray := by
  have hsize : fp.toNat + 36 ≤ (probeCalldataMem mem fp i).size := by
    unfold probeCalldataMem
    rw [hfp4]
    have hsizeArg := toByteArray_write_size_ge_off_add32_no_gap i (probeSelectorMem mem fp)
      (fp.toNat + 4)
    exact hsizeArg
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (probeCalldataMem mem fp i) fp.toNat 4 32
      (by omega) (by omega) (by native_decide) (by native_decide)
      (by native_decide) hsize]
  rw [probeCalldataMem_read_fp_4 hfp4, probeCalldataMem_read_arg hfp4]

theorem probeCalldataMem_size_ge_fp36 {mem : ByteArray} {fp i : UInt256}
    (hfp4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4) :
    fp.toNat + 36 ≤ (probeCalldataMem mem fp i).size := by
  unfold probeCalldataMem
  rw [hfp4]
  exact toByteArray_write_size_ge_off_add32_no_gap i (probeSelectorMem mem fp)
    (fp.toNat + 4)

theorem probeSelectorMem_size_ge_96 {mem : ByteArray} {fp : UInt256}
    (hmin : 96 ≤ fp.toNat) :
    96 ≤ (probeSelectorMem mem fp).size := by
  unfold probeSelectorMem
  have hsize := toByteArray_write_size_ge_off_add32_no_gap probeSelectorShifted mem fp.toNat
  omega

theorem probeSelectorMem_read64 {mem : ByteArray} {fp : UInt256}
    (hread : mem.readWithPadding 64 32 = fp.toByteArray)
    (hmem : 96 ≤ mem.size)
    (hmin : 96 ≤ fp.toNat) :
    (probeSelectorMem mem fp).readWithPadding 64 32 = fp.toByteArray := by
  unfold probeSelectorMem
  rw [toByteArray_write_read_below_no_gap probeSelectorShifted mem fp.toNat 64
    (hread := by omega)
    (hbelow := by omega)]
  exact hread

theorem probeCalldataMem_read64 {mem : ByteArray} {fp i : UInt256}
    (hread : mem.readWithPadding 64 32 = fp.toByteArray)
    (hmem : 96 ≤ mem.size)
    (hmin : 96 ≤ fp.toNat)
    (hfp4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4) :
    (probeCalldataMem mem fp i).readWithPadding 64 32 = fp.toByteArray := by
  unfold probeCalldataMem
  rw [hfp4]
  rw [toByteArray_write_read_below_no_gap i (probeSelectorMem mem fp) (fp.toNat + 4) 64
    (hread := by
      simpa using probeSelectorMem_size_ge_96 (mem := mem) (fp := fp) hmin)
    (hbelow := by omega)]
  exact probeSelectorMem_read64 hread hmem hmin

theorem fp_add4_toNat {fp : UInt256} (hfit : fp.toNat + 36 < UInt256.size) :
    (fp + UInt256.ofNat 4).toNat = fp.toNat + 4 := by
  rw [uadd_toNat]
  change (fp.toNat + 4) % UInt256.size = fp.toNat + 4
  rw [Nat.mod_eq_of_lt (by omega)]

theorem fp_callInputSize_eq (fp : UInt256) :
    UInt256.sub ((fp + UInt256.ofNat 4) + UInt256.ofNat 32) fp = UInt256.ofNat 36 := by
  rw [u256_add_assoc, u256_ofNat_add_local]
  exact usub_uadd_word_36_cancel fp

theorem MachineState_M_mul32_lt_of_bounds {s f l : Nat}
    (hs : s * 32 < UInt256.size) (hf : f + l + 31 < UInt256.size) :
    MachineState.M s f l * 32 < UInt256.size := by
  unfold MachineState.M
  split
  · exact hs
  · by_cases hle : s ≤ (f + l + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv := Nat.div_mul_le_self (f + l + 31) 32
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hs

theorem MachineState_M_ge_left (s f l : Nat) : s ≤ MachineState.M s f l := by
  unfold MachineState.M
  split
  · rfl
  · exact Nat.le_max_left _ _

theorem MachineState_M_covers_len {s f l : Nat} (hpos : 0 < l) :
    f + l ≤ MachineState.M s f l * 32 := by
  unfold MachineState.M
  cases l with
  | zero => omega
  | succ l =>
      have hceil : f + (l + 1) ≤ ((f + (l + 1) + 31) / 32) * 32 := by
        have hmod := Nat.mod_lt (f + (l + 1) + 31) (by norm_num : 0 < 32)
        have hdm := Nat.div_add_mod (f + (l + 1) + 31) 32
        omega
      exact le_trans hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))

theorem UInt256_ofNat_M_mul32_lt (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 <
      UInt256.size := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem UInt256_ofNat_M_len_mul32_lt (s f l : Nat)
    (hs : s * 32 < UInt256.size) (hf : f + l + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M s f l)).toNat * 32 < UInt256.size := by
  have hMmul := MachineState_M_mul32_lt_of_bounds hs hf
  have hMlt : MachineState.M s f l < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem UInt256_ofNat_M_toNat_ge (aw off : UInt256) {n : Nat}
    (hn : n ≤ aw.toNat)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    n ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact le_trans hn (MachineState_M_ge_left _ _ _)

theorem UInt256_ofNat_M_len_toNat_ge {s f l n : Nat}
    (hn : n ≤ s) (hs : s * 32 < UInt256.size) (hf : f + l + 31 < UInt256.size) :
    n ≤ (UInt256.ofNat (MachineState.M s f l)).toNat := by
  have hMmul := MachineState_M_mul32_lt_of_bounds hs hf
  have hMlt : MachineState.M s f l < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact le_trans hn (MachineState_M_ge_left _ _ _)

theorem UInt256_ofNat_M_covers (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    off.toNat + 32 ≤
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  unfold MachineState.M
  have hceil : off.toNat + 32 ≤ ((off.toNat + 32 + 31) / 32) * 32 := by
    have hmod := Nat.mod_lt (off.toNat + 32 + 31) (by norm_num : 0 < 32)
    have hdm := Nat.div_add_mod (off.toNat + 32 + 31) 32
    omega
  split
  · omega
  · exact le_trans hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))

theorem M_mul32_lt (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    (M aw off (⟨32⟩ : UInt256)).toNat * 32 < UInt256.size := by
  simpa [M, show (⟨32⟩ : UInt256).toNat = 32 from rfl] using
    UInt256_ofNat_M_mul32_lt aw off haw hoff

theorem M_toNat_ge (aw off : UInt256) {n : Nat}
    (hn : n ≤ aw.toNat)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    n ≤ (M aw off (⟨32⟩ : UInt256)).toNat := by
  simpa [M, show (⟨32⟩ : UInt256).toNat = 32 from rfl] using
    UInt256_ofNat_M_toNat_ge aw off hn haw hoff

theorem M_covers (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    off.toNat + 32 ≤ (M aw off (⟨32⟩ : UInt256)).toNat * 32 := by
  simpa [M, show (⟨32⟩ : UInt256).toNat = 32 from rfl] using
    UInt256_ofNat_M_covers aw off haw hoff

theorem probeSelectorMem_initial_read64 :
    (probeSelectorMem solcFreePtrMem (UInt256.ofNat 128)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold probeSelectorMem
  rw [show (UInt256.ofNat 128).toNat = 128 from by decide]
  rw [show UInt256.toByteArray (UInt256.ofNat 128) = UInt256.toByteArray (⟨128⟩ : UInt256) from by rfl]
  rw [toByteArray_write_read_below_no_gap probeSelectorShifted solcFreePtrMem 128 64
    (by rw [solcFreePtrMem_size])
    (by decide)]
  exact solcFreePtrMem_read64

theorem probeCalldataMem_initial_read64 (i : UInt256) :
    (probeCalldataMem solcFreePtrMem (UInt256.ofNat 128) i).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold probeCalldataMem
  rw [show ((UInt256.ofNat 128) + UInt256.ofNat 4).toNat = 132 from by decide]
  rw [toByteArray_write_read_below_no_gap i (probeSelectorMem solcFreePtrMem (UInt256.ofNat 128))
    132 64
    (by
      unfold probeSelectorMem
      rw [show (UInt256.ofNat 128).toNat = 128 from by decide]
      have hsize := toByteArray_write_size_ge_off_add32_no_gap probeSelectorShifted solcFreePtrMem 128
      omega)
    (by decide)]
  exact probeSelectorMem_initial_read64

theorem probeCalldataMem_initial_mload64 (i : UInt256) :
    memLoad (UInt256.ofNat 64)
      (M (M (M (UInt256.ofNat 3) (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        (UInt256.ofNat 128) (⟨32⟩ : UInt256))
        ((UInt256.ofNat 128) + UInt256.ofNat 4) (⟨32⟩ : UInt256))
      (probeCalldataMem solcFreePtrMem (UInt256.ofNat 128) i) = UInt256.ofNat 128 := by
  refine mloadFreePtrValue ?_ ?_ (probeCalldataMem_initial_read64 i)
  · unfold probeCalldataMem probeSelectorMem
    rw [show (UInt256.ofNat 128).toNat = 128 from by decide]
    have hsizeSel := toByteArray_write_size_ge_off_add32_no_gap probeSelectorShifted solcFreePtrMem 128
    have hfp4 : ((UInt256.ofNat 128) + UInt256.ofNat 4).toNat = 132 := by decide
    rw [hfp4]
    have hsizeArg := toByteArray_write_size_ge_off_add32_no_gap i
      (probeSelectorShifted.toByteArray.write 0 solcFreePtrMem 128 32) 132
    omega
  · decide

structure RunCarry (I : ExecutionEnv) where
  idx : UInt256
  last : UInt256
  scratch : UInt256
  fp : UInt256
  mem : ByteArray
  aw : UInt256
  rdata : ByteArray
  createdAccounts : Batteries.RBSet AccountAddress compare
  accountMap : AccountMap
  freePtrMemSize : 96 ≤ mem.size
  freePtrRead : mem.readWithPadding 64 32 = fp.toByteArray
  freePtrActive : ¬ (UInt256.ofNat 64) ≥ aw * ⟨32⟩
  freePtr : memLoad (UInt256.ofNat 64) aw mem = fp
  fpMin : 96 ≤ fp.toNat
  fpWindow : fp.toNat + 36 + 31 < UInt256.size
  fpBound : fp.toNat ≤ 128 + idx.toNat * 2 ^ 139
  awMulBound : aw.toNat * 32 < UInt256.size
  fpAdd4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4
  returnSub : UInt256.sub (fp + UInt256.ofNat 32) fp = UInt256.ofNat 32

def initialRunCarry (I : ExecutionEnv)
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap) : RunCarry I where
  idx := ⟨0⟩
  last := ⟨0⟩
  scratch := ⟨0⟩
  fp := UInt256.ofNat 128
  mem := solcFreePtrMem
  aw := UInt256.ofNat 3
  rdata := ByteArray.empty
  createdAccounts := cA
  accountMap := σ
  freePtrMemSize := by rw [solcFreePtrMem_size]
  freePtrRead := solcFreePtrMem_read64
  freePtrActive := by decide
  freePtr := solcFreePtrMem_mload64
  fpMin := by decide
  fpWindow := by decide
  fpBound := by
    change 128 ≤ 128
    rfl
  awMulBound := by decide
  fpAdd4 := by decide
  returnSub := by
    exact usub_uadd_word_ofNat_cancel (UInt256.ofNat 128) (by decide)

abbrev RunCarry.acc {I : ExecutionEnv} (a : RunCarry I) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (a.createdAccounts, a.accountMap)

abbrev RunCarry.callMem {I : ExecutionEnv} (a : RunCarry I) : ByteArray :=
  probeCalldataMem a.mem a.fp a.idx

abbrev RunCarry.probeAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
    (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256)

abbrev RunCarry.callCursorAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  M a.probeAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev RunCarry.returnAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256)

abbrev RunCarry.callOutputAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (MachineState.M a.callCursorAw.toNat a.fp.toNat
        (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat)
      a.fp.toNat (UInt256.ofNat 32).toNat)

abbrev RunCarry.callReturnMem {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    ByteArray :=
  o.write 0 a.callMem a.fp.toNat (callOutLen o)

abbrev RunCarry.postFreePtr {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    UInt256 :=
  a.fp + retAligned o

abbrev RunCarry.postFreePtrMem {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    ByteArray :=
  (a.postFreePtr o).toByteArray.write 0 (a.callReturnMem o) (UInt256.ofNat 64).toNat 32

abbrev RunCarry.postReadAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  M (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
    (⟨32⟩ : UInt256)

abbrev RunCarry.postAw {I : ExecutionEnv} (a : RunCarry I) : UInt256 :=
  M a.postReadAw a.fp (⟨32⟩ : UInt256)

theorem RunCarry.aw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.aw.toNat := by
  by_contra hnot
  have hle : a.aw.toNat ≤ 2 := by omega
  have hprod : (a.aw * (⟨32⟩ : UInt256)).toNat = a.aw.toNat * 32 := by
    exact umul_toNat a.aw (⟨32⟩ : UInt256)
      (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using a.awMulBound)
  have hactive : (UInt256.ofNat 64) ≥ a.aw * (⟨32⟩ : UInt256) := by
    change (a.aw * (⟨32⟩ : UInt256)).toNat ≤ (UInt256.ofNat 64).toNat
    rw [hprod]
    change a.aw.toNat * 32 ≤ 64
    omega
  exact a.freePtrActive hactive

theorem RunCarry.fpWindow32 {I : ExecutionEnv} (a : RunCarry I) :
    a.fp.toNat + 32 + 31 < UInt256.size := by
  have h := a.fpWindow
  omega

theorem RunCarry.fpAdd4Window32 {I : ExecutionEnv} (a : RunCarry I) :
    (a.fp + UInt256.ofNat 4).toNat + 32 + 31 < UInt256.size := by
  rw [a.fpAdd4]
  have h := a.fpWindow
  omega

theorem RunCarry.probeAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.probeAw.toNat * 32 < UInt256.size := by
  have h1 := M_mul32_lt a.aw (UInt256.ofNat 64) a.awMulBound (by decide)
  have h2 := M_mul32_lt (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp h1
    a.fpWindow32
  have h3 := M_mul32_lt
    (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
    (a.fp + UInt256.ofNat 4) h2
    a.fpAdd4Window32
  simpa [RunCarry.probeAw] using h3

theorem RunCarry.probeAw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.probeAw.toNat := by
  have h0 := a.aw_toNat_ge3
  have h1mul := M_mul32_lt a.aw (UInt256.ofNat 64) a.awMulBound (by decide)
  have h1 := M_toNat_ge a.aw (UInt256.ofNat 64) h0 a.awMulBound (by decide)
  have h2mul := M_mul32_lt (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp h1mul
    a.fpWindow32
  have h2 := M_toNat_ge (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp h1 h1mul
    a.fpWindow32
  have h3 := M_toNat_ge
    (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
    (a.fp + UInt256.ofNat 4) h2 h2mul
    a.fpAdd4Window32
  simpa [RunCarry.probeAw] using h3

theorem RunCarry.probeAw_active64 {I : ExecutionEnv} (a : RunCarry I) :
    ¬ (UInt256.ofNat 64) ≥ a.probeAw * (⟨32⟩ : UInt256) :=
  active64_of_aw_toNat_ge3 a.probeAw_toNat_ge3 a.probeAw_mul32_lt

theorem RunCarry.callFreePtr_value {I : ExecutionEnv} (a : RunCarry I) (i : UInt256) :
    memLoad (UInt256.ofNat 64) a.probeAw (probeCalldataMem a.mem a.fp i) = a.fp := by
  exact mloadWordValue_of_readWithPadding
    (off := UInt256.ofNat 64) (aw := a.probeAw) (v := a.fp)
    (by
      have hsz := probeCalldataMem_size_ge_fp36 (mem := a.mem) (fp := a.fp) (i := i)
        a.fpAdd4
      change 64 < (probeCalldataMem a.mem a.fp i).size
      have hmin := a.fpMin
      omega)
    a.probeAw_active64
    (by
      simpa [show (UInt256.ofNat 64).toNat = 64 from by decide] using
        probeCalldataMem_read64 (mem := a.mem) (fp := a.fp) (i := i)
          a.freePtrRead a.freePtrMemSize a.fpMin a.fpAdd4)

theorem RunCarry.callCursorAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.callCursorAw.toNat * 32 < UInt256.size := by
  simpa [RunCarry.callCursorAw] using
    M_mul32_lt a.probeAw (UInt256.ofNat 64) a.probeAw_mul32_lt (by decide)

theorem RunCarry.callCursorAw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.callCursorAw.toNat := by
  simpa [RunCarry.callCursorAw] using
    M_toNat_ge a.probeAw (UInt256.ofNat 64) a.probeAw_toNat_ge3 a.probeAw_mul32_lt
      (by decide)

theorem RunCarry.returnAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.returnAw.toNat * 32 < UInt256.size := by
  have h1 := M_mul32_lt a.aw (UInt256.ofNat 64) a.awMulBound (by decide)
  have h2 := M_mul32_lt (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp h1
    a.fpWindow32
  simpa [RunCarry.returnAw] using h2

theorem RunCarry.returnAw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.returnAw.toNat := by
  have h0 := a.aw_toNat_ge3
  have h1mul := M_mul32_lt a.aw (UInt256.ofNat 64) a.awMulBound (by decide)
  have h1 := M_toNat_ge a.aw (UInt256.ofNat 64) h0 a.awMulBound (by decide)
  have h2 := M_toNat_ge (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp h1 h1mul
    a.fpWindow32
  simpa [RunCarry.returnAw] using h2

theorem RunCarry.returnAw_active64 {I : ExecutionEnv} (a : RunCarry I) :
    ¬ (UInt256.ofNat 64) ≥ a.returnAw * (⟨32⟩ : UInt256) :=
  active64_of_aw_toNat_ge3 a.returnAw_toNat_ge3 a.returnAw_mul32_lt

theorem RunCarry.returnRead_value {I : ExecutionEnv} (a : RunCarry I) (last : UInt256) :
    (last.toByteArray.write 0 a.mem a.fp.toNat 32).readWithPadding a.fp.toNat 32 =
      UInt256.toByteArray last := by
  exact toByteArray_write_read_back_no_gap last a.mem a.fp.toNat

theorem RunCarry.returnFreePtr_value {I : ExecutionEnv} (a : RunCarry I) (last : UInt256) :
    memLoad (UInt256.ofNat 64) a.returnAw
      (last.toByteArray.write 0 a.mem a.fp.toNat 32) = a.fp := by
  exact mloadWordValue_of_readWithPadding
    (off := UInt256.ofNat 64) (aw := a.returnAw) (v := a.fp)
    (by
      have hsize := toByteArray_write_size_ge_off_add32_no_gap last a.mem a.fp.toNat
      change 64 < (last.toByteArray.write 0 a.mem a.fp.toNat 32).size
      have hmin := a.fpMin
      omega)
    a.returnAw_active64
    (by
      rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
      rw [toByteArray_write_read_below_no_gap last a.mem a.fp.toNat 64
        (by
          have hmem := a.freePtrMemSize
          omega)
        (by
          have hmin := a.fpMin
          omega)]
      exact a.freePtrRead)

theorem RunCarry.callOutputAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.callOutputAw.toNat * 32 < UInt256.size := by
  unfold RunCarry.callOutputAw
  rw [fp_callInputSize_eq a.fp]
  change (UInt256.ofNat
    (MachineState.M
      (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
      a.fp.toNat 32)).toNat * 32 < UInt256.size
  have hinner :
      MachineState.M a.callCursorAw.toNat a.fp.toNat 36 * 32 < UInt256.size := by
    exact MachineState_M_mul32_lt_of_bounds
      a.callCursorAw_mul32_lt a.fpWindow
  exact UInt256_ofNat_M_len_mul32_lt
    (MachineState.M a.callCursorAw.toNat a.fp.toNat 36) a.fp.toNat 32 hinner
    a.fpWindow32

theorem RunCarry.callOutputAw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.callOutputAw.toNat := by
  unfold RunCarry.callOutputAw
  rw [fp_callInputSize_eq a.fp]
  change 3 ≤ (UInt256.ofNat
    (MachineState.M
      (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
      a.fp.toNat 32)).toNat
  have hinnerGeNat :
      3 ≤ MachineState.M a.callCursorAw.toNat a.fp.toNat 36 := by
    exact le_trans a.callCursorAw_toNat_ge3 (MachineState_M_ge_left _ _ _)
  have hinnerMul :
      MachineState.M a.callCursorAw.toNat a.fp.toNat 36 * 32 < UInt256.size := by
    exact MachineState_M_mul32_lt_of_bounds
      a.callCursorAw_mul32_lt a.fpWindow
  exact UInt256_ofNat_M_len_toNat_ge hinnerGeNat hinnerMul a.fpWindow32

theorem RunCarry.callOutputAw_active64 {I : ExecutionEnv} (a : RunCarry I) :
    ¬ (UInt256.ofNat 64) ≥ a.callOutputAw * (⟨32⟩ : UInt256) :=
  active64_of_aw_toNat_ge3 a.callOutputAw_toNat_ge3 a.callOutputAw_mul32_lt

theorem RunCarry.callOutputAw_covers_fp {I : ExecutionEnv} (a : RunCarry I) :
    a.fp.toNat + 32 ≤ a.callOutputAw.toNat * 32 := by
  unfold RunCarry.callOutputAw
  rw [fp_callInputSize_eq a.fp]
  change a.fp.toNat + 32 ≤
    (UInt256.ofNat
      (MachineState.M (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
        a.fp.toNat 32)).toNat * 32
  have hinner :
      MachineState.M a.callCursorAw.toNat a.fp.toNat 36 * 32 < UInt256.size := by
    exact MachineState_M_mul32_lt_of_bounds a.callCursorAw_mul32_lt a.fpWindow
  have hcover :
      a.fp.toNat + 32 ≤
        MachineState.M (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
          a.fp.toNat 32 * 32 :=
    MachineState_M_covers_len (s := MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
      (f := a.fp.toNat) (l := 32) (by decide)
  have houter :
      MachineState.M (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
          a.fp.toNat 32 * 32 < UInt256.size :=
    MachineState_M_mul32_lt_of_bounds hinner a.fpWindow32
  have hlt :
      MachineState.M (MachineState.M a.callCursorAw.toNat a.fp.toNat 36)
          a.fp.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hlt]
  exact hcover

theorem RunCarry.postReadAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.postReadAw.toNat * 32 < UInt256.size := by
  have h1 := M_mul32_lt a.callOutputAw (UInt256.ofNat 64) a.callOutputAw_mul32_lt
    (by decide)
  have h2 := M_mul32_lt
    (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) h1
    (by decide)
  simpa [RunCarry.postReadAw] using h2

theorem RunCarry.postReadAw_covers_fp {I : ExecutionEnv} (a : RunCarry I) :
    a.fp.toNat + 32 ≤ a.postReadAw.toNat * 32 := by
  have h1 := M_toNat_ge a.callOutputAw (UInt256.ofNat 64)
    (n := a.callOutputAw.toNat) le_rfl a.callOutputAw_mul32_lt (by decide)
  have h1mul := M_mul32_lt a.callOutputAw (UInt256.ofNat 64) a.callOutputAw_mul32_lt
    (by decide)
  have h2 := M_toNat_ge
    (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
    (n := a.callOutputAw.toNat) h1 h1mul (by decide)
  have hcover := a.callOutputAw_covers_fp
  have hmono : a.callOutputAw.toNat * 32 ≤ a.postReadAw.toNat * 32 := by
    simpa [RunCarry.postReadAw] using Nat.mul_le_mul_right 32 h2
  exact le_trans hcover hmono

theorem RunCarry.postReadAw_active_fp {I : ExecutionEnv} (a : RunCarry I) :
    ¬ a.fp ≥ a.postReadAw * (⟨32⟩ : UInt256) := by
  intro hge
  have hmul := a.postReadAw_mul32_lt
  have hprod : (a.postReadAw * (⟨32⟩ : UInt256)).toNat = a.postReadAw.toNat * 32 := by
    exact umul_toNat a.postReadAw (⟨32⟩ : UInt256)
      (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hmul)
  change (a.postReadAw * (⟨32⟩ : UInt256)).toNat ≤ a.fp.toNat at hge
  rw [hprod] at hge
  have hcover := a.postReadAw_covers_fp
  omega

theorem RunCarry.callMem_size_ge_fp36 {I : ExecutionEnv} (a : RunCarry I) :
    a.fp.toNat + 36 ≤ a.callMem.size := by
  exact probeCalldataMem_size_ge_fp36 (mem := a.mem) (fp := a.fp) (i := a.idx) a.fpAdd4

theorem RunCarry.callMem_size_gt64 {I : ExecutionEnv} (a : RunCarry I) :
    64 < a.callMem.size := by
  have hsz := a.callMem_size_ge_fp36
  have hmin := a.fpMin
  omega

theorem RunCarry.callReturnMem_size_gt64 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray)
    (hhi : o.size < UInt256.size) :
    64 < (a.callReturnMem o).size := by
  by_cases hzero : callOutLen o = 0
  · unfold RunCarry.callReturnMem
    rw [hzero, byteArray_write_len_zero]
    exact a.callMem_size_gt64
  · have hbase : a.callMem.size ≤ (a.callReturnMem o).size := by
      unfold RunCarry.callReturnMem
      exact write_size_ge_base_extend o a.callMem a.fp.toNat (callOutLen o) hzero
        (callOutLen_le_size o hhi)
        (by
          have hsz := a.callMem_size_ge_fp36
          omega)
    exact lt_of_lt_of_le a.callMem_size_gt64 hbase

theorem RunCarry.callReturnMem_read64 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray)
    (hhi : o.size < UInt256.size) :
    (a.callReturnMem o).readWithPadding 64 32 = a.fp.toByteArray := by
  by_cases hzero : callOutLen o = 0
  · unfold RunCarry.callReturnMem
    rw [hzero, byteArray_write_len_zero]
    exact probeCalldataMem_read64 (mem := a.mem) (fp := a.fp) (i := a.idx)
      a.freePtrRead a.freePtrMemSize a.fpMin a.fpAdd4
  · unfold RunCarry.callReturnMem
    rw [write_read_below_gen_extend o a.callMem a.fp.toNat (callOutLen o) 64 hzero
      (callOutLen_le_size o hhi)
      (by
        have hsz := a.callMem_size_ge_fp36
        omega)
      (by
        have hmin := a.fpMin
        omega)]
    exact probeCalldataMem_read64 (mem := a.mem) (fp := a.fp) (i := a.idx)
      a.freePtrRead a.freePtrMemSize a.fpMin a.fpAdd4

theorem RunCarry.callReturnMem_mload64 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray)
    (hhi : o.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) a.callOutputAw (a.callReturnMem o) = a.fp := by
  exact mloadWordValue_of_readWithPadding
    (off := UInt256.ofNat 64) (aw := a.callOutputAw) (v := a.fp)
    (by
      rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
      exact a.callReturnMem_size_gt64 o hhi)
    a.callOutputAw_active64
    (by
      simpa [show (UInt256.ofNat 64).toNat = 64 from by decide] using
        a.callReturnMem_read64 o hhi)

theorem RunCarry.callReturnMem_read_fp_extract {I : ExecutionEnv} (a : RunCarry I)
    (o : ByteArray) (ho32 : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (a.callReturnMem o).readWithPadding a.fp.toNat 32 = o.extract 0 32 := by
  unfold RunCarry.callReturnMem
  rw [callOutLen_eq32 o ho32 hhi]
  exact write32_read_back o a.callMem a.fp.toNat ho32
    (by
      have hsz := a.callMem_size_ge_fp36
      omega)

theorem RunCarry.callReturnMem_read_fp_word {I : ExecutionEnv} (a : RunCarry I)
    (o : ByteArray) (ho32 : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (a.callReturnMem o).readWithPadding a.fp.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) := by
  rw [a.callReturnMem_read_fp_extract o ho32 hhi]
  have hw := readWithPadding_eq_toByteArray_ofNat o 0 (by simpa using ho32)
  rw [readWithPadding_eq_extract o 0 (by simpa using ho32)] at hw
  simpa using hw

theorem RunCarry.postFreePtrMem_read64 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    (a.postFreePtrMem o).readWithPadding 64 32 =
      UInt256.toByteArray (a.postFreePtr o) := by
  unfold RunCarry.postFreePtrMem
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
  exact toByteArray_write_read_back_no_gap (a.postFreePtr o) (a.callReturnMem o) 64

theorem RunCarry.postFreePtrMem_size_ge96 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    96 ≤ (a.postFreePtrMem o).size := by
  unfold RunCarry.postFreePtrMem
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
  exact toByteArray_write_size_ge_off_add32_no_gap (a.postFreePtr o) (a.callReturnMem o) 64

theorem RunCarry.postFreePtrMem_read_old_fp {I : ExecutionEnv} (a : RunCarry I)
    (o : ByteArray) (ho32 : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (a.postFreePtrMem o).readWithPadding a.fp.toNat 32 =
      (a.callReturnMem o).readWithPadding a.fp.toNat 32 := by
  unfold RunCarry.postFreePtrMem
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
  exact write32_read_above (UInt256.toByteArray (a.postFreePtr o)) (a.callReturnMem o) 64
    a.fp.toNat (by rw [toByteArray_size])
    (by
      have hsz := a.callReturnMem_size_gt64 o hhi
      omega)
    (by
      have hmin := a.fpMin
      omega)
    (by
      unfold RunCarry.callReturnMem
      rw [callOutLen_eq32 o ho32 hhi]
      have hbase := a.callMem_size_ge_fp36
      have hsz := write_size_ge_base_extend o a.callMem a.fp.toNat 32
        (by decide) (by exact ho32) (by omega)
      have hread : a.fp.toNat + 32 ≤ (o.write 0 a.callMem a.fp.toNat 32).size := by
        by_cases hin : a.fp.toNat + 32 ≤ a.callMem.size
        · have hb := hsz
          omega
        · have hext := write_size_ge_base_extend o a.callMem a.fp.toNat 32
            (by decide) (by exact ho32) (by omega)
          have hwrite := toByteArray_write_size_ge_off_add32_no_gap a.fp a.callMem a.fp.toNat
          omega
      exact hread)

theorem RunCarry.postAw_mul32_lt {I : ExecutionEnv} (a : RunCarry I) :
    a.postAw.toNat * 32 < UInt256.size := by
  have h1 := M_mul32_lt a.callOutputAw (UInt256.ofNat 64) a.callOutputAw_mul32_lt
    (by decide)
  have h2 := M_mul32_lt
    (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) h1
    (by decide)
  have h3 := M_mul32_lt
    (M (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
      (⟨32⟩ : UInt256))
    a.fp h2 a.fpWindow32
  simpa [RunCarry.postAw] using h3

theorem RunCarry.postAw_toNat_ge3 {I : ExecutionEnv} (a : RunCarry I) :
    3 ≤ a.postAw.toNat := by
  have h1mul := M_mul32_lt a.callOutputAw (UInt256.ofNat 64) a.callOutputAw_mul32_lt
    (by decide)
  have h1 := M_toNat_ge a.callOutputAw (UInt256.ofNat 64) a.callOutputAw_toNat_ge3
    a.callOutputAw_mul32_lt (by decide)
  have h2mul := M_mul32_lt
    (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) h1mul
    (by decide)
  have h2 := M_toNat_ge
    (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) h1 h1mul
    (by decide)
  have h3 := M_toNat_ge
    (M (M a.callOutputAw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
      (⟨32⟩ : UInt256))
    a.fp h2 h2mul a.fpWindow32
  simpa [RunCarry.postAw] using h3

theorem RunCarry.postAw_active64 {I : ExecutionEnv} (a : RunCarry I) :
    ¬ (UInt256.ofNat 64) ≥ a.postAw * (⟨32⟩ : UInt256) :=
  active64_of_aw_toNat_ge3 a.postAw_toNat_ge3 a.postAw_mul32_lt

theorem RunCarry.postFreePtrMem_mload64 {I : ExecutionEnv} (a : RunCarry I) (o : ByteArray) :
    memLoad (UInt256.ofNat 64) a.postAw (a.postFreePtrMem o) = a.postFreePtr o := by
  exact mloadWordValue_of_readWithPadding
    (off := UInt256.ofNat 64) (aw := a.postAw) (v := a.postFreePtr o)
    (by
      rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
      have hsz := a.postFreePtrMem_size_ge96 o
      omega)
    a.postAw_active64
    (by
      simpa [show (UInt256.ofNat 64).toNat = 64 from by decide] using
        a.postFreePtrMem_read64 o)

theorem RunCarry.postFreePtrMem_mload_old_fp {I : ExecutionEnv} (a : RunCarry I)
    (o : ByteArray) (ho32 : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    memLoad a.fp a.postReadAw (a.postFreePtrMem o) =
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  exact mloadWordValue_of_readWithPadding
    (off := a.fp) (aw := a.postReadAw)
    (v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
    (by
      have hread : a.fp.toNat + 32 ≤ (a.postFreePtrMem o).size := by
        unfold RunCarry.postFreePtrMem
        rw [show (UInt256.ofNat 64).toNat = 64 from by decide]
        have hbase : a.fp.toNat + 32 ≤ (a.callReturnMem o).size := by
          unfold RunCarry.callReturnMem
          rw [callOutLen_eq32 o ho32 hhi]
          have hszw := write_size_ge_base_extend o a.callMem a.fp.toNat 32
            (by decide) (by exact ho32)
            (by
              have hc := a.callMem_size_ge_fp36
              omega)
          have hc := a.callMem_size_ge_fp36
          omega
        have hwr : (a.callReturnMem o).size ≤
            ((a.postFreePtr o).toByteArray.write 0 (a.callReturnMem o) 64 32).size := by
          exact write_size_ge_base_extend (UInt256.toByteArray (a.postFreePtr o))
            (a.callReturnMem o) 64 32
            (by decide) (by rw [toByteArray_size])
            (by
              have hgt := a.callReturnMem_size_gt64 o hhi
              omega)
        omega
      omega)
    a.postReadAw_active_fp
    (by
      rw [a.postFreePtrMem_read_old_fp o ho32 hhi]
      exact a.callReturnMem_read_fp_word o ho32 hhi)

def RunCarry.postCallNext {I : ExecutionEnv} (a : RunCarry I)
    (idx last : UInt256) (o : ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare) (accountMap : AccountMap)
    (hmin : 96 ≤ (a.postFreePtr o).toNat)
    (hwindow : (a.postFreePtr o).toNat + 36 + 31 < UInt256.size)
    (hbound : (a.postFreePtr o).toNat ≤ 128 + idx.toNat * 2 ^ 139) :
    RunCarry I where
  idx := idx
  last := last
  scratch := a.scratch
  fp := a.postFreePtr o
  mem := a.postFreePtrMem o
  aw := a.postAw
  rdata := o
  createdAccounts := createdAccounts
  accountMap := accountMap
  freePtrMemSize := a.postFreePtrMem_size_ge96 o
  freePtrRead := a.postFreePtrMem_read64 o
  freePtrActive := a.postAw_active64
  freePtr := a.postFreePtrMem_mload64 o
  fpMin := hmin
  fpWindow := hwindow
  fpBound := hbound
  awMulBound := a.postAw_mul32_lt
  fpAdd4 := fp_add4_toNat (by
    have h := hwindow
    omega)
  returnSub := usub_uadd_word_ofNat_cancel (a.postFreePtr o) (by decide)

abbrev RunCarry.stack {I : ExecutionEnv} (a : RunCarry I)
    (count target sel : UInt256) : List UInt256 :=
  [a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]

abbrev RunCarry.exitStack {I : ExecutionEnv} (a : RunCarry I) (sel : UInt256) :
    List UInt256 :=
  [a.last, sel]

theorem initialRunCarry_shape {I : ExecutionEnv}
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap) :
    (initialRunCarry I cA σ).stack (runCountWord I) (runTargetWord I) (nestedCallerSelWord I) =
      [⟨0⟩, ⟨0⟩, ⟨0⟩, runCountWord I, runTargetWord I, ⟨71⟩, nestedCallerSelWord I] := by
  rfl

theorem initialRunCarry_acc {I : ExecutionEnv}
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap) :
    (initialRunCarry I cA σ).acc = (cA, σ) := by
  rfl

theorem runArgStore_target (I : ExecutionEnv) :
    (runArgStore I).get? "target" = some (runTargetValue I) := by
  rw [runArgStore, store_get_ne _ _ (by decide), store_get_self]

theorem runArgStore_count (I : ExecutionEnv) :
    (runArgStore I).get? "count" = some (runCountValue I) := by
  rw [runArgStore, store_get_self]

theorem runArgStore_last_none (I : ExecutionEnv) :
    (runArgStore I).get? "last" = none := by
  simp [runArgStore, runTargetValue, runCountValue]

abbrev runStoreWithLast (I : ExecutionEnv) : Store :=
  (runArgStore I).insert "last" (.int 0)

abbrev runLoopStore (I : ExecutionEnv) (i last : UInt256) : Store :=
  (((∅ : Store).insert "target" (runTargetValue I)).insert "count" (runCountValue I))
    |>.insert "last" (.int (Int.ofNat last.toNat))
    |>.insert "i" (.int (Int.ofNat i.toNat))

abbrev sampleStore (I : ExecutionEnv) (i : UInt256) : Store :=
  ((∅ : Store).insert "i" (.int (Int.ofNat i.toNat))).insert "target" (runTargetValue I)

abbrev sampleGasStore (I : ExecutionEnv) (i gasWord : UInt256) : Store :=
  (sampleStore I i).insert "remaining" (.int (Int.ofNat gasWord.toNat))

theorem runStoreWithLast_target (I : ExecutionEnv) :
    (runStoreWithLast I).get? "target" = some (runTargetValue I) := by
  rw [runStoreWithLast, store_get_ne _ _ (by decide), runArgStore_target]

theorem runStoreWithLast_count (I : ExecutionEnv) :
    (runStoreWithLast I).get? "count" = some (runCountValue I) := by
  rw [runStoreWithLast, store_get_ne _ _ (by decide), runArgStore_count]

theorem runStoreWithLast_last (I : ExecutionEnv) :
    (runStoreWithLast I).get? "last" = some (.int 0) := by
  rw [runStoreWithLast, store_get_self]

theorem runLoopStore_target (I : ExecutionEnv) (i last : UInt256) :
    (runLoopStore I i last).get? "target" = some (runTargetValue I) := by
  rw [runLoopStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem runLoopStore_count (I : ExecutionEnv) (i last : UInt256) :
    (runLoopStore I i last).get? "count" = some (runCountValue I) := by
  rw [runLoopStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem runLoopStore_last (I : ExecutionEnv) (i last : UInt256) :
    (runLoopStore I i last).get? "last" = some (.int (Int.ofNat last.toNat)) := by
  rw [runLoopStore, store_get_ne _ _ (by decide), store_get_self]

theorem runLoopStore_i (I : ExecutionEnv) (i last : UInt256) :
    (runLoopStore I i last).get? "i" = some (.int (Int.ofNat i.toNat)) := by
  rw [runLoopStore, store_get_self]

theorem sampleStore_target (I : ExecutionEnv) (i : UInt256) :
    (sampleStore I i).get? "target" = some (runTargetValue I) := by
  rw [sampleStore, store_get_self]

theorem sampleStore_i (I : ExecutionEnv) (i : UInt256) :
    (sampleStore I i).get? "i" = some (.int (Int.ofNat i.toNat)) := by
  rw [sampleStore, store_get_ne _ _ (by decide), store_get_self]

theorem sampleGasStore_remaining (I : ExecutionEnv) (i gasWord : UInt256) :
    (sampleGasStore I i gasWord).get? "remaining" =
      some (.int (Int.ofNat gasWord.toNat)) := by
  rw [sampleGasStore, store_get_self]

theorem sampleGasStore_target (I : ExecutionEnv) (i gasWord : UInt256) :
    (sampleGasStore I i gasWord).get? "target" = some (runTargetValue I) := by
  rw [sampleGasStore, store_get_ne _ _ (by decide), sampleStore_target]

theorem sampleGasStore_i (I : ExecutionEnv) (i gasWord : UInt256) :
    (sampleGasStore I i gasWord).get? "i" = some (.int (Int.ofNat i.toNat)) := by
  rw [sampleGasStore, store_get_ne _ _ (by decide), sampleStore_i]

theorem evalSampleProbeReceiver (evm : EVM.State) (I : ExecutionEnv) (i gasWord : UInt256) :
    evalExpr? nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleGasStore I i gasWord } evm
      (.var "target") = .ok (runTargetValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, sampleGasStore_target]

theorem evalSampleProbeArgs (evm : EVM.State) (I : ExecutionEnv) (i gasWord : UInt256) :
    evalExprs? nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleGasStore I i gasWord } evm
      [.var "i"] = .ok [.int (Int.ofNat i.toNat)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, sampleGasStore_i, EvalResult.bind,
    bind, pure]

theorem runLoopStore_init (I : ExecutionEnv) :
    (runStoreWithLast I).insert "i" (.int 0) = runLoopStore I ⟨0⟩ ⟨0⟩ := by
  simp [runStoreWithLast, runArgStore, runLoopStore, runTargetValue, runCountValue]

def runCarryInv (I : ExecutionEnv) (base : EVM.State) (count : UInt256)
    (v : ℕ) (a : RunCarry I) (L : Store) (evm : EVM.State) : Prop :=
  L.get? "target" = some (runTargetValue I) ∧
  L.get? "count" = some (.int (Int.ofNat count.toNat)) ∧
  L.get? "i" = some (.int (Int.ofNat a.idx.toNat)) ∧
  L.get? "last" = some (.int (Int.ofNat a.last.toNat)) ∧
  count = runCountWord I ∧
  a.idx.toNat + v = count.toNat ∧
  a.idx.toNat ≤ count.toNat ∧
  evm.executionEnv = I ∧
  evm.σ₀ = base.σ₀ ∧
  evm.genesisBlockHeader = base.genesisBlockHeader ∧
  evm.blocks = base.blocks ∧
  a.createdAccounts = evm.createdAccounts ∧
  accountMapEquiv a.accountMap evm.accountMap

def runCarryDone (I : ExecutionEnv) (count : UInt256)
    (a : RunCarry I) (L : Store) (evm : EVM.State) : Prop :=
  L.get? "last" = some (.int (Int.ofNat a.last.toNat)) ∧
  count.toNat ≤ a.idx.toNat ∧
  evm.executionEnv = I ∧
  a.createdAccounts = evm.createdAccounts ∧
  accountMapEquiv a.accountMap evm.accountMap

theorem runCarryInv_shape {I : ExecutionEnv} {base : EVM.State} {count : UInt256}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State}
    (h : runCarryInv I base count v a L evm) :
    L.get? "target" = some (runTargetValue I) ∧
    L.get? "count" = some (.int (Int.ofNat count.toNat)) ∧
    L.get? "i" = some (.int (Int.ofNat a.idx.toNat)) ∧
    L.get? "last" = some (.int (Int.ofNat a.last.toNat)) ∧
    count = runCountWord I ∧
    a.idx.toNat + v = count.toNat ∧
    a.idx.toNat ≤ count.toNat := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1⟩

theorem runCarryDone_of_inv_zero {I : ExecutionEnv} {base : EVM.State} {count : UInt256}
    {a : RunCarry I} {L : Store} {evm : EVM.State}
    (h : runCarryInv I base count 0 a L evm) :
    runCarryDone I count a L evm := by
  rcases h with
    ⟨_htarget, _hcount, _hi, hlast, _hcountEq, hvariant, _hle, henv, _hσ₀, _hgh, _hbl,
      hcreated, haccounts⟩
  exact ⟨hlast, by omega, henv, hcreated, haccounts⟩

theorem runCarryDone_exit {I : ExecutionEnv} {count : UInt256}
    {a : RunCarry I} {L : Store} {evm : EVM.State}
    (h : runCarryDone I count a L evm) :
    count.toNat ≤ a.idx.toNat := h.2.1

theorem RunCarry.nextIdx_toNat_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    (hInv : runCarryInv I base count (v + 1) a L evm) :
    (UInt256.ofNat 1 + a.idx).toNat = a.idx.toNat + 1 := by
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, hcountEq, hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  rw [uadd_toNat]
  change (1 + a.idx.toNat) % UInt256.size = a.idx.toNat + 1
  rw [Nat.mod_eq_of_lt (by
    rw [hcountEq] at hvariant
    have hcountSmall : (runCountWord I).toNat < UInt256.size := (runCountWord I).val.isLt
    omega)]
  omega

theorem RunCarry.postFreePtr_toNat_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    (a.postFreePtr o).toNat = a.fp.toNat + (retAligned o).toNat := by
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, _hcountEq, hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hidx : a.idx.toNat + 1 ≤ 16 := by omega
  have hret := retAligned_toNat_lt_2pow139 o ho138
  have hbound := a.fpBound
  have hcap : 128 + 16 * 2 ^ 139 < UInt256.size := by norm_num [UInt256.size]
  have hsum : a.fp.toNat + (retAligned o).toNat < UInt256.size := by omega
  unfold RunCarry.postFreePtr
  exact uadd_toNat_of_lt hsum

theorem RunCarry.postFreePtr_min_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    96 ≤ (a.postFreePtr o).toNat := by
  rw [a.postFreePtr_toNat_of_inv hInv hcountLe ho138]
  exact le_trans a.fpMin (Nat.le_add_right _ _)

theorem RunCarry.postFreePtr_window_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    (a.postFreePtr o).toNat + 36 + 31 < UInt256.size := by
  have hInvAll := hInv
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, _hcountEq, hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  rw [a.postFreePtr_toNat_of_inv hInvAll hcountLe ho138]
  have hidx : a.idx.toNat + 1 ≤ 16 := by omega
  have hret := retAligned_toNat_lt_2pow139 o ho138
  have hbound := a.fpBound
  have hcap : 128 + 16 * 2 ^ 139 + 67 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem RunCarry.postFreePtr_bound_next_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    (a.postFreePtr o).toNat ≤ 128 + (UInt256.ofNat 1 + a.idx).toNat * 2 ^ 139 := by
  rw [a.postFreePtr_toNat_of_inv hInv hcountLe ho138, a.nextIdx_toNat_of_inv hInv]
  have hret := retAligned_toNat_lt_2pow139 o ho138
  have hbound := a.fpBound
  omega

theorem RunCarry.postFreePtr_bound_count_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    (a.postFreePtr o).toNat ≤ 128 + count.toNat * 2 ^ 139 := by
  have hInvAll := hInv
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, _hcountEq, hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  rw [a.postFreePtr_toNat_of_inv hInvAll hcountLe ho138]
  have hret := retAligned_toNat_lt_2pow139 o ho138
  have hbound := a.fpBound
  omega

theorem RunCarry.fp_add_return_size_lt_of_inv {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138) :
    a.fp.toNat + o.size < UInt256.size := by
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, _hcountEq, hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hidx : a.idx.toNat + 1 ≤ 16 := by omega
  have hbound := a.fpBound
  have hcap : 128 + 16 * 2 ^ 139 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem runCarryInv_postCallZeroNext {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {σ'_solm : AccountMap} {A'_solm : Substate}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138)
    (hacc : accountMapEquiv σ' σ'_solm) :
    runCarryInv I base count v
      (a.postCallNext (UInt256.ofNat 1 + a.idx) a.last o cA' σ'
        (a.postFreePtr_min_of_inv hInv hcountLe ho138)
        (a.postFreePtr_window_of_inv hInv hcountLe ho138)
        (a.postFreePtr_bound_next_of_inv hInv hcountLe ho138))
      ((L.insert "value" (.int 0)).insert "i"
        (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))))
      { evm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  have hnext := a.nextIdx_toNat_of_inv hInv
  rcases hInv with
    ⟨htarget, hcount, _hi, hlast, hcountEq, hvariant, _hle, henv, hσ₀, hgh, hbl, _hcreated,
      _haccounts⟩
  refine ⟨?_, ?_, ?_, ?_, hcountEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), htarget]
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hcount]
  · rw [store_get_self]
    rfl
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
    change L.get? "last" = some (.int (Int.ofNat a.last.toNat))
    exact hlast
  · change (UInt256.ofNat 1 + a.idx).toNat + v = count.toNat
    rw [hnext]
    omega
  · change (UInt256.ofNat 1 + a.idx).toNat ≤ count.toNat
    rw [hnext]
    omega
  · rw [henv]
  · exact hσ₀
  · exact hgh
  · exact hbl
  · rfl
  · exact hacc

theorem runCarryInv_postCallOtherNext {I : ExecutionEnv} {base : EVM.State}
    {count value : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {σ'_solm : AccountMap} {A'_solm : Substate}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138)
    (hacc : accountMapEquiv σ' σ'_solm) :
    runCarryInv I base count v
      (a.postCallNext (UInt256.ofNat 1 + a.idx) value o cA' σ'
        (a.postFreePtr_min_of_inv hInv hcountLe ho138)
        (a.postFreePtr_window_of_inv hInv hcountLe ho138)
        (a.postFreePtr_bound_next_of_inv hInv hcountLe ho138))
      (((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
          (.int (Int.ofNat value.toNat))).insert "i"
        (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))))
      { evm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  have hnext := a.nextIdx_toNat_of_inv hInv
  rcases hInv with
    ⟨htarget, hcount, _hi, _hlast, hcountEq, hvariant, _hle, henv, hσ₀, hgh, hbl, _hcreated,
      _haccounts⟩
  refine ⟨?_, ?_, ?_, ?_, hcountEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), htarget]
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hcount]
  · rw [store_get_self]
    rfl
  · rw [store_get_ne _ _ (by decide), store_get_self]
    rfl
  · change (UInt256.ofNat 1 + a.idx).toNat + v = count.toNat
    rw [hnext]
    omega
  · change (UInt256.ofNat 1 + a.idx).toNat ≤ count.toNat
    rw [hnext]
    omega
  · rw [henv]
  · exact hσ₀
  · exact hgh
  · exact hbl
  · rfl
  · exact hacc

theorem runCarryDone_postCallBreak {I : ExecutionEnv} {base : EVM.State}
    {count : UInt256} {v : Nat} {a : RunCarry I} {L : Store} {evm : EVM.State}
    {o : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {σ'_solm : AccountMap} {A'_solm : Substate}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hcountLe : count.toNat ≤ 16) (ho138 : o.size < 2 ^ 138)
    (hacc : accountMapEquiv σ' σ'_solm) :
    runCarryDone I count
      (a.postCallNext count a.last o cA' σ'
        (a.postFreePtr_min_of_inv hInv hcountLe ho138)
        (a.postFreePtr_window_of_inv hInv hcountLe ho138)
        (a.postFreePtr_bound_count_of_inv hInv hcountLe ho138))
      (L.insert "value" (.int 1))
      { evm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' } := by
  rcases hInv with
    ⟨_htarget, _hcount, _hi, hlast, _hcountEq, _hvariant, _hle, henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (by decide)]
    change L.get? "last" = some (.int (Int.ofNat a.last.toNat))
    exact hlast
  · rfl
  · rw [henv]
  · rfl
  · exact hacc

theorem initialRunCarry_inv {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runCarryInv I (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (runCountWord I) (runCountWord I).toNat
      (initialRunCarry I cA σ_evm) (runLoopStore I ⟨0⟩ ⟨0⟩)
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) := by
  refine ⟨runLoopStore_target I ⟨0⟩ ⟨0⟩, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simpa [runCountValue] using runLoopStore_count I ⟨0⟩ ⟨0⟩
  · exact runLoopStore_i I ⟨0⟩ ⟨0⟩
  · simpa using runLoopStore_last I ⟨0⟩ ⟨0⟩
  · change (⟨0⟩ : UInt256).toNat + (runCountWord I).toNat = (runCountWord I).toNat
    simp
  · exact Nat.zero_le _
  · rfl
  · rfl
  · rfl
  · rfl
  · change cA = cA
    rfl
  · simpa [initState] using hAccounts

def RunCarry.lowGasNext {I : ExecutionEnv} (a : RunCarry I)
    (hsmall : a.idx.toNat + 1 < UInt256.size) : RunCarry I where
  idx := UInt256.ofNat 1 + a.idx
  last := a.last
  scratch := a.scratch
  fp := a.fp
  mem := a.mem
  aw := a.aw
  rdata := a.rdata
  createdAccounts := a.createdAccounts
  accountMap := a.accountMap
  freePtrMemSize := a.freePtrMemSize
  freePtrRead := a.freePtrRead
  freePtrActive := a.freePtrActive
  freePtr := a.freePtr
  fpMin := a.fpMin
  fpWindow := a.fpWindow
  fpBound := by
    have hnext : (UInt256.ofNat 1 + a.idx).toNat = a.idx.toNat + 1 := by
      rw [uadd_toNat]
      change (1 + a.idx.toNat) % UInt256.size = a.idx.toNat + 1
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    change a.fp.toNat ≤ 128 + (UInt256.ofNat 1 + a.idx).toNat * 2 ^ 139
    rw [hnext]
    exact le_trans a.fpBound
      (Nat.add_le_add_left
        (Nat.mul_le_mul_right (2 ^ 139) (Nat.le_succ a.idx.toNat)) 128)
  awMulBound := a.awMulBound
  fpAdd4 := a.fpAdd4
  returnSub := a.returnSub

theorem runCarryInv_lowGasNext {I : ExecutionEnv} {base : EVM.State} {count : UInt256}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State}
    (hInv : runCarryInv I base count (v + 1) a L evm)
    (hsmall : a.idx.toNat + 1 < UInt256.size) :
    runCarryInv I base count v (a.lowGasNext hsmall)
      ((L.insert "value" (.int 0)).insert "i"
        (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))))
      evm := by
  rcases hInv with
    ⟨htarget, hcount, _hi, hlast, hcountEq, hvariant, hle, henv, hσ₀, hgh, hbl, hcreated,
      haccounts⟩
  have hsmall : a.idx.toNat + 1 < UInt256.size := by
    rw [hcountEq] at hvariant hle
    have hcountSmall : (runCountWord I).toNat < UInt256.size := (runCountWord I).val.isLt
    omega
  have hnext : (UInt256.ofNat 1 + a.idx).toNat = a.idx.toNat + 1 := by
    rw [uadd_toNat]
    change (1 + a.idx.toNat) % UInt256.size = a.idx.toNat + 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_, ?_, ?_, ?_, hcountEq, ?_, ?_, henv, hσ₀, hgh, hbl, hcreated, haccounts⟩
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), htarget]
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hcount]
  · rw [store_get_self]
    rfl
  · rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hlast]
    rfl
  · change (UInt256.ofNat 1 + a.idx).toNat + v = count.toNat
    rw [hnext]
    omega
  · change (UInt256.ofNat 1 + a.idx).toNat ≤ count.toNat
    rw [hnext]
    omega

theorem evalRunCountLe_true (evm : EVM.State) (I : ExecutionEnv)
    (hle : (runCountWord I).toNat ≤ 16) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := runArgStore I } evm
      (.binary .le (.var "count") (.intLit 16)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, runArgStore_count, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hle]

theorem evalRunCountLe_false (evm : EVM.State) (I : ExecutionEnv)
    (hgt : 16 < (runCountWord I).toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := runArgStore I } evm
      (.binary .le (.var "count") (.intLit 16)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, runArgStore_count, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hgt]

theorem evalRunLoopCond_true (evm : EVM.State) (I : ExecutionEnv) (i last : UInt256)
    (hlt : i.toNat < (runCountWord I).toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := runLoopStore I i last } evm
      (.binary .lt (.var "i") (.var "count")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, runLoopStore_i, runLoopStore_count, EvalResult.bind,
    bind]
  simp [evalBinaryOp?, hlt]

theorem evalRunLoopCond_true_of_get (evm : EVM.State) (L : Store)
    (i count : UInt256)
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hcount : L.get? "count" = some (.int (Int.ofNat count.toNat)))
    (hlt : i.toNat < count.toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .lt (.var "i") (.var "count")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, hi, hcount, EvalResult.bind, bind]
  simp [evalBinaryOp?, hlt]

theorem evalRunLoopCond_false (evm : EVM.State) (I : ExecutionEnv) (i last : UInt256)
    (hle : (runCountWord I).toNat ≤ i.toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := runLoopStore I i last } evm
      (.binary .lt (.var "i") (.var "count")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, runLoopStore_i, runLoopStore_count, EvalResult.bind,
    bind]
  simp [evalBinaryOp?, hle]

theorem evalRunLoopCond_false_of_get (evm : EVM.State) (L : Store)
    (i count : UInt256)
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hcount : L.get? "count" = some (.int (Int.ofNat count.toNat)))
    (hle : count.toNat ≤ i.toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .lt (.var "i") (.var "count")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, hi, hcount, EvalResult.bind, bind]
  simp [evalBinaryOp?, hle]

theorem evalSampleRemainingLt_true (evm : EVM.State) (I : ExecutionEnv) (i gasWord : UInt256)
    (hlt : gasWord.toNat < 1000) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := sampleGasStore I i gasWord } evm
      (.binary .lt (.var "remaining") (.intLit 1000)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, sampleGasStore_remaining, EvalResult.bind, bind]
  simp [evalBinaryOp?, hlt]

theorem evalSampleRemainingLt_false (evm : EVM.State) (I : ExecutionEnv) (i gasWord : UInt256)
    (hle : 1000 ≤ gasWord.toNat) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := sampleGasStore I i gasWord } evm
      (.binary .lt (.var "remaining") (.intLit 1000)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, sampleGasStore_remaining, EvalResult.bind, bind]
  simp [evalBinaryOp?, hle]

theorem evalRunBodySampleArgs_of_get (evm : EVM.State) (I : ExecutionEnv) (L : Store)
    (i : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat))) :
  evalExprs? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      [.var "target", .var "i"] = .ok [runTargetValue I, .int (Int.ofNat i.toNat)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, htarget, hi, EvalResult.bind, bind, pure]

theorem bindSampleArgs (I : ExecutionEnv) (i : UInt256) :
    bindParams? sampleFunction.params [runTargetValue I, .int (Int.ofNat i.toNat)] =
      some (sampleStore I i) := by
  simp [sampleFunction, sampleStore, runTargetValue, addr, uint256, bindParams?]

theorem evalValueEqZero_true_of_get (evm : EVM.State) (L : Store)
    (hvalue : L.get? "value" = some (.int 0)) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .eq (.var "value") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, hvalue, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem evalValueEqZero_false_of_get (evm : EVM.State) (L : Store) (value : UInt256)
    (hvalue : L.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hnz : value.toNat ≠ 0) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .eq (.var "value") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, hvalue, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hnz]

theorem evalValueEqOne_true_of_get (evm : EVM.State) (L : Store)
    (hvalue : L.get? "value" = some (.int 1)) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .eq (.var "value") (.intLit 1)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, hvalue, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem evalValueEqOne_false_of_get (evm : EVM.State) (L : Store) (value : UInt256)
    (hvalue : L.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hne : value.toNat ≠ 1) :
    evalExpr? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      (.binary .eq (.var "value") (.intLit 1)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, hvalue, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hne]

theorem intOfNat_uadd_one (i : UInt256) (hsmall : i.toNat + 1 < UInt256.size) :
    Int.ofNat i.toNat + 1 = Int.ofNat ((UInt256.ofNat 1 + i).toNat) := by
  have htoNat : (UInt256.ofNat 1 + i).toNat = i.toNat + 1 := by
    rw [uadd_toNat]
    change (1 + i.toNat) % UInt256.size = i.toNat + 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [htoNat]
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]

theorem nestedCallerSampleLowGas (evm : EVM.State) (I : ExecutionEnv) (i gasWord : UInt256)
    (hlt : gasWord.toNat < 1000) :
    ExecFuncBody nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleStore I i } evm
      sampleFunction.body
      (.returned { contract := nestedCallerContract, locals := sampleGasStore I i gasWord }
        evm (some [.int 0])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.letGas gasWord) ?_
  refine ExecBlock.consReturn ?_
  exact ExecStmt.iteTrue (evalSampleRemainingLt_true evm I i gasWord hlt)
    (ExecBlock.consReturn (ExecStmt.return (by
      simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])))

theorem nestedCallerSampleExternalFailure (evm evm' : EVM.State) (I : ExecutionEnv)
    (i gasWord : UInt256) (out : ByteArray)
    (hge : 1000 ≤ gasWord.toNat)
    (hcall :
      typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
        [.int (Int.ofNat i.toNat)] (false, evm', out) true) :
    ExecFuncBody nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleStore I i } evm
      sampleFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letGas gasWord) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalSampleRemainingLt_false evm I i gasWord hge) ExecBlock.nil) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (by simpa [runTargetValue] using evalSampleProbeReceiver evm I i gasWord)
      (by simp [evalExpr?, pure])
      (evalSampleProbeArgs evm I i gasWord)
      hcall)

theorem nestedCallerSampleExternalDecodeRevert (evm evm' : EVM.State) (I : ExecutionEnv)
    (i gasWord : UInt256) (out : ByteArray)
    (hge : 1000 ≤ gasWord.toNat)
    (hcall :
      typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
        [.int (Int.ofNat i.toNat)] (true, evm', out) true)
    (hdec : nestedCallerConfig.externalABI.decode? "probe" out = none) :
    ExecFuncBody nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleStore I i } evm
      sampleFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.letGas gasWord) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalSampleRemainingLt_false evm I i gasWord hge) ExecBlock.nil) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (by simpa [runTargetValue] using evalSampleProbeReceiver evm I i gasWord)
      (by simp [evalExpr?, pure])
      (evalSampleProbeArgs evm I i gasWord)
      hcall hdec)

theorem nestedCallerSampleExternalSuccess (evm evm' : EVM.State) (I : ExecutionEnv)
    (i value gasWord : UInt256) (out : ByteArray)
    (hge : 1000 ≤ gasWord.toNat)
    (hcall :
      typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
        [.int (Int.ofNat i.toNat)] (true, evm', out) true)
    (hdec :
      nestedCallerConfig.externalABI.decode? "probe" out =
        some [.int (Int.ofNat value.toNat)]) :
    ExecFuncBody nestedCallerConfig
      { contract := nestedCallerContract, locals := sampleStore I i } evm
      sampleFunction.body
      (.returned
        { contract := nestedCallerContract,
          locals := (sampleGasStore I i gasWord).insert "value"
            (.int (Int.ofNat value.toNat)) }
        evm' (some [.int (Int.ofNat value.toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.letGas gasWord) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalSampleRemainingLt_false evm I i gasWord hge) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := (sampleGasStore I i gasWord).insert "value" (.int (Int.ofNat value.toNat)) })
    (evm' := evm') ?_ ?_
  · simpa [collapseReturns] using
      ExecStmt.externalCallSuccess
        (by simpa [runTargetValue] using evalSampleProbeReceiver evm I i gasWord)
        (by simp [evalExpr?, pure])
        (evalSampleProbeArgs evm I i gasWord)
        hcall hdec
  · exact ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, evalExpr?, EvalResult.ofOption, store_get_self,
        EvalResult.bind, bind, pure]))

theorem nestedCallerLoopBodyLowGas (evm : EVM.State) (I : ExecutionEnv) (L : Store)
    (i gasWord : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hgas : gasWord.toNat < 1000) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopBody
      (.continue { contract := nestedCallerContract, locals := L.insert "value" (.int 0) } evm) := by
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int 0) })
    (evm' := evm) ?_ ?_
  · have hlookup : lookupCallable? nestedCallerContract "sample" = some sampleFunction.toCallable := by
      rfl
    simpa [resumeAfterInternalCall, collapseReturns] using internalCallFunctionReturn
      (evalRunBodySampleArgs_of_get evm I L i htarget hi)
      hlookup
      (bindSampleArgs I i)
      (nestedCallerSampleLowGas evm I i gasWord hgas)
  · refine ExecBlock.consContinue ?_
    refine ExecStmt.iteTrue ?_ ?_
    · exact evalValueEqZero_true_of_get evm (L.insert "value" (.int 0))
        (store_get_self L "value" (.int 0))
    · exact ExecBlock.consContinue ExecStmt.continue

theorem nestedCallerLoopBodySampleZero (evm evm1 : EVM.State) (I : ExecutionEnv) (L : Store)
    (i : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hsample :
      ExecFuncBody nestedCallerConfig
        { contract := nestedCallerContract, locals := sampleStore I i } evm
        sampleFunction.body (.returned sampleSolm evm1 (some [.int 0]))) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopBody
      (.continue { contract := nestedCallerContract, locals := L.insert "value" (.int 0) } evm1) := by
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int 0) })
    (evm' := evm1) ?_ ?_
  · have hlookup : lookupCallable? nestedCallerContract "sample" = some sampleFunction.toCallable := by
      rfl
    simpa [resumeAfterInternalCall, collapseReturns] using internalCallFunctionReturn
      (evalRunBodySampleArgs_of_get evm I L i htarget hi)
      hlookup
      (bindSampleArgs I i)
      hsample
  · refine ExecBlock.consContinue ?_
    refine ExecStmt.iteTrue ?_ ?_
    · exact evalValueEqZero_true_of_get evm1 (L.insert "value" (.int 0))
        (store_get_self L "value" (.int 0))
    · exact ExecBlock.consContinue ExecStmt.continue

theorem nestedCallerLoopBodySampleOne (evm evm1 : EVM.State) (I : ExecutionEnv) (L : Store)
    (i : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hsample :
      ExecFuncBody nestedCallerConfig
        { contract := nestedCallerContract, locals := sampleStore I i } evm
        sampleFunction.body (.returned sampleSolm evm1 (some [.int 1]))) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopBody
      (.break { contract := nestedCallerContract, locals := L.insert "value" (.int 1) } evm1) := by
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int 1) })
    (evm' := evm1) ?_ ?_
  · have hlookup : lookupCallable? nestedCallerContract "sample" = some sampleFunction.toCallable := by
      rfl
    simpa [resumeAfterInternalCall, collapseReturns] using internalCallFunctionReturn
      (evalRunBodySampleArgs_of_get evm I L i htarget hi)
      hlookup
      (bindSampleArgs I i)
      hsample
  · refine ExecBlock.consNormal
      (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int 1) })
      (evm' := evm1) ?_ ?_
    · exact ExecStmt.iteFalse
        (evalValueEqZero_false_of_get evm1 (L.insert "value" (.int 1)) (UInt256.ofNat 1)
          (by
            rw [show Int.ofNat (UInt256.ofNat 1).toNat = 1 from by decide]
            exact store_get_self L "value" (.int 1))
          (by decide))
        ExecBlock.nil
    · refine ExecBlock.consBreak ?_
      refine ExecStmt.iteTrue ?_ ?_
      · exact evalValueEqOne_true_of_get evm1 (L.insert "value" (.int 1))
          (store_get_self L "value" (.int 1))
      · exact ExecBlock.consBreak ExecStmt.break

theorem nestedCallerLoopBodySampleOther (evm evm1 : EVM.State) (I : ExecutionEnv) (L : Store)
    (i value : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hnz : value.toNat ≠ 0) (hne : value.toNat ≠ 1)
    (hsample :
      ExecFuncBody nestedCallerConfig
        { contract := nestedCallerContract, locals := sampleStore I i } evm
        sampleFunction.body (.returned sampleSolm evm1 (some [.int (Int.ofNat value.toNat)]))) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopBody
      (ExecResult.ok
        ({ contract := nestedCallerContract, locals := (L.insert "value" (.int (Int.ofNat value.toNat))).insert "last" (.int (Int.ofNat value.toNat)) } : Frame)
        evm1) := by
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int (Int.ofNat value.toNat)) })
    (evm' := evm1) ?_ ?_
  · have hlookup : lookupCallable? nestedCallerContract "sample" = some sampleFunction.toCallable := by
      rfl
    simpa [resumeAfterInternalCall, collapseReturns] using internalCallFunctionReturn
      (evalRunBodySampleArgs_of_get evm I L i htarget hi)
      hlookup
      (bindSampleArgs I i)
      hsample
  · refine ExecBlock.consNormal
      (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int (Int.ofNat value.toNat)) })
      (evm' := evm1) ?_ ?_
    · exact ExecStmt.iteFalse
        (evalValueEqZero_false_of_get evm1 (L.insert "value" (.int (Int.ofNat value.toNat)))
          value (store_get_self L "value" (.int (Int.ofNat value.toNat))) hnz)
        ExecBlock.nil
    · refine ExecBlock.consNormal
        (solm' := { contract := nestedCallerContract, locals := L.insert "value" (.int (Int.ofNat value.toNat)) })
        (evm' := evm1) ?_ ?_
      · exact ExecStmt.iteFalse
          (evalValueEqOne_false_of_get evm1
            (L.insert "value" (.int (Int.ofNat value.toNat))) value
            (store_get_self L "value" (.int (Int.ofNat value.toNat))) hne)
          ExecBlock.nil
      · exact ExecBlock.consNormal
          (solm' := { contract := nestedCallerContract, locals := (L.insert "value" (.int (Int.ofNat value.toNat))).insert "last" (.int (Int.ofNat value.toNat)) })
          (evm' := evm1)
          (ExecStmt.letDecl (by
            simp only [evalExpr?, EvalResult.ofOption, store_get_self]))
          ExecBlock.nil

theorem nestedCallerLoopBodySampleRevert (evm : EVM.State) (I : ExecutionEnv) (L : Store)
    (i : UInt256)
    (htarget : L.get? "target" = some (runTargetValue I))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hsample :
      ExecFuncBody nestedCallerConfig
        { contract := nestedCallerContract, locals := sampleStore I i } evm
        sampleFunction.body .reverted) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopBody
      .reverted := by
  exact ExecBlock.consRevert <|
    internalCallFunctionRevert
      (evalRunBodySampleArgs_of_get evm I L i htarget hi)
      (by rfl)
      (bindSampleArgs I i)
      hsample

theorem nestedCallerLoopPostAdd1 (evm : EVM.State) (L : Store) (i : UInt256)
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hsmall : i.toNat + 1 < UInt256.size) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm loopPost
      (ExecResult.ok
        ({ contract := nestedCallerContract, locals := L.insert "i"
            (.int (Int.ofNat ((UInt256.ofNat 1 + i).toNat))) } : Frame) evm) := by
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  exact ExecStmt.letDecl (by
    simp only [evalExpr?, EvalResult.ofOption, hi, EvalResult.bind, bind,
      evalBinaryOp?]
    rw [intOfNat_uadd_one i hsmall])

theorem evalRunReturnLast_of_get (evm : EVM.State) (L : Store) (last : UInt256)
    (hlast : L.get? "last" = some (.int (Int.ofNat last.toNat))) :
    evalExprs? nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
      [.var "last"] = .ok [.int (Int.ofNat last.toNat)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hlast, EvalResult.bind, bind, pure]

theorem nestedCallerRunBodyFromLoop (evm evm' : EVM.State) (I : ExecutionEnv)
    (L : Store) (last : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hle : (runCountWord I).toNat ≤ 16)
    (hloop :
      ExecForLoop nestedCallerConfig
        { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ } evm
        (.binary .lt (.var "i") (.var "count")) loopPost loopBody
        (.ok { contract := nestedCallerContract, locals := L } evm'))
    (hlast : L.get? "last" = some (.int (Int.ofNat last.toNat))) :
    ExecTransitionBody nestedCallerConfig nestedCallerContract evm (runArgStore I)
      runTransition.body
      (.returned { contract := nestedCallerContract, locals := L } evm'
        (some [.int (Int.ofNat last.toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalRunCountLe_true evm I hle)) ?_
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := runStoreWithLast I })
    (evm' := evm) (ExecStmt.letDecl (by simp [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := L }) (evm' := evm') ?_ ?_
  · have hinit0 :
        ExecBlock nestedCallerConfig
          { contract := nestedCallerContract, locals := runStoreWithLast I } evm
          [.letDecl "i" none (.intLit 0)]
          (ExecResult.ok
            ({ contract := nestedCallerContract, locals := (runStoreWithLast I).insert "i" (.int 0) } : Frame)
            evm) := by
        exact ExecBlock.consNormal
          (solm' := { contract := nestedCallerContract, locals := (runStoreWithLast I).insert "i" (.int 0) })
          (evm' := evm) (ExecStmt.letDecl (by simp [evalExpr?, pure]))
          ExecBlock.nil
    have hinit :
        ExecBlock nestedCallerConfig
          { contract := nestedCallerContract, locals := runStoreWithLast I } evm
          [.letDecl "i" none (.intLit 0)]
          (.ok { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ } evm) := by
      simpa [runLoopStore_init] using hinit0
    exact ExecStmt.for hinit hloop
  · exact ExecBlock.consReturn (ExecStmt.return (evalRunReturnLast_of_get evm' L last hlast))

theorem nestedCallerRunBodyLoopRevert (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hle : (runCountWord I).toNat ≤ 16)
    (hloop :
      ExecForLoop nestedCallerConfig
        { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ } evm
        (.binary .lt (.var "i") (.var "count")) loopPost loopBody
        .reverted) :
    ExecTransitionBody nestedCallerConfig nestedCallerContract evm (runArgStore I)
      runTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalRunCountLe_true evm I hle)) ?_
  refine ExecBlock.consNormal
    (solm' := { contract := nestedCallerContract, locals := runStoreWithLast I })
    (evm' := evm) (ExecStmt.letDecl (by simp [evalExpr?, pure])) ?_
  have hinit0 :
      ExecBlock nestedCallerConfig
        { contract := nestedCallerContract, locals := runStoreWithLast I } evm
        [.letDecl "i" none (.intLit 0)]
        (ExecResult.ok
          ({ contract := nestedCallerContract, locals := (runStoreWithLast I).insert "i" (.int 0) } : Frame)
          evm) := by
    exact ExecBlock.consNormal
      (solm' := { contract := nestedCallerContract, locals := (runStoreWithLast I).insert "i" (.int 0) })
      (evm' := evm) (ExecStmt.letDecl (by simp [evalExpr?, pure]))
      ExecBlock.nil
  have hinit :
      ExecBlock nestedCallerConfig
        { contract := nestedCallerContract, locals := runStoreWithLast I } evm
        [.letDecl "i" none (.intLit 0)]
        (.ok { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ } evm) := by
    simpa [runLoopStore_init] using hinit0
  exact ExecBlock.consRevert (ExecStmt.for hinit hloop)

theorem nestedCallerRunBodyCountTooLarge (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hgt : 16 < (runCountWord I).toNat) :
    ExecTransitionBody nestedCallerConfig nestedCallerContract evm (runArgStore I)
      runTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    nonpayableSecondRequireReverts hwv (evalRunCountLe_false evm I hgt)

theorem nestedCallerRunPrefixToLoop (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hle : (runCountWord I).toNat ≤ 16) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := runArgStore I } evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .le (.var "count") (.intLit 16)),
        .letDecl "last" none (.intLit 0) ]
      (.ok { contract := nestedCallerContract, locals := runStoreWithLast I } evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalRunCountLe_true evm I hle)) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp [evalExpr?, pure]))
    ExecBlock.nil

theorem nestedCallerX_decode407 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨407⟩
      [UInt256.land (runTargetWord I) addrMask, runTargetWord I, ⟨434⟩,
        runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
        (UInt256.ofNat 64) = UInt256.ofNat 0 := by
    simpa using solcDecodeLenCheckOk_4_64 hsz68 hbig hsize
  obtain ⟨k0, C0, rd45⟩ := hreach
  have rd491 := nestedCallerBlocks.nestedCaller_block_45
    (R := [nestedCallerSelWord I]) (hstack := by simp) (hvalid := by jump_dest) rd45
  have hlen : UInt256.ofNat 4 + UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4)
      = UInt256.ofNat I.calldata.size :=
    uadd_word_usub_ofNat_word (c := UInt256.ofNat 4)
      (by rw [show (UInt256.ofNat 4).toNat = 4 from by decide]; omega) hsize
  rw [hlen] at rd491
  have rd513 := nestedCallerBlocks.nestedCaller_block_491_taken
    (R := [⟨66⟩, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hcond := by rw [hslt]; decide) (hvalid := by jump_dest) rd491
  have rd420 := nestedCallerBlocks.nestedCaller_block_513
    (R := [⟨66⟩, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hvalid := by jump_dest) rd513
  have rd398 := nestedCallerBlocks.nestedCaller_block_420
    (R := [UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd420
  have htargetOff : UInt256.ofNat 4 + (⟨0⟩ : UInt256) = UInt256.ofNat 4 := by native_decide
  rw [htargetOff] at rd398
  rw [show (UInt256.ofNat 4).toNat = 4 from rfl] at rd398
  have rd381 := nestedCallerBlocks.nestedCaller_block_398
    (R := [⟨434⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩,
      ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
      nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd398
  have rd350 := nestedCallerBlocks.nestedCaller_block_381
    (R := [⟨407⟩, runTargetWord I, ⟨434⟩, runTargetWord I, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd381
  have rd391 := nestedCallerBlocks.nestedCaller_block_350
    (R := [⟨0⟩, runTargetWord I, ⟨407⟩, runTargetWord I, ⟨434⟩, runTargetWord I,
      ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd350
  have rd407 := nestedCallerBlocks.nestedCaller_block_391
    (R := [runTargetWord I, ⟨434⟩, runTargetWord I, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd391
  exact ⟨_, _, rd407⟩

theorem nestedCallerX_decode93 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus) :
    ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨93⟩
      [runCountWord I, runTargetWord I, ⟨71⟩, nestedCallerSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd407⟩ := nestedCallerX_decode407 hreach hsz68 hsize hbig
  have hclean := runTargetWord_canon_eq (I := I) hcanon
  have rd417 := nestedCallerBlocks.nestedCaller_block_407_taken
    (R := [⟨434⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩,
      ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
      nestedCallerSelWord I])
    (hstack := by simp) (hcond := by rw [hclean]; decide) (hvalid := by jump_dest) rd407
  have rd434 := nestedCallerBlocks.nestedCaller_block_417
    (R := [runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩,
      ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd417
  have rd526 := nestedCallerBlocks.nestedCaller_block_434
    (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
      nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd434
  have rd471 := nestedCallerBlocks.nestedCaller_block_526
    (R := [⟨66⟩, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hvalid := by jump_dest) rd526
  have hoff : (⟨4⟩ : UInt256) + UInt256.ofNat 32 = (⟨36⟩ : UInt256) := by native_decide
  rw [hoff] at rd471
  have rd449 := nestedCallerBlocks.nestedCaller_block_471
    (R := [UInt256.ofNat I.calldata.size, ⟨543⟩, ⟨32⟩, ⟨0⟩, runTargetWord I, ⟨4⟩,
      UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd471
  rw [show ((⟨36⟩ : UInt256).toNat) = 36 from rfl] at rd449
  have rd440 := nestedCallerBlocks.nestedCaller_block_449
    (R := [⟨485⟩, runCountWord I, ⟨36⟩, UInt256.ofNat I.calldata.size, ⟨543⟩,
      ⟨32⟩, ⟨0⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩,
      ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd449
  have rd458 := nestedCallerBlocks.nestedCaller_block_440
    (R := [runCountWord I, ⟨485⟩, runCountWord I, ⟨36⟩, UInt256.ofNat I.calldata.size,
      ⟨543⟩, ⟨32⟩, ⟨0⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
      ⟨66⟩, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd440
  have rd468 := nestedCallerBlocks.nestedCaller_block_458_taken
    (R := [⟨485⟩, runCountWord I, ⟨36⟩, UInt256.ofNat I.calldata.size, ⟨543⟩,
      ⟨32⟩, ⟨0⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩,
      ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hcond := by rw [ueq_self]; decide) (hvalid := by jump_dest) rd458
  have rd485 := nestedCallerBlocks.nestedCaller_block_468
    (R := [runCountWord I, ⟨36⟩, UInt256.ofNat I.calldata.size, ⟨543⟩, ⟨32⟩,
      ⟨0⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
      nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd468
  have rd543 := nestedCallerBlocks.nestedCaller_block_485
    (R := [⟨32⟩, ⟨0⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩,
      ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd485
  have rd66 := nestedCallerBlocks.nestedCaller_block_543
    (R := [⟨71⟩, nestedCallerSelWord I]) (hstack := by simp) (hvalid := by jump_dest) rd543
  have rd93 := nestedCallerBlocks.nestedCaller_block_66
    (R := [runCountWord I, runTargetWord I, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) (hvalid := by jump_dest) rd66
  exact ⟨_, _, rd93⟩

theorem nestedCallerX_loopEntry {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus)
    (hle : (runCountWord I).toNat ≤ 16) :
    ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨116⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, runCountWord I, runTargetWord I, ⟨71⟩, nestedCallerSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd93⟩ := nestedCallerX_decode93 hreach hsz68 hsize hbig hcanon
  have hgtw : UInt256.gt (runCountWord I) (UInt256.ofNat 16) = UInt256.ofNat 0 := by
    simpa using (ugt_zero (a := runCountWord I) (b := (⟨16⟩ : UInt256)) hle)
  have rd107 := nestedCallerBlocks.nestedCaller_block_93_taken
    (R := [runTargetWord I, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hcond := by rw [hgtw]; decide) (hvalid := by jump_dest) rd93
  have rd116 := nestedCallerBlocks.nestedCaller_block_107
    (R := [⟨0⟩, runCountWord I, runTargetWord I, ⟨71⟩, nestedCallerSelWord I])
    (hstack := by simp) rd107
  exact ⟨_, _, rd116⟩

theorem nestedCallerX_loopCond_enter {I g s0 mem aw rdata acc k C}
    {i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨116⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k C)
    (hlt : i.toNat < count.toNat) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨125⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k' C' := by
  have hltw : UInt256.lt i count = UInt256.ofNat 1 := by
    simpa using (ult_one hlt : UInt256.lt i count = ⟨1⟩)
  have rd125 := nestedCallerBlocks.nestedCaller_block_116_fallthrough
    (R := [target, ⟨71⟩, sel]) (hstack := by simp)
    (hcond := by rw [hltw]; decide) rd
  exact ⟨_, _, rd125⟩

theorem nestedCallerX_loopCond_exit {I g s0 mem aw rdata acc k C}
    {i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨116⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k C)
    (hle : count.toNat ≤ i.toNat) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨180⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k' C' := by
  have hltw : UInt256.lt i count = UInt256.ofNat 0 := by
    simpa using (ult_zero (a := i) (b := count) hle)
  have rd180 := nestedCallerBlocks.nestedCaller_block_116_taken
    (R := [target, ⟨71⟩, sel]) (hstack := by simp)
    (hcond := by rw [hltw]; decide) (hvalid := by jump_dest) rd
  exact ⟨_, _, rd180⟩

theorem nestedCallerX_loopExit_toReturn {I g s0 mem aw rdata acc k C}
    {i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨180⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨71⟩
      [last, sel] mem aw rdata acc k' C' := by
  have rd71 := nestedCallerBlocks.nestedCaller_block_180
    (R := [sel]) (hstack := by simp) (hvalid := by jump_dest) rd
  exact ⟨_, _, rd71⟩

theorem nestedCallerX_body_toGas {I g s0 mem aw rdata acc k C}
    {i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨125⟩
      [i, last, scratch, count, target, ⟨71⟩, sel] mem aw rdata acc k C) :
    ∃ gasWord k' C', RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count,
        target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  have rd191 := nestedCallerBlocks.nestedCaller_block_125
    (R := [⟨71⟩, sel]) (hstack := by simp) (hvalid := by jump_dest) rd
  have rd194 := nestedCallerBlocks.nestedCaller_block_191
    (R := [i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) rd191
  obtain ⟨gasWord, rd195⟩ := rd194.rawGas (by decide) (by simp)
  exact ⟨gasWord, _, _, rd195⟩

theorem nestedCallerX_highGas_toCallCursor {I g s0 mem aw rdata acc k C}
    {gasWord i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count,
        target, ⟨71⟩, sel]
      mem aw rdata acc k C)
    (hgas : 1000 ≤ gasWord.toNat) :
    ∃ callGas inOff inSize outOff outSize t memCall awCall k' C',
      RD nestedCallerBytecode I g s0 ⟨285⟩
        (callGas :: UInt256.land addrMask target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: t)
        memCall awCall rdata acc k' C' := by
  have hlt : UInt256.lt gasWord (UInt256.ofNat 1000) = UInt256.ofNat 0 := by
    simpa using (ult_zero (a := gasWord) (b := (⟨1000⟩ : UInt256)) hgas)
  have hcond : UInt256.isZero (UInt256.lt gasWord (UInt256.ofNat 1000)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd215 := nestedCallerBlocks.nestedCaller_block_195_taken
    (R := [⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hcond) (hvalid := by jump_dest) rd
  have rd568 := nestedCallerBlocks.nestedCaller_block_215
    (R := [⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd215
  have rd553 := nestedCallerBlocks.nestedCaller_block_568
    (hstack := by simp) (hvalid := by jump_dest) rd568
  have rd440 := nestedCallerBlocks.nestedCaller_block_553
    (hstack := by simp) (hvalid := by jump_dest) rd553
  have rd562 := nestedCallerBlocks.nestedCaller_block_440
    (hstack := by simp) (hvalid := by jump_dest) rd440
  have rd587 := nestedCallerBlocks.nestedCaller_block_562
    (hstack := by simp) (hvalid := by jump_dest) rd562
  have rd272 := nestedCallerBlocks.nestedCaller_block_587
    (hstack := by simp) (hvalid := by jump_dest) rd587
  have rd284 := nestedCallerBlocks.nestedCaller_block_272
    (hstack := by simp) rd272
  obtain ⟨callGas, rd285⟩ := rd284.rawGas (by decide) (by evm_ov)
  exact ⟨callGas, _, _, _, _, _, _, _, _, _, rd285⟩

theorem nestedCallerX_highGas_toCallCursorExact {I g s0 mem aw rdata acc k C}
    {gasWord i last scratch count target sel fp : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count,
        target, ⟨71⟩, sel]
      mem aw rdata acc k C)
    (hgas : 1000 ≤ gasWord.toNat)
    (hfp : memLoad (UInt256.ofNat 64) aw mem = fp)
    (hfpArg :
      memLoad (UInt256.ofNat 64)
        (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) fp (⟨32⟩ : UInt256))
          (fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
        (probeCalldataMem mem fp i) = fp) :
    ∃ callGas k' C',
      RD nestedCallerBytecode I g s0 ⟨285⟩
        [callGas, UInt256.land addrMask target, ⟨0⟩, fp,
          UInt256.sub ((fp + UInt256.ofNat 4) + UInt256.ofNat 32) fp, fp,
          UInt256.ofNat 32, (fp + UInt256.ofNat 4) + UInt256.ofNat 32,
          UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, i,
          target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
        (probeCalldataMem mem fp i)
        (M
          (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) fp (⟨32⟩ : UInt256))
            (fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
          (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have hlt : UInt256.lt gasWord (UInt256.ofNat 1000) = UInt256.ofNat 0 := by
    simpa using (ult_zero (a := gasWord) (b := (⟨1000⟩ : UInt256)) hgas)
  have hcond : UInt256.isZero (UInt256.lt gasWord (UInt256.ofNat 1000)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd215 := nestedCallerBlocks.nestedCaller_block_195_taken
    (R := [⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hcond) (hvalid := by jump_dest) rd
  have rd568 := nestedCallerBlocks.nestedCaller_block_215
    (R := [⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd215
  rw [hfp] at rd568
  rw [u256_add_comm (UInt256.ofNat 4) fp] at rd568
  have rd553 := nestedCallerBlocks.nestedCaller_block_568
    (R := [UInt256.ofNat 272, UInt256.ofNat 3674743872, UInt256.land addrMask target,
      gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd568
  rw [uadd_zero_right (fp + UInt256.ofNat 4)] at rd553
  have rd440 := nestedCallerBlocks.nestedCaller_block_553
    (R := [fp + UInt256.ofNat 4, UInt256.ofNat 587,
      (fp + UInt256.ofNat 4) + UInt256.ofNat 32, fp + UInt256.ofNat 4, i,
      UInt256.ofNat 272, UInt256.ofNat 3674743872, UInt256.land addrMask target,
      gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd553
  have rd562 := nestedCallerBlocks.nestedCaller_block_440
    (R := [i, fp + UInt256.ofNat 4, UInt256.ofNat 587,
      (fp + UInt256.ofNat 4) + UInt256.ofNat 32, fp + UInt256.ofNat 4, i,
      UInt256.ofNat 272, UInt256.ofNat 3674743872, UInt256.land addrMask target,
      gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd440
  have rd587 := nestedCallerBlocks.nestedCaller_block_562
    (R := [(fp + UInt256.ofNat 4) + UInt256.ofNat 32, fp + UInt256.ofNat 4, i,
      UInt256.ofNat 272, UInt256.ofNat 3674743872, UInt256.land addrMask target,
      gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd562
  change RD nestedCallerBytecode I g s0 (UInt256.ofNat 587)
      (((fp + UInt256.ofNat 4) + UInt256.ofNat 32) :: (fp + UInt256.ofNat 4) :: i ::
        UInt256.ofNat 272 :: UInt256.ofNat 3674743872 :: UInt256.land addrMask target ::
        gasWord :: ⟨0⟩ :: i :: target :: ⟨135⟩ :: ⟨0⟩ :: i :: last :: scratch ::
        count :: target :: ⟨71⟩ :: sel :: [])
      (probeCalldataMem mem fp i)
      (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) fp (⟨32⟩ : UInt256))
        (fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
      rdata (cA, σ) _ _ at rd587
  have rd272 := nestedCallerBlocks.nestedCaller_block_587
    (R := [UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩,
      i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd587
  have rd284 := nestedCallerBlocks.nestedCaller_block_272
    (R := [gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
      ⟨71⟩, sel])
    (hstack := by simp) rd272
  rw [hfpArg] at rd284
  obtain ⟨callGas, rd285⟩ := rd284.rawGas (by decide) (by evm_ov)
  exact ⟨callGas, _, _, rd285⟩

theorem nestedCallerX_callFailureRevert {I g s0 mem aw rdata acc k C}
    {R : List UInt256}
    (hov : R.length + 4 ≤ 1024)
    (rd : RD nestedCallerBytecode I g s0 ⟨286⟩ (⟨0⟩ :: R) mem aw rdata acc k C) :
    RDrev nestedCallerBytecode g s0 := by
  rcases acc with ⟨cA, σ⟩
  have rd293 := nestedCallerBlocks.nestedCaller_block_286_fallthrough
    (R := R) (hstack := by omega) (hcond := by decide) rd
  exact nestedCallerBlocks.nestedCaller_block_293
    (R := [solcCallFailedWord (⟨0⟩ : UInt256)] ++ R)
    (hstack := by simp only [List.length_append, List.length_singleton]; omega) rd293

theorem nestedCallerX_callSuccessDecodeRevert {I g s0 mem aw acc k C}
    {retEnd selectorWord targetClean gasWord i target last scratch count sel retBase : UInt256}
    {o : ByteArray}
    (rd : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, retEnd, selectorWord, targetClean, gasWord, ⟨0⟩, i, target,
        ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw o acc k C)
    (hbase : memLoad (UInt256.ofNat 64) aw mem = retBase)
    (hbad :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) = UInt256.ofNat 0) :
    RDrev nestedCallerBytecode g s0 := by
  rcases acc with ⟨cA, σ⟩
  have rd300 := nestedCallerBlocks.nestedCaller_block_286_taken
    (R := [retEnd, selectorWord, targetClean, gasWord, ⟨0⟩, i, target, ⟨135⟩,
      ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by decide) (hvalid := by jump_dest) rd
  have rd613 := nestedCallerBlocks.nestedCaller_block_300
    (R := [gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
      ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd300
  rw [hbase] at rd613
  have rd626 := nestedCallerBlocks.nestedCaller_block_613_fallthrough
    (R := [UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last,
      scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hbad) rd613
  have rd346 := nestedCallerBlocks.nestedCaller_block_626
    (R := [⟨0⟩, retBase, retBase + UInt256.ofNat o.size, UInt256.ofNat 336, gasWord,
      ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd626
  exact nestedCallerBlocks.nestedCaller_block_346
    (R := [UInt256.ofNat 633, ⟨0⟩, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch,
      count, target, ⟨71⟩, sel])
    (hstack := by simp) rd346

theorem nestedCallerX_callSuccessTo340 {I g s0 mem aw acc k C}
    {retEnd selectorWord targetClean gasWord i target last scratch count sel retBase value : UInt256}
    {o : ByteArray}
    (rd : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, retEnd, selectorWord, targetClean, gasWord, ⟨0⟩, i, target,
        ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw o acc k C)
    (hbase : memLoad (UInt256.ofNat 64) aw mem = retBase)
    (hok :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hload :
      memLoad retBase
        (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256))
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 mem
              (UInt256.ofNat 64).toNat 32)) = value) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨340⟩
      [value, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      (((retBase +
        UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
          (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 mem
            (UInt256.ofNat 64).toNat 32))
      (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
        (⟨32⟩ : UInt256)) retBase (⟨32⟩ : UInt256))
      o acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd300 := nestedCallerBlocks.nestedCaller_block_286_taken
    (R := [retEnd, selectorWord, targetClean, gasWord, ⟨0⟩, i, target, ⟨135⟩,
      ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by decide) (hvalid := by jump_dest) rd
  have rd613 := nestedCallerBlocks.nestedCaller_block_300
    (R := [gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
      ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd300
  rw [hbase] at rd613
  have rd634 := nestedCallerBlocks.nestedCaller_block_613_taken
    (R := [UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last,
      scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hok) (hvalid := by jump_dest) rd613
  have rd593 := nestedCallerBlocks.nestedCaller_block_634
    (R := [UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last,
      scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd634
  rw [uadd_zero_right retBase] at rd593
  have rd449 := nestedCallerBlocks.nestedCaller_block_593
    (R := [retBase + UInt256.ofNat o.size, UInt256.ofNat 647, ⟨0⟩, ⟨0⟩, retBase,
      retBase + UInt256.ofNat o.size, UInt256.ofNat 336, gasWord, ⟨0⟩, i, target,
      ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd593
  rw [hload] at rd449
  have rd440 := nestedCallerBlocks.nestedCaller_block_449
    (R := [UInt256.ofNat 607, value, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 647, ⟨0⟩, ⟨0⟩, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch,
      count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd449
  have rd458 := nestedCallerBlocks.nestedCaller_block_440
    (R := [value, UInt256.ofNat 607, value, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 647, ⟨0⟩, ⟨0⟩, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch,
      count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd440
  have rd468 := nestedCallerBlocks.nestedCaller_block_458_taken
    (R := [UInt256.ofNat 607, value, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 647, ⟨0⟩, ⟨0⟩, retBase, retBase + UInt256.ofNat o.size,
      UInt256.ofNat 336, gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch,
      count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [ueq_self]; decide) (hvalid := by jump_dest) rd458
  have rd607 := nestedCallerBlocks.nestedCaller_block_468
    (R := [value, retBase, retBase + UInt256.ofNat o.size, UInt256.ofNat 647, ⟨0⟩,
      ⟨0⟩, retBase, retBase + UInt256.ofNat o.size, UInt256.ofNat 336, gasWord,
      ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd468
  have rd647 := nestedCallerBlocks.nestedCaller_block_607
    (R := [⟨0⟩, ⟨0⟩, retBase, retBase + UInt256.ofNat o.size, UInt256.ofNat 336,
      gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
      ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd607
  have rd336 := nestedCallerBlocks.nestedCaller_block_647
    (R := [gasWord, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
      ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd647
  have rd340 := nestedCallerBlocks.nestedCaller_block_336
    (R := [i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) rd336
  exact ⟨_, _, rd340⟩

theorem nestedCallerX_sampleZeroContinueFrom340 {I g s0 mem aw rdata acc k C}
    {i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [⟨0⟩, ⟨0⟩, i, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨116⟩
      [(UInt256.ofNat 1) + i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hzero : UInt256.sub (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by
    decide
  have rd145 := nestedCallerBlocks.nestedCaller_block_135_fallthrough
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hzero]) rd135
  have rd169 := nestedCallerBlocks.nestedCaller_block_145
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd145
  have rd116 := nestedCallerBlocks.nestedCaller_block_169
    (R := [last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd169
  exact ⟨_, _, rd116⟩

theorem nestedCallerX_sampleOneBreakFrom340 {I g s0 mem aw rdata acc k C}
    {i scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [UInt256.ofNat 1, ⟨0⟩, i, ⟨135⟩, ⟨0⟩, i, UInt256.ofNat 1, scratch, count,
        target, ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨71⟩
      [UInt256.ofNat 1, sel] mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, UInt256.ofNat 1, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hone_ne : UInt256.sub (UInt256.ofNat 1) (⟨0⟩ : UInt256) ≠ UInt256.ofNat 0 := by
    decide
  have rd150 := nestedCallerBlocks.nestedCaller_block_135_taken
    (R := [i, UInt256.ofNat 1, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hone_ne) (hvalid := by jump_dest) rd135
  have hone_eq : UInt256.sub (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 0 := by
    decide
  have rd159 := nestedCallerBlocks.nestedCaller_block_150_fallthrough
    (R := [i, UInt256.ofNat 1, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hone_eq]) rd150
  have rd180 := nestedCallerBlocks.nestedCaller_block_159
    (R := [i, UInt256.ofNat 1, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd159
  have rd71 := nestedCallerBlocks.nestedCaller_block_180
    (R := [sel]) (hstack := by simp) (hvalid := by jump_dest) rd180
  exact ⟨_, _, rd71⟩

theorem nestedCallerX_sampleOtherContinueFrom340 {I g s0 mem aw rdata acc k C}
    {value i last scratch count target sel : UInt256}
    (hnz : value.toNat ≠ 0) (hne : value.toNat ≠ 1)
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [value, ⟨0⟩, i, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨116⟩
      [(UInt256.ofNat 1) + i, value, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hnzWord : UInt256.sub value (⟨0⟩ : UInt256) ≠ UInt256.ofNat 0 := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      apply hnz
      rw [h]
      rfl)
  have rd150 := nestedCallerBlocks.nestedCaller_block_135_taken
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hnzWord) (hvalid := by jump_dest) rd135
  have hneWord : UInt256.sub value (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      apply hne
      rw [h]
      rfl)
  have rd164 := nestedCallerBlocks.nestedCaller_block_150_taken
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hneWord) (hvalid := by jump_dest) rd150
  have rd169 := nestedCallerBlocks.nestedCaller_block_164
    (x0 := value) (x1 := i) (x2 := last)
    (R := [scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) rd164
  have rd116 := nestedCallerBlocks.nestedCaller_block_169
    (R := [value, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd169
  exact ⟨_, _, rd116⟩

theorem nestedCallerX_sampleZeroContinueFrom340Junk {I g s0 mem aw rdata acc k C}
    {j1 j2 i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [⟨0⟩, j1, j2, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨116⟩
      [(UInt256.ofNat 1) + i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hzero : UInt256.sub (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by
    decide
  have rd145 := nestedCallerBlocks.nestedCaller_block_135_fallthrough
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hzero]) rd135
  have rd169 := nestedCallerBlocks.nestedCaller_block_145
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd145
  have rd116 := nestedCallerBlocks.nestedCaller_block_169
    (R := [last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd169
  exact ⟨_, _, rd116⟩

theorem nestedCallerX_sampleOneBreakFrom340Junk {I g s0 mem aw rdata acc k C}
    {j1 j2 i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [UInt256.ofNat 1, j1, j2, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target,
        ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨71⟩
      [last, sel] mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hone_ne : UInt256.sub (UInt256.ofNat 1) (⟨0⟩ : UInt256) ≠ UInt256.ofNat 0 := by
    decide
  have rd150 := nestedCallerBlocks.nestedCaller_block_135_taken
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hone_ne) (hvalid := by jump_dest) rd135
  have hone_eq : UInt256.sub (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 0 := by
    decide
  have rd159 := nestedCallerBlocks.nestedCaller_block_150_fallthrough
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hone_eq]) rd150
  have rd180 := nestedCallerBlocks.nestedCaller_block_159
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd159
  have rd71 := nestedCallerBlocks.nestedCaller_block_180
    (R := [sel]) (hstack := by simp) (hvalid := by jump_dest) rd180
  exact ⟨_, _, rd71⟩

theorem nestedCallerX_sampleOtherContinueFrom340Junk {I g s0 mem aw rdata acc k C}
    {value j1 j2 i last scratch count target sel : UInt256}
    (hnz : value.toNat ≠ 0) (hne : value.toNat ≠ 1)
    (rd : RD nestedCallerBytecode I g s0 ⟨340⟩
      [value, j1, j2, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k C) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨116⟩
      [(UInt256.ofNat 1) + i, value, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  rcases acc with ⟨cA, σ⟩
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd
  have hnzWord : UInt256.sub value (⟨0⟩ : UInt256) ≠ UInt256.ofNat 0 := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      apply hnz
      rw [h]
      rfl)
  have rd150 := nestedCallerBlocks.nestedCaller_block_135_taken
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hnzWord) (hvalid := by jump_dest) rd135
  have hneWord : UInt256.sub value (UInt256.ofNat 1) ≠ UInt256.ofNat 0 := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      apply hne
      rw [h]
      rfl)
  have rd164 := nestedCallerBlocks.nestedCaller_block_150_taken
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := hneWord) (hvalid := by jump_dest) rd150
  have rd169 := nestedCallerBlocks.nestedCaller_block_164
    (R := [scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) rd164
  have rd116 := nestedCallerBlocks.nestedCaller_block_169
    (R := [value, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd169
  exact ⟨_, _, rd116⟩

theorem nestedCallerX_sampleLowGasContinue {I g s0 mem aw rdata acc k C}
    {gasWord i last scratch count target sel : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count,
        target, ⟨71⟩, sel]
      mem aw rdata acc k C)
    (hgas : gasWord.toNat < 1000) :
    ∃ k' C', RD nestedCallerBytecode I g s0 ⟨116⟩
      [(UInt256.ofNat 1) + i, last, scratch, count, target, ⟨71⟩, sel]
      mem aw rdata acc k' C' := by
  have hlt : UInt256.lt gasWord (UInt256.ofNat 1000) = UInt256.ofNat 1 := by
    simpa using (ult_one (a := gasWord) (b := (⟨1000⟩ : UInt256)) hgas)
  have rd207 := nestedCallerBlocks.nestedCaller_block_195_fallthrough
    (R := [⟨0⟩, i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hlt]; decide) rd
  have rd340 := nestedCallerBlocks.nestedCaller_block_207
    (R := [i, target, ⟨135⟩, ⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd207
  have rd135 := nestedCallerBlocks.nestedCaller_block_340
    (R := [⟨0⟩, i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd340
  have hzero : UInt256.sub (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by
    native_decide
  have rd145 := nestedCallerBlocks.nestedCaller_block_135_fallthrough
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hcond := by rw [hzero]) rd135
  have rd169 := nestedCallerBlocks.nestedCaller_block_145
    (R := [i, last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd145
  have rd116 := nestedCallerBlocks.nestedCaller_block_169
    (ee := I) (g := g) (s0 := s0) (mem := mem) (aw := aw) (rdata := rdata)
    (cA := acc.1) (σ := acc.2) (k := k + 8 + 6 + 6 + 8 + 3)
    (C := C + 30 + 20 + 19 + 27 + 13) (x0 := i)
    (R := [last, scratch, count, target, ⟨71⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd169
  exact ⟨_, _, by simpa using rd116⟩

theorem nestedCallerCarryBodyLowGasBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State} {k C}
    {gasWord : UInt256}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (rd195 : RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, a.idx, target, ⟨135⟩, ⟨0⟩, a.idx, a.last,
        a.scratch, count, target, ⟨71⟩, sel]
      a.mem a.aw a.rdata a.acc k C)
    (hgas : gasWord.toNat < 1000) :
    ∃ a' L1 evm1 L2 evm2 k' C',
      (ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          loopBody (.ok { contract := nestedCallerContract, locals := L1 } evm1) ∨
        ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          loopBody (.continue { contract := nestedCallerContract, locals := L1 } evm1)) ∧
      ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L1 } evm1
        loopPost (.ok { contract := nestedCallerContract, locals := L2 } evm2) ∧
      runCarryInv I s0 count v a' L2 evm2 ∧
      RD nestedCallerBytecode I g s0 ⟨116⟩
        (a'.stack count target sel) a'.mem a'.aw a'.rdata a'.acc k' C' := by
  have hInvAll := hInv
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, hcountEq, hvariant, _hle, _henv, _hcreated, _haccounts⟩
  have hsmall : a.idx.toNat + 1 < UInt256.size := by
    rw [hcountEq] at hvariant
    have hcountSmall : (runCountWord I).toNat < UInt256.size := (runCountWord I).val.isLt
    omega
  have hInvNext := runCarryInv_lowGasNext hInvAll hsmall
  have hbody := nestedCallerLoopBodyLowGas evm I L a.idx gasWord htarget hi hgas
  have hiPost :
      (L.insert "value" (.int 0)).get? "i" = some (.int (Int.ofNat a.idx.toNat)) := by
    rw [store_get_ne _ _ (by decide), hi]
  have hpost := nestedCallerLoopPostAdd1 evm (L.insert "value" (.int 0)) a.idx hiPost hsmall
  obtain ⟨k', C', rd116⟩ := nestedCallerX_sampleLowGasContinue rd195 hgas
  refine ⟨a.lowGasNext hsmall, L.insert "value" (.int 0), evm,
    (L.insert "value" (.int 0)).insert "i"
      (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))),
    evm, k', C', Or.inr hbody, hpost, ?_, ?_⟩
  · exact hInvNext
  · simpa [RunCarry.stack, RunCarry.lowGasNext] using rd116

theorem nestedCallerCarryHighGasToCallCursor {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State} {k C}
    {gasWord : UInt256}
    (_hInv : runCarryInv I s0 count (v + 1) a L evm)
    (rd195 : RD nestedCallerBytecode I g s0 ⟨195⟩
      [gasWord, ⟨0⟩, ⟨0⟩, a.idx, target, ⟨135⟩, ⟨0⟩, a.idx, a.last,
        a.scratch, count, target, ⟨71⟩, sel]
      a.mem a.aw a.rdata a.acc k C)
    (hgas : 1000 ≤ gasWord.toNat) :
    ∃ callGas k' C',
      RD nestedCallerBytecode I g s0 ⟨285⟩
        [callGas, UInt256.land addrMask target, ⟨0⟩, a.fp,
          UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp, a.fp,
          UInt256.ofNat 32, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
          UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
          target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
        (probeCalldataMem a.mem a.fp a.idx)
        (M
          (M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
            (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
          (UInt256.ofNat 64) (⟨32⟩ : UInt256))
        a.rdata a.acc k' C' := by
  exact nestedCallerX_highGas_toCallCursorExact rd195 hgas a.freePtr (a.callFreePtr_value a.idx)

theorem nestedCallerCarryProbeCalldata_eq {I : ExecutionEnv} (a : RunCarry I) :
    nestedCallerConfig.externalABI.encode? "probe" [.int (Int.ofNat a.idx.toNat)] =
      some
        ((probeCalldataMem a.mem a.fp a.idx).readWithPadding a.fp.toNat
          (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat) := by
  rw [nestedCallerEncodeProbe_eq]
  rw [fp_callInputSize_eq a.fp]
  rw [show (UInt256.ofNat 36).toNat = 36 from by decide]
  rw [probeCalldataMem_read a.fpAdd4]

theorem nestedCallerCarryCallMade {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State} {k C}
    {callGas gasWord : UInt256}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (htgt : EVM.address (runTarget I) =
      AccountAddress.ofUInt256 (UInt256.land addrMask target))
    (rd285 : RD nestedCallerBytecode I g s0 ⟨285⟩
      [callGas, UInt256.land addrMask target, ⟨0⟩, a.fp,
        UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp, a.fp,
        UInt256.ofNat 32, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      (probeCalldataMem a.mem a.fp a.idx)
      (M
        (M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
          (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256))
      a.rdata a.acc k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (σ'_solm : AccountMap) (A'_solm : Substate)
      (k' C' : ℕ),
      typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
        [.int (Int.ofNat a.idx.toNat)]
        (z,
          { evm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) true ∧
      accountMapEquiv σ' σ'_solm ∧
      o.size < UInt256.size ∧
      o.size < 2 ^ 138 ∧
      RD nestedCallerBytecode I g s0 ⟨286⟩
        [(if z then ⟨1⟩ else ⟨0⟩), (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
          UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
          target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
        (o.write 0 (probeCalldataMem a.mem a.fp a.idx) a.fp.toNat
          (min (UInt256.ofNat 32) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat
          (MachineState.M
            (MachineState.M
              (M
                (M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp
                  (⟨32⟩ : UInt256))
                  (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
                (UInt256.ofNat 64) (⟨32⟩ : UInt256)).toNat
              a.fp.toNat
              (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat)
            a.fp.toNat
            (UInt256.ofNat 32).toNat))
        o (cA', σ') k' C' := by
  rcases hInv with
    ⟨_htarget, _hcount, _hi, _hlast, _hcountEq, _hvariant, _hle, henv, hσ₀, hgh, hbl,
      hcreated, haccounts⟩
  obtain ⟨cA', σ', z, o, A_in, callGas', k', C', hThetaEx, rd286, hosz⟩ :=
    RD.call rd285 (by native_decide) hdepth (by simp)
  obtain ⟨g'', A', hTheta⟩ := hThetaEx
  let evmE : EVM.State := { evm with accountMap := a.accountMap, createdAccounts := a.createdAccounts }
  have hTheta' :
      (cA', σ', g'', A', z, o) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender
          (AccountAddress.ofUInt256 (UInt256.land addrMask target))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (UInt256.land addrMask target)))
          callGas' (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((probeCalldataMem a.mem a.fp a.idx).readWithPadding a.fp.toNat
            (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, henv, hσ₀, hgh, hbl, hperm] using hTheta
  obtain ⟨σ'_solm, A'_solm, hcall, hacc⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := nestedCallerConfig) (evm_evm := evmE) (evm_solm := evm)
      (tgt := EVM.address (runTarget I)) (targetWord := UInt256.land addrMask target)
      (name := "probe") (args := [.int (Int.ofNat a.idx.toNat)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z) (out := o)
      (g'' := g'') (callGas := callGas')
      (mem := probeCalldataMem a.mem a.fp a.idx) (inOff := a.fp)
      (inSize := UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp)
      (callPerm := true)
      (by
        intro hdepthEq
        simp [evmE, henv] at hdepthEq
        exact absurd hdepthEq (by
          intro h
          have := I.depth.isLt
          rw [h] at this
          omega))
      htgt (nestedCallerCarryProbeCalldata_eq a) hTheta'
      haccounts rfl (by simpa [evmE] using hcreated.symm) rfl rfl rfl rfl
  have ho138 : o.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      evmE.executionEnv.blobVersionedHashes evmE.createdAccounts evmE.genesisBlockHeader
      evmE.blocks evmE.accountMap evmE.σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
      evmE.executionEnv.sender
      (AccountAddress.ofUInt256 (UInt256.land addrMask target))
      (toExecute evmE.accountMap (AccountAddress.ofUInt256 (UInt256.land addrMask target)))
      callGas' (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
      ((probeCalldataMem a.mem a.fp a.idx).readWithPadding a.fp.toNat
        (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat)
      (evmE.executionEnv.depth + 1) evmE.executionEnv.header true
      hTheta'
      (Ethereum.EVM.ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas _ _ _)
  refine ⟨cA', σ', z, o, σ'_solm, A'_solm, k', C', hcall, hacc, hosz, ho138, ?_⟩
  simpa using rd286

theorem nestedCallerCarryCallDepthLimitRevert {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm : EVM.State} {k C}
    {callGas gasWord : UInt256}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hdepth : I.depth = 1024)
    (rd285 : RD nestedCallerBytecode I g s0 ⟨285⟩
      [callGas, UInt256.land addrMask target, ⟨0⟩, a.fp,
        UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp, a.fp,
        UInt256.ofNat 32, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      (probeCalldataMem a.mem a.fp a.idx)
      (M
        (M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp (⟨32⟩ : UInt256))
          (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
        (UInt256.ofNat 64) (⟨32⟩ : UInt256))
      a.rdata a.acc k C) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
        loopBody .reverted ∧
      RDrev nestedCallerBytecode g s0 := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hcall :
      typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
        [.int (Int.ofNat a.idx.toNat)]
        (false,
          { evm with substate := (evm.addAccessedAccount (EVM.address (runTarget I))).substate },
          ByteArray.empty) true := by
    exact callNotMade_depthLimit
      (cfg := nestedCallerConfig) (evm := evm) (tgt := EVM.address (runTarget I))
      (name := "probe") (args := [.int (Int.ofNat a.idx.toNat)])
      (calldata := probeSelector ++ a.idx.toByteArray) (callPerm := true)
      (nestedCallerEncodeProbe_eq a.idx)
      (by rw [henv]; exact hdepth)
  have hsample := nestedCallerSampleExternalFailure evm
    ({ evm with substate := (evm.addAccessedAccount (EVM.address (runTarget I))).substate })
    I a.idx gasWord ByteArray.empty hgas hcall
  have hbody := nestedCallerLoopBodySampleRevert evm I L a.idx htarget hi hsample
  obtain ⟨k', C', rd286⟩ := RD.callDepthLimit rd285 (by native_decide) hdepth (by simp)
  have rd286' : RD nestedCallerBytecode I g s0 ⟨286⟩
      [⟨0⟩, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      (probeCalldataMem a.mem a.fp a.idx)
      (UInt256.ofNat
        (MachineState.M
          (MachineState.M
            (M
              (M (M (M a.aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) a.fp
                (⟨32⟩ : UInt256))
                (a.fp + UInt256.ofNat 4) (⟨32⟩ : UInt256))
              (UInt256.ofNat 64) (⟨32⟩ : UInt256)).toNat
            a.fp.toNat
            (UInt256.sub ((a.fp + UInt256.ofNat 4) + UInt256.ofNat 32) a.fp).toNat)
          a.fp.toNat
          (UInt256.ofNat 32).toNat))
      ByteArray.empty a.acc k' C' := by
    simpa [byteArray_write_len_zero] using rd286
  exact ⟨hbody, nestedCallerX_callFailureRevert (R :=
    [(a.fp + UInt256.ofNat 4) + UInt256.ofNat 32, UInt256.ofNat 3674743872,
      UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx, target, ⟨135⟩, ⟨0⟩,
      a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel])
    (hov := by simp) rd286'⟩

theorem nestedCallerCarryCallFailureRevertBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm evm1 : EVM.State} {k C}
    {gasWord : UInt256} {o memPost : ByteArray} {awPost : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hcall : typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
      [.int (Int.ofNat a.idx.toNat)] (false, evm1, o) true)
    (rd286 : RD nestedCallerBytecode I g s0 ⟨286⟩
      [⟨0⟩, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      memPost awPost o (cA', σ') k C) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
        loopBody .reverted ∧
      RDrev nestedCallerBytecode g s0 := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hsample := nestedCallerSampleExternalFailure evm evm1 I a.idx gasWord o hgas hcall
  have hbody := nestedCallerLoopBodySampleRevert evm I L a.idx htarget hi hsample
  exact ⟨hbody, nestedCallerX_callFailureRevert (R :=
    [(a.fp + UInt256.ofNat 4) + UInt256.ofNat 32, UInt256.ofNat 3674743872,
      UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx, target, ⟨135⟩, ⟨0⟩,
      a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel])
    (hov := by simp) rd286⟩

theorem nestedCallerCarryCallDecodeRevertBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm evm1 : EVM.State} {k C}
    {gasWord retBase : UInt256} {o memPost : ByteArray} {awPost : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hcall : typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
      [.int (Int.ofNat a.idx.toNat)] (true, evm1, o) true)
    (hdec : nestedCallerConfig.externalABI.decode? "probe" o = none)
    (hbase : memLoad (UInt256.ofNat 64) awPost memPost = retBase)
    (hbad :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) = UInt256.ofNat 0)
    (rd286 : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      memPost awPost o (cA', σ') k C) :
    ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
        loopBody .reverted ∧
      RDrev nestedCallerBytecode g s0 := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hsample := nestedCallerSampleExternalDecodeRevert evm evm1 I a.idx gasWord o hgas hcall hdec
  have hbody := nestedCallerLoopBodySampleRevert evm I L a.idx htarget hi hsample
  have hrd := nestedCallerX_callSuccessDecodeRevert
    (retEnd := (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32)
    (selectorWord := UInt256.ofNat 3674743872)
    (targetClean := UInt256.land addrMask target)
    (last := a.last) (scratch := a.scratch)
    rd286 hbase hbad
  exact ⟨hbody, hrd⟩

theorem nestedCallerCarryCallSuccessZeroBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm evm1 : EVM.State} {k C}
    {gasWord retBase : UInt256} {o memPost : ByteArray} {awPost : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hcall : typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
      [.int (Int.ofNat a.idx.toNat)] (true, evm1, o) true)
    (hdec : nestedCallerConfig.externalABI.decode? "probe" o = some [.int 0])
    (hbase : memLoad (UInt256.ofNat 64) awPost memPost = retBase)
    (hok :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hload :
      memLoad retBase
        (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256))
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32)) = (⟨0⟩ : UInt256))
    (rd286 : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      memPost awPost o (cA', σ') k C) :
    ∃ k' C', ExecBlock nestedCallerConfig
        { contract := nestedCallerContract, locals := L } evm loopBody
        (.continue { contract := nestedCallerContract, locals := L.insert "value" (.int 0) } evm1) ∧
      RD nestedCallerBytecode I g s0 ⟨116⟩
        [(UInt256.ofNat 1) + a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32))
        (M (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256)) retBase (⟨32⟩ : UInt256))
        o (cA', σ') k' C' := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hsample := nestedCallerSampleExternalSuccess evm evm1 I a.idx (⟨0⟩ : UInt256) gasWord o
    hgas hcall (by simpa using hdec)
  have hbody := nestedCallerLoopBodySampleZero evm evm1 I L a.idx htarget hi hsample
  obtain ⟨k340, C340, rd340⟩ := nestedCallerX_callSuccessTo340
    (retEnd := (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32)
    (selectorWord := UInt256.ofNat 3674743872)
    (targetClean := UInt256.land addrMask target)
    (last := a.last) (scratch := a.scratch)
    rd286 hbase hok hload
  obtain ⟨k116, C116, rd116⟩ := nestedCallerX_sampleZeroContinueFrom340Junk
    (j1 := a.idx) (j2 := target) rd340
  exact ⟨k116, C116, hbody, rd116⟩

theorem nestedCallerCarryCallSuccessOneBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm evm1 : EVM.State} {k C}
    {gasWord retBase : UInt256} {o memPost : ByteArray} {awPost : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hcall : typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
      [.int (Int.ofNat a.idx.toNat)] (true, evm1, o) true)
    (hdec : nestedCallerConfig.externalABI.decode? "probe" o = some [.int 1])
    (hbase : memLoad (UInt256.ofNat 64) awPost memPost = retBase)
    (hok :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hload :
      memLoad retBase
        (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256))
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32)) = (⟨1⟩ : UInt256))
    (rd286 : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      memPost awPost o (cA', σ') k C) :
    ∃ k' C', ExecBlock nestedCallerConfig
        { contract := nestedCallerContract, locals := L } evm loopBody
        (.break { contract := nestedCallerContract, locals := L.insert "value" (.int 1) } evm1) ∧
      RD nestedCallerBytecode I g s0 ⟨71⟩ [a.last, sel]
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32))
        (M (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256)) retBase (⟨32⟩ : UInt256))
        o (cA', σ') k' C' := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hsample := nestedCallerSampleExternalSuccess evm evm1 I a.idx (⟨1⟩ : UInt256) gasWord o
    hgas hcall (by simpa using hdec)
  have hbody := nestedCallerLoopBodySampleOne evm evm1 I L a.idx htarget hi hsample
  obtain ⟨k340, C340, rd340⟩ := nestedCallerX_callSuccessTo340
    (retEnd := (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32)
    (selectorWord := UInt256.ofNat 3674743872)
    (targetClean := UInt256.land addrMask target)
    (last := a.last) (scratch := a.scratch)
    rd286 hbase hok hload
  obtain ⟨k71, C71, rd71⟩ := nestedCallerX_sampleOneBreakFrom340Junk
    (j1 := a.idx) (j2 := target) rd340
  exact ⟨k71, C71, hbody, rd71⟩

theorem nestedCallerCarryCallSuccessOtherBranch {I g s0 count target sel}
    {v : ℕ} {a : RunCarry I} {L : Store} {evm evm1 : EVM.State} {k C}
    {gasWord retBase value : UInt256} {o memPost : ByteArray} {awPost : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    (hInv : runCarryInv I s0 count (v + 1) a L evm)
    (hgas : 1000 ≤ gasWord.toNat)
    (hcall : typedCallViaEVM nestedCallerConfig evm (EVM.address (runTarget I)) "probe" 0
      [.int (Int.ofNat a.idx.toNat)] (true, evm1, o) true)
    (hdec : nestedCallerConfig.externalABI.decode? "probe" o =
      some [.int (Int.ofNat value.toNat)])
    (hnz : value.toNat ≠ 0) (hne : value.toNat ≠ 1)
    (hbase : memLoad (UInt256.ofNat 64) awPost memPost = retBase)
    (hok :
      UInt256.isZero
        (UInt256.slt (UInt256.sub (retBase + UInt256.ofNat o.size) retBase)
          (UInt256.ofNat 32)) ≠ UInt256.ofNat 0)
    (hload :
      memLoad retBase
        (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256))
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32)) = value)
    (rd286 : RD nestedCallerBytecode I g s0 ⟨286⟩
      [UInt256.ofNat 1, (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32,
        UInt256.ofNat 3674743872, UInt256.land addrMask target, gasWord, ⟨0⟩, a.idx,
        target, ⟨135⟩, ⟨0⟩, a.idx, a.last, a.scratch, count, target, ⟨71⟩, sel]
      memPost awPost o (cA', σ') k C) :
    ∃ k' C', ExecBlock nestedCallerConfig
        { contract := nestedCallerContract, locals := L } evm loopBody
        (ExecResult.ok
          (⟨nestedCallerContract, ((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
            (.int (Int.ofNat value.toNat)))⟩ : Frame) evm1) ∧
      RD nestedCallerBytecode I g s0 ⟨116⟩
        [(UInt256.ofNat 1) + a.idx, value, a.scratch, count, target, ⟨71⟩, sel]
        (((retBase +
          UInt256.land ((UInt256.ofNat o.size) + UInt256.ofNat 31)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 memPost
              (UInt256.ofNat 64).toNat 32))
        (M (M (M awPost (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64)
          (⟨32⟩ : UInt256)) retBase (⟨32⟩ : UInt256))
        o (cA', σ') k' C' := by
  rcases hInv with
    ⟨htarget, _hcount, hi, _hlast, _hcountEq, _hvariant, _hle, _henv, _hσ₀, _hgh, _hbl,
      _hcreated, _haccounts⟩
  have hsample := nestedCallerSampleExternalSuccess evm evm1 I a.idx value gasWord o
    hgas hcall hdec
  have hbody := nestedCallerLoopBodySampleOther evm evm1 I L a.idx value htarget hi hnz hne hsample
  obtain ⟨k340, C340, rd340⟩ := nestedCallerX_callSuccessTo340
    (retEnd := (a.fp + UInt256.ofNat 4) + UInt256.ofNat 32)
    (selectorWord := UInt256.ofNat 3674743872)
    (targetClean := UInt256.land addrMask target)
    (last := a.last) (scratch := a.scratch)
    rd286 hbase hok hload
  obtain ⟨k116, C116, rd116⟩ := nestedCallerX_sampleOtherContinueFrom340Junk
    hnz hne (j1 := a.idx) (j2 := target) rd340
  exact ⟨k116, C116, hbody, rd116⟩

/-- `RD.execForLoopOrRevertBreakContinueCarryFull` with return data in the carried state.

NestedCaller's loop body may execute `CALL`, which updates EVM return data before the next loop
header.  The library combinator keeps `rdata` fixed; this local variant is the same induction with
`rdata : α → ByteArray`. -/
theorem execForLoopOrRevertBreakContinueCarryFullRData {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {α : Type}
    (header bodyHeader exit : UInt256) (condExpr : Expr) (post body : List Stmt)
    (Inv : ℕ → α → Store → EVM.State → Prop) (Done : α → Store → EVM.State → Prop)
    (stk : α → List UInt256) (mem : α → ByteArray) (aw : α → UInt256)
    (rdata : α → ByteArray) (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool false))
    (hdoneFalse : ∀ a L evm, Inv 0 a L evm → Done a L evm)
    (hexit : ∀ a L evm, Done a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) (rdata a) (acc a) k C →
      ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) (rdata a) (acc a) k' C')
    (htrue : ∀ v a L evm, Inv (v + 1) a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool true))
    (henter : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) (rdata a) (acc a) k C →
      ∃ k' C', RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) (rdata a) (acc a) k' C')
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) (rdata a) (acc a) k C →
      (ExecBlock cfg { contract := contract, locals := L } evm body .reverted ∧
        RDrev code g s0) ∨
      (∃ a' L1 evm1 k' C',
        ExecBlock cfg { contract := contract, locals := L } evm body
          (.break { contract := contract, locals := L1 } evm1) ∧
        Done a' L1 evm1 ∧
        RD code ee g s0 exit (exitStk a') (mem a') (aw a') (rdata a') (acc a') k' C') ∨
      ∃ a' L1 evm1 L2 evm2 k' C',
        (ExecBlock cfg { contract := contract, locals := L } evm body
            (.ok { contract := contract, locals := L1 } evm1) ∨
          ExecBlock cfg { contract := contract, locals := L } evm body
            (.continue { contract := contract, locals := L1 } evm1)) ∧
        ExecBlock cfg { contract := contract, locals := L1 } evm1 post
          (.ok { contract := contract, locals := L2 } evm2) ∧
        Inv v a' L2 evm2 ∧
        RD code ee g s0 header (stk a') (mem a') (aw a') (rdata a') (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) (rdata a) (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body
          (.ok { contract := contract, locals := L' } evm') ∧
        Done a' L' evm' ∧
        RD code ee g s0 exit (exitStk a') (mem a') (aw a') (rdata a') (acc a') k' C') ∨
      (ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body .reverted ∧
        RDrev code g s0) := by
  intro v
  induction v with
  | zero =>
      intro a L evm hInv k C rd
      have hDone : Done a L evm := hdoneFalse a L evm hInv
      obtain ⟨k', C', rdExit⟩ := hexit a L evm hDone k C rd
      exact Or.inl ⟨a, L, evm, k', C', ExecForLoop.falseDone (hfalse a L evm hInv),
        hDone, rdExit⟩
  | succ v ih =>
      intro a L evm hInv k C rd
      obtain ⟨k1, C1, rdBody⟩ := henter v a L evm hInv k C rd
      rcases hbody v a L evm hInv k1 C1 rdBody with hrev | hbodyNonRevert
      · exact Or.inr ⟨ExecForLoop.bodyRevert (htrue v a L evm hInv) hrev.1, hrev.2⟩
      · rcases hbodyNonRevert with hbreak | hstep
        · rcases hbreak with ⟨a', L1, evm1, k2, C2, hbodyBreak, hDone, rdExit⟩
          exact Or.inl ⟨a', L1, evm1, k2, C2,
            ExecForLoop.bodyBreak (htrue v a L evm hInv) hbodyBreak, hDone, rdExit⟩
        · rcases hstep with
            ⟨a', L1, evm1, L2, evm2, k2, C2, hbodyStep, hpost, hInv', rdNext⟩
          rcases ih a' L2 evm2 hInv' k2 C2 rdNext with hdone | hloopRev
          · rcases hdone with ⟨a'', L', evm', k', C', hloop, hDone, rdExit⟩
            rcases hbodyStep with hbodyOk | hbodyCont
            · exact Or.inl ⟨a'', L', evm', k', C',
                ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop,
                hDone, rdExit⟩
            · exact Or.inl ⟨a'', L', evm', k', C',
                ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
                hDone, rdExit⟩
          · rcases hloopRev with ⟨hloop, hrdRev⟩
            rcases hbodyStep with hbodyOk | hbodyCont
            · exact Or.inr
                ⟨ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop, hrdRev⟩
            · exact Or.inr
                ⟨ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
                  hrdRev⟩

/-- NestedCaller-specialized wrapper around the rdata-carrying loop combinator.

The bytecode loop exits to pc 71 after the Solidity loop condition becomes false; a Solidity
`break` body proof should therefore also produce the pc-71 cursor directly.  The `Done` predicate is
allowed to forget the final loop index, so break cases can choose any carried index convenient for
the final return proof. -/
theorem nestedCallerRunLoop_from_body_or_revert {I} {g : Sat256} {s0 : State} {α : Type}
    (count target sel : UInt256)
    (Inv : ℕ → α → Store → EVM.State → Prop)
    (Done : α → Store → EVM.State → Prop)
    (idx last scratch : α → UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (rdata : α → ByteArray)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (hshape : ∀ v a L evm, Inv v a L evm →
      L.get? "target" = some (runTargetValue I) ∧
      L.get? "count" = some (.int (Int.ofNat count.toNat)) ∧
      L.get? "i" = some (.int (Int.ofNat (idx a).toNat)) ∧
      L.get? "last" = some (.int (Int.ofNat (last a).toNat)) ∧
      count = runCountWord I ∧
      (idx a).toNat + v = count.toNat ∧
      (idx a).toNat ≤ count.toNat)
    (hdoneFalse : ∀ a L evm, Inv 0 a L evm → Done a L evm)
    (hdoneExit : ∀ a L evm, Done a L evm → count.toNat ≤ (idx a).toNat)
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
        RD nestedCallerBytecode I g s0 ⟨125⟩
          [idx a, last a, scratch a, count, target, ⟨71⟩, sel]
          (mem a) (aw a) (rdata a) (acc a) k C →
        (ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
            loopBody .reverted ∧
          RDrev nestedCallerBytecode g s0) ∨
        (∃ a' L1 evm1 k' C',
          ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
            loopBody (.break { contract := nestedCallerContract, locals := L1 } evm1) ∧
          Done a' L1 evm1 ∧
          RD nestedCallerBytecode I g s0 ⟨71⟩ [last a', sel]
            (mem a') (aw a') (rdata a') (acc a') k' C') ∨
        ∃ a' L1 evm1 L2 evm2 k' C',
          (ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
              loopBody (.ok { contract := nestedCallerContract, locals := L1 } evm1) ∨
            ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
              loopBody (.continue { contract := nestedCallerContract, locals := L1 } evm1)) ∧
          ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L1 } evm1
            loopPost (.ok { contract := nestedCallerContract, locals := L2 } evm2) ∧
          Inv v a' L2 evm2 ∧
          RD nestedCallerBytecode I g s0 ⟨116⟩
            [idx a', last a', scratch a', count, target, ⟨71⟩, sel]
            (mem a') (aw a') (rdata a') (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD nestedCallerBytecode I g s0 ⟨116⟩
        [idx a, last a, scratch a, count, target, ⟨71⟩, sel]
        (mem a) (aw a) (rdata a) (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody
          (.ok { contract := nestedCallerContract, locals := L' } evm') ∧
        Done a' L' evm' ∧
        RD nestedCallerBytecode I g s0 ⟨71⟩ [last a', sel]
          (mem a') (aw a') (rdata a') (acc a') k' C') ∨
      (ExecForLoop nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody .reverted ∧
        RDrev nestedCallerBytecode g s0) := by
  refine execForLoopOrRevertBreakContinueCarryFullRData
    (cfg := nestedCallerConfig) (contract := nestedCallerContract)
    (code := nestedCallerBytecode) (ee := I) (g := g) (s0 := s0)
    (header := ⟨116⟩) (bodyHeader := ⟨125⟩) (exit := ⟨71⟩)
    (condExpr := (.binary .lt (.var "i") (.var "count")))
    (post := loopPost) (body := loopBody)
    (Inv := Inv) (Done := Done)
    (stk := fun a => [idx a, last a, scratch a, count, target, ⟨71⟩, sel])
    (mem := mem) (aw := aw) (rdata := rdata) (acc := acc)
    (exitStk := fun a => [last a, sel])
    ?_ hdoneFalse ?_ ?_ ?_ hbody
  · intro a L evm hInv
    rcases hshape 0 a L evm hInv with ⟨_htarget, hcountGet, hi, _hlast, _hcount, hvar, _hle⟩
    exact evalRunLoopCond_false_of_get evm L (idx a) count hi hcountGet (by omega)
  · intro a L evm hDone k C rd
    obtain ⟨k1, C1, rd180⟩ := nestedCallerX_loopCond_exit
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata a) (acc := acc a)
      (i := idx a) (last := last a) (scratch := scratch a) (count := count)
      (target := target) (sel := sel) rd (hdoneExit a L evm hDone)
    exact nestedCallerX_loopExit_toReturn
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (mem := mem a) (aw := aw a) (rdata := rdata a) (acc := acc a)
      (i := idx a) (last := last a) (scratch := scratch a) (count := count)
      (target := target) (sel := sel) rd180
  · intro v a L evm hInv
    rcases hshape (v + 1) a L evm hInv with
      ⟨_htarget, hcountGet, hi, _hlast, _hcount, hvar, _hle⟩
    exact evalRunLoopCond_true_of_get evm L (idx a) count hi hcountGet (by omega)
  · intro v a L evm hInv k C rd
    rcases hshape (v + 1) a L evm hInv with
      ⟨_htarget, _hcountGet, _hi, _hlast, _hcount, hvar, _hle⟩
    exact nestedCallerX_loopCond_enter
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata a) (acc := acc a)
      (i := idx a) (last := last a) (scratch := scratch a) (count := count)
      (target := target) (sel := sel) rd (by omega)

theorem nestedCallerRunLoop_from_carry_body_or_revert {I} {g : Sat256} {s0 : State}
    (count target sel : UInt256)
    (hbody : ∀ v a L evm, runCarryInv I s0 count (v + 1) a L evm → ∀ k C,
        RD nestedCallerBytecode I g s0 ⟨125⟩
          (a.stack count target sel) a.mem a.aw a.rdata a.acc k C →
        (ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
            loopBody .reverted ∧
          RDrev nestedCallerBytecode g s0) ∨
        (∃ a' L1 evm1 k' C',
          ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
            loopBody (.break { contract := nestedCallerContract, locals := L1 } evm1) ∧
          runCarryDone I count a' L1 evm1 ∧
          RD nestedCallerBytecode I g s0 ⟨71⟩ [a'.last, sel]
            a'.mem a'.aw a'.rdata a'.acc k' C') ∨
        ∃ a' L1 evm1 L2 evm2 k' C',
          (ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
              loopBody (.ok { contract := nestedCallerContract, locals := L1 } evm1) ∨
            ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
              loopBody (.continue { contract := nestedCallerContract, locals := L1 } evm1)) ∧
          ExecBlock nestedCallerConfig { contract := nestedCallerContract, locals := L1 } evm1
            loopPost (.ok { contract := nestedCallerContract, locals := L2 } evm2) ∧
          runCarryInv I s0 count v a' L2 evm2 ∧
          RD nestedCallerBytecode I g s0 ⟨116⟩
            (a'.stack count target sel) a'.mem a'.aw a'.rdata a'.acc k' C') :
    ∀ v a L evm, runCarryInv I s0 count v a L evm → ∀ k C,
      RD nestedCallerBytecode I g s0 ⟨116⟩
        (a.stack count target sel) a.mem a.aw a.rdata a.acc k C →
      (∃ a' L' evm' k' C',
        ExecForLoop nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody
          (.ok { contract := nestedCallerContract, locals := L' } evm') ∧
        runCarryDone I count a' L' evm' ∧
        RD nestedCallerBytecode I g s0 ⟨71⟩ [a'.last, sel]
          a'.mem a'.aw a'.rdata a'.acc k' C') ∨
      (ExecForLoop nestedCallerConfig { contract := nestedCallerContract, locals := L } evm
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody .reverted ∧
        RDrev nestedCallerBytecode g s0) := by
  exact nestedCallerRunLoop_from_body_or_revert
    (I := I) (g := g) (s0 := s0) (count := count) (target := target) (sel := sel)
    (Inv := runCarryInv I s0 count) (Done := runCarryDone I count)
    (idx := RunCarry.idx) (last := RunCarry.last) (scratch := RunCarry.scratch)
    (mem := RunCarry.mem) (aw := RunCarry.aw) (rdata := RunCarry.rdata)
    (acc := RunCarry.acc)
    (hshape := by intro v a L evm h; exact runCarryInv_shape h)
    (hdoneFalse := by intro a L evm h; exact runCarryDone_of_inv_zero h)
    (hdoneExit := by intro a L evm h; exact runCarryDone_exit h)
    hbody

theorem nestedCallerX_returnWord {I g s0 mem aw rdata acc k C}
    {last sel fp : UInt256}
    (rd : RD nestedCallerBytecode I g s0 ⟨71⟩ [last, sel] mem aw rdata acc k C)
    (hfp : memLoad (UInt256.ofNat 64) aw mem = fp)
    (hfpAfter :
      memLoad (UInt256.ofNat 64)
        (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) fp (⟨32⟩ : UInt256))
        (last.toByteArray.write 0 mem fp.toNat 32) = fp)
    (hsub : UInt256.sub (fp + (UInt256.ofNat 32)) fp = UInt256.ofNat 32)
    (hread :
      (last.toByteArray.write 0 mem fp.toNat 32).readWithPadding fp.toNat 32 =
        UInt256.toByteArray last) :
    RDret nestedCallerBytecode g s0 acc (UInt256.toByteArray last) := by
  rcases acc with ⟨cA, σ⟩
  have rd568 := nestedCallerBlocks.nestedCaller_block_71
    (R := [sel]) (hstack := by simp) (hvalid := by jump_dest) rd
  rw [hfp] at rd568
  have rd553 := nestedCallerBlocks.nestedCaller_block_568
    (R := [⟨84⟩, sel]) (hstack := by simp) (hvalid := by jump_dest) rd568
  have rd440 := nestedCallerBlocks.nestedCaller_block_553
    (R := [fp + (⟨0⟩ : UInt256), ⟨587⟩, fp + (UInt256.ofNat 32), fp, last, ⟨84⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd553
  have rd562 := nestedCallerBlocks.nestedCaller_block_440
    (R := [last, fp + (⟨0⟩ : UInt256), ⟨587⟩, fp + (UInt256.ofNat 32), fp, last,
      ⟨84⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd440
  have rd587 := nestedCallerBlocks.nestedCaller_block_562
    (R := [fp + (UInt256.ofNat 32), fp, last, ⟨84⟩, sel])
    (hstack := by simp) (hvalid := by jump_dest) rd562
  have rd84 := nestedCallerBlocks.nestedCaller_block_587
    (R := [sel]) (hstack := by simp) (hvalid := by jump_dest) rd587
  have hret := nestedCallerBlocks.nestedCaller_block_84
    (R := [sel]) (hstack := by simp) rd84
  rw [uadd_zero_right fp] at hret
  rw [hfpAfter, hsub] at hret
  rw [show (UInt256.ofNat 32).toNat = 32 from by decide] at hret
  rw [hread] at hret
  exact hret

theorem nestedCallerX_shortarg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
        (UInt256.ofNat 64) = UInt256.ofNat 1 := by
    simpa using solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k0, C0, rd45⟩ := hreach
  have rd491 := nestedCallerBlocks.nestedCaller_block_45
    (R := [nestedCallerSelWord I]) (hstack := by simp) (hvalid := by jump_dest) rd45
  have hlen : UInt256.ofNat 4 + UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4)
      = UInt256.ofNat I.calldata.size :=
    uadd_word_usub_ofNat_word (c := UInt256.ofNat 4)
      (by rw [show (UInt256.ofNat 4).toNat = 4 from by decide]; omega) hsize
  rw [hlen] at rd491
  have rd505 := nestedCallerBlocks.nestedCaller_block_491_fallthrough
    (R := [⟨66⟩, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hcond := by rw [hslt]; decide) rd491
  have rd346 := nestedCallerBlocks.nestedCaller_block_505
    (hstack := by simp) (hvalid := by jump_dest) rd505
  exact nestedCallerBlocks.nestedCaller_block_346 (hstack := by simp) rd346

theorem nestedCallerX_hugearg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (_hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
        (UInt256.ofNat 64) = UInt256.ofNat 1 := by
    simpa using solcDecodeLenCheckHuge_4_64 hbig hsize
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨k0, C0, rd45⟩ := hreach
  have rd491 := nestedCallerBlocks.nestedCaller_block_45
    (R := [nestedCallerSelWord I]) (hstack := by simp) (hvalid := by jump_dest) rd45
  have hlen : UInt256.ofNat 4 + UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4)
      = UInt256.ofNat I.calldata.size :=
    uadd_word_usub_ofNat_word (c := UInt256.ofNat 4)
      (by rw [show (UInt256.ofNat 4).toNat = 4 from by decide]; exact hsz4) hsize
  rw [hlen] at rd491
  have rd505 := nestedCallerBlocks.nestedCaller_block_491_fallthrough
    (R := [⟨66⟩, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hcond := by rw [hslt]; decide) rd491
  have rd346 := nestedCallerBlocks.nestedCaller_block_505
    (hstack := by simp) (hvalid := by jump_dest) rd505
  exact nestedCallerBlocks.nestedCaller_block_346 (hstack := by simp) rd346

theorem nestedCallerX_noncanon {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (runTargetWord I).toNat < EVM.addressModulus) :
    RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hsize : I.calldata.size < UInt256.size := by
    have hlim : 2 ^ 255 + 4 < UInt256.size := by decide
    omega
  obtain ⟨k0, C0, rd407⟩ := nestedCallerX_decode407 hreach hsz68 hsize hbig
  have hclean : UInt256.eq (runTargetWord I) (UInt256.land (runTargetWord I) addrMask) = ⟨0⟩ :=
    ueq_zero_of_ne (fun he => hnc (runTargetWord_canonical he))
  have rd414 := nestedCallerBlocks.nestedCaller_block_407_fallthrough
    (R := [⟨434⟩, runTargetWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨526⟩,
      ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
      nestedCallerSelWord I])
    (hstack := by simp) (hcond := by rw [hclean]; rfl) rd407
  exact nestedCallerBlocks.nestedCaller_block_414 (hstack := by simp) rd414

theorem nestedCallerX_countTooLarge {cA gh bl σ σ₀ A I} {g : UInt256}
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus)
    (hgt : 16 < (runCountWord I).toNat) :
    RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨k0, C0, rd93⟩ := nestedCallerX_decode93 hreach hsz68 hsize hbig hcanon
  have hgtw : UInt256.gt (runCountWord I) (UInt256.ofNat 16) = UInt256.ofNat 1 := by
    simpa using (ugt_one hgt : UInt256.gt (runCountWord I) (⟨16⟩ : UInt256) = ⟨1⟩)
  have rd104 := nestedCallerBlocks.nestedCaller_block_93_fallthrough
    (R := [runTargetWord I, ⟨71⟩, nestedCallerSelWord I]) (hstack := by simp)
    (hcond := by rw [hgtw]; decide) rd93
  exact nestedCallerBlocks.nestedCaller_block_104 (hstack := by simp) rd104

theorem nestedCallerRunBodyReturnBridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {L : Store} {evm' : EVM.State} {last : UInt256}
    (hcode : I.code = nestedCallerBytecode)
    (hd : dispatchMsg nestedCallerContract I.calldata = some runTransition)
    (hdec : decodeCalldataWithMode nestedCallerConfig.abiDecodeMode
      (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes
      I.calldata = some (runArgStore I))
    (hrd : RDret nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc
      (UInt256.toByteArray last))
    (hbody : ExecTransitionBody nestedCallerConfig nestedCallerContract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (runArgStore I)
      runTransition.body
      (.returned { contract := nestedCallerContract, locals := L } evm'
        (some [.int (Int.ofNat last.toNat)])))
    (hCreated : acc.1 = evm'.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evm'.accountMap) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact hrd.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts
    (by
      simpa [runTransition, uint256] using
        returnEquiv_of_encode (uint256ReturnEncoding last))

theorem nestedCallerRunBodyRevertBridge {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode)
    (hd : dispatchMsg nestedCallerContract I.calldata = some runTransition)
    (hdec : decodeCalldataWithMode nestedCallerConfig.abiDecodeMode
      (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes
      I.calldata = some (runArgStore I))
    (hrd : RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hbody : ExecTransitionBody nestedCallerConfig nestedCallerContract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (runArgStore I)
      runTransition.body .reverted) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact hrd.reEquivExecutionRevert hcode hd hdec hbody

theorem nestedCallerRunBodyFromCarryLoop {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hd : dispatchMsg nestedCallerContract I.calldata = some runTransition)
    (hdec : decodeCalldataWithMode nestedCallerConfig.abiDecodeMode
      (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes
      I.calldata = some (runArgStore I))
    (hle : (runCountWord I).toNat ≤ 16)
    (hloop :
      (∃ a : RunCarry I, ∃ L evm' k C,
        ExecForLoop nestedCallerConfig
          { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody
          (.ok { contract := nestedCallerContract, locals := L } evm') ∧
        runCarryDone I (runCountWord I) a L evm' ∧
        RD nestedCallerBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨71⟩
          [a.last, nestedCallerSelWord I] a.mem a.aw a.rdata a.acc k C) ∨
      (ExecForLoop nestedCallerConfig
          { contract := nestedCallerContract, locals := runLoopStore I ⟨0⟩ ⟨0⟩ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (.binary .lt (.var "i") (.var "count")) loopPost loopBody .reverted ∧
        RDrev nestedCallerBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hloop with hok | hrev
  · rcases hok with ⟨a, L, evm', k, C, hfor, hDone, rd71⟩
    rcases hDone with ⟨hlast, _hidx, _henv, hCreated, hAccounts⟩
    have hrdRet : RDret nestedCallerBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) a.acc
        (UInt256.toByteArray a.last) :=
      nestedCallerX_returnWord rd71 a.freePtr (a.returnFreePtr_value a.last) a.returnSub
        (a.returnRead_value a.last)
    have hbody :
        ExecTransitionBody nestedCallerConfig nestedCallerContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (runArgStore I)
          runTransition.body
          (.returned { contract := nestedCallerContract, locals := L } evm'
            (some [.int (Int.ofNat a.last.toNat)])) :=
      nestedCallerRunBodyFromLoop
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evm' I L a.last
        (by simp only [initState]; exact hwv) hle hfor hlast
    exact nestedCallerRunBodyReturnBridge hcode hd hdec hrdRet hbody hCreated hAccounts
  · rcases hrev with ⟨hfor, hrdRev⟩
    have hbody :
        ExecTransitionBody nestedCallerConfig nestedCallerContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (runArgStore I)
          runTransition.body .reverted :=
      nestedCallerRunBodyLoopRevert
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv) hle hfor
    exact nestedCallerRunBodyRevertBridge hcode hd hdec hrdRev hbody

theorem nestedCallerRunBodyValid {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : (runSelector == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (runTargetWord I).toNat < EVM.addressModulus)
    (hle : (runCountWord I).toNat ≤ 16)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd : dispatchMsg nestedCallerContract I.calldata = some runTransition := by
    rw [nestedCallerDispatch.eq, if_pos hsel]
  have hdec := nestedCallerDecode_run hsz68 hbig hcanon
  obtain ⟨k116, C116, rd116⟩ := nestedCallerX_loopEntry hreach hsz68 hsize hbig hcanon hle
  let a0 := initialRunCarry I cA σ_evm
  have hInv0 := initialRunCarry_inv (cA := cA) (gh := gh) (bl := bl)
    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hAccounts
  have hloop := nestedCallerRunLoop_from_carry_body_or_revert
    (I := I) (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    (count := runCountWord I) (target := runTargetWord I) (sel := nestedCallerSelWord I)
    (by
      intro v a L evm hInv k C rd125
      obtain ⟨gasWord, k195, C195, rd195⟩ := nestedCallerX_body_toGas rd125
      by_cases hgasLt : gasWord.toNat < 1000
      · exact Or.inr (Or.inr
          (nestedCallerCarryBodyLowGasBranch hInv rd195 hgasLt))
      · have hgas : 1000 ≤ gasWord.toNat := by omega
        obtain ⟨callGas, k285, C285, rd285⟩ :=
          nestedCallerCarryHighGasToCallCursor hInv rd195 hgas
        by_cases hdepth : I.depth.val < 1024
        · have htgt : EVM.address (runTarget I) =
              AccountAddress.ofUInt256 (UInt256.land addrMask (runTargetWord I)) := by
            simpa [runTarget] using (nestedCallerTarget_eq (I := I) hcanon)
          obtain ⟨cA', σ', z, o, σ'_solm, A'_solm, k286, C286, hcall, hacc,
            hosz, ho138, rd286⟩ :=
            nestedCallerCarryCallMade hInv hperm hdepth htgt rd285
          cases z
          · simp only [Bool.false_eq_true, if_false] at hcall rd286
            exact Or.inl
              (nestedCallerCarryCallFailureRevertBranch hInv hgas hcall rd286)
          · simp only [if_true] at hcall rd286
            by_cases ho32 : 32 ≤ o.size
            · have ho255 : o.size < (2 : Nat) ^ 255 := by
                have hlim : (2 : Nat) ^ 138 < 2 ^ 255 := by norm_num
                exact lt_trans ho138 hlim
              let value : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
              have hvalueNat :
                  value.toNat = fromByteArrayBigEndian (o.extract 0 32) := by
                dsimp [value]
                exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt ho32)
              have hdecValue :
                  nestedCallerConfig.externalABI.decode? "probe" o =
                    some [.int (Int.ofNat value.toNat)] := by
                have hdecRaw := nestedCallerDecodeReturn_uint256_ok
                  (returndata := o) ho32 ho255
                simpa [hvalueNat] using hdecRaw
              have hbase :
                  memLoad (UInt256.ofNat 64) a.callOutputAw (a.callReturnMem o) = a.fp :=
                a.callReturnMem_mload64 o hosz
              have hsltOk :
                  UInt256.slt (UInt256.sub (a.fp + UInt256.ofNat o.size) a.fp)
                    (UInt256.ofNat 32) = ⟨0⟩ := by
                have hslt := solcReturnStaticLenCheckOk
                  (base := a.fp.toNat) (len := o.size) (words := 1)
                  (by simpa using ho32) ho255 a.fp.val.isLt
                  (a.fp_add_return_size_lt_of_inv hInv hle ho138)
                simpa [show 32 * 1 = 32 by norm_num, u256_ofNat_toNat a.fp] using hslt
              have hok :
                  UInt256.isZero
                    (UInt256.slt (UInt256.sub (a.fp + UInt256.ofNat o.size) a.fp)
                      (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
                rw [hsltOk]
                decide
              have hload :
                  memLoad a.fp a.postReadAw (a.postFreePtrMem o) = value := by
                simpa [value] using a.postFreePtrMem_mload_old_fp o ho32 hosz
              by_cases hz : value.toNat = 0
              · have hvalue0 : value = (⟨0⟩ : UInt256) := uint256_toNat_eq_zero hz
                have hdec0 :
                    nestedCallerConfig.externalABI.decode? "probe" o = some [.int 0] := by
                  simpa [hz] using hdecValue
                have hload0 :
                    memLoad a.fp a.postReadAw (a.postFreePtrMem o) = (⟨0⟩ : UInt256) := by
                  simpa [hvalue0] using hload
                obtain ⟨k116', C116', hbody, rd116'⟩ :=
                  nestedCallerCarryCallSuccessZeroBranch hInv hgas hcall hdec0
                    (by
                      simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                        RunCarry.callOutputAw] using hbase)
                    hok
                    (by
                      simpa [RunCarry.postReadAw, RunCarry.postFreePtrMem,
                        RunCarry.postFreePtr, retAligned, RunCarry.callReturnMem,
                        RunCarry.callMem, callOutLen] using hload0)
                    (by
                      simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                        RunCarry.callOutputAw] using rd286)
                have hshape := runCarryInv_shape hInv
                rcases hshape with
                  ⟨_htargetL, _hcountL, hiL, _hlastL, hcountEq, hvariant, _hidxLe⟩
                have hsmall : a.idx.toNat + 1 < UInt256.size := by
                  rw [hcountEq] at hvariant
                  have hcountSmall : (runCountWord I).toNat < UInt256.size :=
                    (runCountWord I).val.isLt
                  omega
                have hiPost :
                    (L.insert "value" (.int 0)).get? "i" =
                      some (.int (Int.ofNat a.idx.toNat)) := by
                  rw [store_get_ne _ _ (by decide), hiL]
                have hpost := nestedCallerLoopPostAdd1
                  ({ evm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' })
                  (L.insert "value" (.int 0)) a.idx hiPost hsmall
                let a' := a.postCallNext (UInt256.ofNat 1 + a.idx) a.last o cA' σ'
                  (a.postFreePtr_min_of_inv hInv hle ho138)
                  (a.postFreePtr_window_of_inv hInv hle ho138)
                  (a.postFreePtr_bound_next_of_inv hInv hle ho138)
                have hInvNext :
                    runCarryInv I
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      (runCountWord I) v a'
                      ((L.insert "value" (.int 0)).insert "i"
                        (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))))
                      { evm with
                          accountMap := σ'_solm, substate := A'_solm,
                          createdAccounts := cA' } := by
                  simpa [a'] using runCarryInv_postCallZeroNext hInv hle ho138 hacc
                exact Or.inr (Or.inr
                  ⟨a', L.insert "value" (.int 0),
                    { evm with
                        accountMap := σ'_solm, substate := A'_solm,
                        createdAccounts := cA' },
                    (L.insert "value" (.int 0)).insert "i"
                      (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))),
                    { evm with
                        accountMap := σ'_solm, substate := A'_solm,
                        createdAccounts := cA' },
                    k116', C116', Or.inr hbody, hpost, hInvNext,
                    by
                      simpa [a', RunCarry.stack, RunCarry.postCallNext,
                        RunCarry.postFreePtrMem, RunCarry.postFreePtr, retAligned,
                        RunCarry.postAw, RunCarry.postReadAw, RunCarry.callReturnMem,
                        RunCarry.callMem, callOutLen] using rd116'⟩)
              · by_cases hone : value.toNat = 1
                · have hvalue1 : value = UInt256.ofNat 1 := by
                    apply u256_inj
                    rw [hone]
                    rfl
                  have hdec1 :
                      nestedCallerConfig.externalABI.decode? "probe" o = some [.int 1] := by
                    simpa [hone] using hdecValue
                  have hload1 :
                      memLoad a.fp a.postReadAw (a.postFreePtrMem o) = UInt256.ofNat 1 := by
                    simpa [hvalue1] using hload
                  obtain ⟨k71', C71', hbody, rd71'⟩ :=
                    nestedCallerCarryCallSuccessOneBranch hInv hgas hcall hdec1
                      (by
                        simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                          RunCarry.callOutputAw] using hbase)
                      hok
                      (by
                        simpa [RunCarry.postReadAw, RunCarry.postFreePtrMem,
                          RunCarry.postFreePtr, retAligned, RunCarry.callReturnMem,
                          RunCarry.callMem, callOutLen] using hload1)
                      (by
                        simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                          RunCarry.callOutputAw] using rd286)
                  let a' := a.postCallNext (runCountWord I) a.last o cA' σ'
                    (a.postFreePtr_min_of_inv hInv hle ho138)
                    (a.postFreePtr_window_of_inv hInv hle ho138)
                    (a.postFreePtr_bound_count_of_inv hInv hle ho138)
                  have hDone :
                      runCarryDone I (runCountWord I) a' (L.insert "value" (.int 1))
                        { evm with
                            accountMap := σ'_solm, substate := A'_solm,
                            createdAccounts := cA' } := by
                    simpa [a'] using runCarryDone_postCallBreak hInv hle ho138 hacc
                  exact Or.inr (Or.inl
                    ⟨a', L.insert "value" (.int 1),
                      { evm with
                          accountMap := σ'_solm, substate := A'_solm,
                          createdAccounts := cA' },
                      k71', C71', hbody, hDone,
                      by
                        simpa [a', RunCarry.postCallNext, RunCarry.postFreePtrMem,
                          RunCarry.postFreePtr, retAligned, RunCarry.postAw,
                          RunCarry.postReadAw, RunCarry.callReturnMem, RunCarry.callMem,
                          callOutLen] using rd71'⟩)
                · have hdecOther :
                      nestedCallerConfig.externalABI.decode? "probe" o =
                        some [.int (Int.ofNat value.toNat)] := hdecValue
                  obtain ⟨k116', C116', hbody, rd116'⟩ :=
                    nestedCallerCarryCallSuccessOtherBranch hInv hgas hcall hdecOther
                      hz hone
                      (by
                        simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                          RunCarry.callOutputAw] using hbase)
                      hok
                      (by
                        simpa [RunCarry.postReadAw, RunCarry.postFreePtrMem,
                          RunCarry.postFreePtr, retAligned, RunCarry.callReturnMem,
                          RunCarry.callMem, callOutLen] using hload)
                      (by
                        simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                          RunCarry.callOutputAw] using rd286)
                  have hshape := runCarryInv_shape hInv
                  rcases hshape with
                    ⟨_htargetL, _hcountL, hiL, _hlastL, hcountEq, hvariant, _hidxLe⟩
                  have hsmall : a.idx.toNat + 1 < UInt256.size := by
                    rw [hcountEq] at hvariant
                    have hcountSmall : (runCountWord I).toNat < UInt256.size :=
                      (runCountWord I).val.isLt
                    omega
                  have hiPost :
                      (((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
                        (.int (Int.ofNat value.toNat))).get? "i" =
                          some (.int (Int.ofNat a.idx.toNat))) := by
                    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hiL]
                  have hpost := nestedCallerLoopPostAdd1
                    ({ evm with
                        accountMap := σ'_solm, substate := A'_solm,
                        createdAccounts := cA' })
                    ((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
                      (.int (Int.ofNat value.toNat)))
                    a.idx hiPost hsmall
                  let a' := a.postCallNext (UInt256.ofNat 1 + a.idx) value o cA' σ'
                    (a.postFreePtr_min_of_inv hInv hle ho138)
                    (a.postFreePtr_window_of_inv hInv hle ho138)
                    (a.postFreePtr_bound_next_of_inv hInv hle ho138)
                  have hInvNext :
                      runCarryInv I
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                        (runCountWord I) v a'
                        (((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
                          (.int (Int.ofNat value.toNat))).insert "i"
                            (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat))))
                        { evm with
                            accountMap := σ'_solm, substate := A'_solm,
                            createdAccounts := cA' } := by
                    simpa [a'] using runCarryInv_postCallOtherNext hInv hle ho138 hacc
                  exact Or.inr (Or.inr
                    ⟨a',
                      (L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
                        (.int (Int.ofNat value.toNat)),
                      { evm with
                          accountMap := σ'_solm, substate := A'_solm,
                          createdAccounts := cA' },
                      (((L.insert "value" (.int (Int.ofNat value.toNat))).insert "last"
                        (.int (Int.ofNat value.toNat))).insert "i"
                          (.int (Int.ofNat ((UInt256.ofNat 1 + a.idx).toNat)))),
                      { evm with
                          accountMap := σ'_solm, substate := A'_solm,
                          createdAccounts := cA' },
                      k116', C116', Or.inl hbody, hpost, hInvNext,
                      by
                        simpa [a', RunCarry.stack, RunCarry.postCallNext,
                          RunCarry.postFreePtrMem, RunCarry.postFreePtr, retAligned,
                          RunCarry.postAw, RunCarry.postReadAw, RunCarry.callReturnMem,
                          RunCarry.callMem, callOutLen] using rd116'⟩)
            · have hshort : o.size < 32 := Nat.lt_of_not_ge ho32
              have hdecn := nestedCallerDecodeReturn_uint256_none_short
                (returndata := o) hshort
              have hbase :
                  memLoad (UInt256.ofNat 64) a.callOutputAw (a.callReturnMem o) = a.fp :=
                a.callReturnMem_mload64 o hosz
              have hsltBad :
                  UInt256.slt (UInt256.sub (a.fp + UInt256.ofNat o.size) a.fp)
                    (UInt256.ofNat 32) = ⟨1⟩ := by
                have hslt := solcReturnStaticLenCheckShort
                  (base := a.fp.toNat) (len := o.size) (words := 1)
                  (by simpa using hshort) a.fp.val.isLt
                  (a.fp_add_return_size_lt_of_inv hInv hle ho138)
                  (by norm_num)
                simpa [show 32 * 1 = 32 by norm_num, u256_ofNat_toNat a.fp] using hslt
              have hbad :
                  UInt256.isZero
                    (UInt256.slt (UInt256.sub (a.fp + UInt256.ofNat o.size) a.fp)
                      (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
                rw [hsltBad]
                decide
              exact Or.inl
                (nestedCallerCarryCallDecodeRevertBranch hInv hgas hcall hdecn
                  (by
                    simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                      RunCarry.callOutputAw] using hbase)
                  hbad
                  (by
                    simpa [RunCarry.callReturnMem, RunCarry.callMem, callOutLen,
                      RunCarry.callOutputAw] using rd286))
        · have hdepthEq : I.depth = 1024 := by
            apply Fin.ext
            have hlt := I.depth.isLt
            omega
          exact Or.inl
            (nestedCallerCarryCallDepthLimitRevert hInv hgas hdepthEq rd285))
    (runCountWord I).toNat a0 (runLoopStore I ⟨0⟩ ⟨0⟩)
    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) hInv0 k116 C116
    (by simpa [a0, RunCarry.stack] using rd116)
  exact nestedCallerRunBodyFromCarryLoop hcode hwv hd hdec hle hloop

/-- `run(address,uint256)` body obligation, entered after the dispatcher has selected the
function and reached pc 45.  The proof is intentionally isolated from `Correct.lean`. -/
theorem nestedCallerRunBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = nestedCallerBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : (runSelector == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD nestedCallerBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨45⟩
      [nestedCallerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd : dispatchMsg nestedCallerContract I.calldata = some runTransition := by
    rw [nestedCallerDispatch.eq, if_pos hsel]
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (runTargetWord I).toNat < EVM.addressModulus
      · by_cases hle : (runCountWord I).toNat ≤ 16
        · exact nestedCallerRunBodyValid hcode hsize hperm hwv hsel hreach hsz68 hbig hcanon hle
            hAccounts
        · have hgt : 16 < (runCountWord I).toNat := by omega
          exact (nestedCallerX_countTooLarge hreach hsz68 hsize hbig hcanon hgt)
            |>.reEquivExecutionRevert hcode hd
              (nestedCallerDecode_run hsz68 hbig hcanon)
              (nestedCallerRunBodyCountTooLarge
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hgt)
      · exact (nestedCallerX_noncanon hreach hsz68 hbig hcanon).reEquivDecodingFailed
          hcode hd (nestedCallerDecode_run_none_noncanon hsz68 hbig hcanon)
    · rw [not_lt] at hbig
      exact (nestedCallerX_hugearg hreach hsz68 hsize hbig).reEquivDecodingFailed
        hcode hd (nestedCallerDecode_run_none_huge hbig)
  · have hshort : I.calldata.size < 68 := by omega
    exact (nestedCallerX_shortarg hreach
        (calldata_size_ge_of_selIs I runSelector (by decide) hsel) hsize hshort)
      |>.reEquivDecodingFailed hcode hd
        (nestedCallerDecode_run_none_short
          (calldata_size_ge_of_selIs I runSelector (by decide) hsel) hshort)

end NestedCaller
