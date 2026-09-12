import Benchmarks.Dss.Flapper.Rely
import Benchmarks.Dss.Flapper.RuntimeBlocks_003

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperFileWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperFileDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev flapperFileBegLit : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232)

abbrev flapperFileTtlLit : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234)

abbrev flapperFileTauLit : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232)

abbrev flapperFileLidLit : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234)

@[simp] theorem flapperBytes32Width_eq_abiBytes32Width :
    bytes32Width = abiBytes32Width := by
  rfl

@[simp] theorem flapperFileBegLit_bytes :
    EVM.Word.toBytesBE flapperFileBegLit = [98, 101, 103] ++ zeroPad29 := by
  native_decide

@[simp] theorem flapperFileTtlLit_bytes :
    EVM.Word.toBytesBE flapperFileTtlLit = [116, 116, 108] ++ zeroPad29 := by
  native_decide

@[simp] theorem flapperFileTauLit_bytes :
    EVM.Word.toBytesBE flapperFileTauLit = [116, 97, 117] ++ zeroPad29 := by
  native_decide

@[simp] theorem flapperFileLidLit_bytes :
    EVM.Word.toBytesBE flapperFileLidLit = [108, 105, 100] ++ zeroPad29 := by
  native_decide

theorem flapperUint48Mask_toNat :
    flapperUint48Mask.toNat = 2 ^ 48 - 1 := by
  decide

theorem flapperUint48Mask_mod_eq_land (w : UInt256) :
    w.toNat % 2 ^ 48 = (UInt256.land w flapperUint48Mask).toNat := by
  rw [uland_toNat, flapperUint48Mask_toNat]
  exact (nat_land_mask_eq_mod w.toNat 48).symm

theorem flapperStorageLocStore_uint48_offset0 (evm : EVM.State)
    (slot val : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨0, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land val flapperUint48Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor (UInt256.land val flapperUint48Mask)
          (UInt256.land (UInt256.lnot flapperUint48Mask)
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure,
    Nat.zero_add]
  have htakeLen :
      ((EVM.Word.toBytesLEWithSizeProof
        (UInt256.land val flapperUint48Mask)).1.take 6).length = 6 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof (UInt256.land val flapperUint48Mask)).2]
    norm_num
  have hmaskHigh :
      UInt256.lnot flapperUint48Mask = UInt256.ofNat (2 ^ 256 - 2 ^ 48) := by
    native_decide
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  have hlow : (UInt256.land val flapperUint48Mask).toNat < 2 ^ 48 :=
    flapperUint48Word_lt val
  have hq : old.toNat / 2 ^ 48 < 2 ^ 208 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 48 * 2 ^ 208 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    exact old.val.isLt
  have hsumlt :
      (UInt256.land val flapperUint48Mask).toNat +
          old.toNat / 2 ^ 48 * 2 ^ 48 < UInt256.size := by
    have hlowle :
        (UInt256.land val flapperUint48Mask).toNat ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 48 ≤ 2 ^ 208 - 1 :=
      Nat.le_pred_of_lt hq
    have hqterm :
        old.toNat / 2 ^ 48 * 2 ^ 48 ≤ (2 ^ 208 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 48 - 1) + (2 ^ 208 - 1) * 2 ^ 48 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  congr 2
  apply u256_inj
  change fromBytes'
      (List.take 0 (EVM.Word.toBytesLEWithSizeProof old).1 ++
        List.take 6 (EVM.Word.toBytesLEWithSizeProof
          (UInt256.land val flapperUint48Mask)).1 ++
        List.drop 6 (EVM.Word.toBytesLEWithSizeProof old).1) =
      ((UInt256.land val flapperUint48Mask).lor
        (flapperUint48Mask.lnot.land old)).toNat
  rw [List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask _ 6 (by decide),
    fromBytes'_drop_wordLE, htakeLen]
  rw [show 2 ^ (8 * 6) = 2 ^ 48 by norm_num]
  rw [show 256 ^ 6 = 2 ^ 48 by norm_num]
  rw [u256_lor_toNat, hmaskHigh, u256_land_high_mask_toNat old 48 (by norm_num)]
  rw [nat_lor_shift_add (UInt256.land val flapperUint48Mask).toNat
    (old.toNat / 2 ^ 48) 48 hlow]
  rw [Nat.mod_eq_of_lt hsumlt]
  rw [show UInt256.ofNat (2 ^ 48 - 1) = flapperUint48Mask by native_decide]
  rw [u256_land_comm val flapperUint48Mask, flapperUint48Mask_clean]
  rw [u256_land_comm flapperUint48Mask val]
  ring_nf

theorem flapperUint48Mask_clean_right_file (w : UInt256) :
    UInt256.land (UInt256.land w flapperUint48Mask) flapperUint48Mask =
      UInt256.land w flapperUint48Mask := by
  rw [u256_land_comm w flapperUint48Mask]
  rw [flapperUint48Mask_clean w]
  rw [u256_land_comm w flapperUint48Mask]

theorem flapperNatLorAssoc (a b c : Nat) :
    Nat.lor (Nat.lor a b) c = Nat.lor a (Nat.lor b c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show ((a ||| b) ||| c).testBit i = (a ||| (b ||| c)).testBit i
  simp [Nat.testBit_or, Bool.or_assoc]

theorem flapperNatLandClearMiddle48 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 48 - 1 + (2 ^ 256 - 2 ^ 96)) =
      n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96 := by
  have hmaskLor :
      (2 : Nat) ^ 48 - 1 + (2 ^ 256 - 2 ^ 96) =
        Nat.lor (2 ^ 48 - 1) ((2 ^ 160 - 1) * 2 ^ 96) := by
    rw [nat_lor_shift_add (2 ^ 48 - 1) (2 ^ 160 - 1) 96]
    · norm_num [Nat.pow_add]
    · norm_num
  have htargetLor :
      n % 2 ^ 48 + n / 2 ^ 96 * 2 ^ 96 =
        Nat.lor (n % 2 ^ 48) (n / 2 ^ 96 * 2 ^ 96) := by
    rw [nat_lor_shift_add (n % 2 ^ 48) (n / 2 ^ 96) 96]
    exact Nat.lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48))
      (by norm_num : 2 ^ 48 < 2 ^ 96)
  rw [hmaskLor, htargetLor]
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& ((2 ^ 48 - 1) ||| ((2 ^ 160 - 1) * 2 ^ 96))).testBit i =
    ((n % 2 ^ 48) ||| (n / 2 ^ 96 * 2 ^ 96)).testBit i
  rw [Nat.testBit_and]
  rw [Nat.testBit_or]
  rw [Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_two_pow_sub_one]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi48 : i < 48
  · have hi96 : i < 96 := by omega
    simp [hi48, hi96]
  · by_cases hi96 : i < 96
    · have hnot96le : ¬ 96 ≤ i := by omega
      simp [hi48, hnot96le]
    · have h96i : 96 ≤ i := Nat.le_of_not_gt hi96
      by_cases hi256 : i < 256
      · have hsub160 : i - 96 < 160 := by omega
        simp [hi48, h96i, hsub160]
        exact (divPow_testBit n 96 i h96i).symm
      · have hnbit : n.testBit i = false := by
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
            (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (by omega)))
        have hsub160 : ¬ i - 96 < 160 := by omega
        have hq : n / 2 ^ 96 < 2 ^ 160 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
          exact hn
        have hdivbit : (n / 2 ^ 96).testBit (i - 96) = false := by
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hq
            (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (by omega)))
        simp [hi48, h96i, hsub160, hnbit]
        simpa [show 2 ^ 96 = 79228162514264337593543950336 by norm_num] using hdivbit

theorem flapperClearUint48Offset6_toNat (old : UInt256) :
    (UInt256.land
        (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680)) old).toNat =
      old.toNat % 2 ^ 48 + old.toNat / 2 ^ 96 * 2 ^ 96 := by
  have hmask :
      UInt256.lnot (UInt256.ofNat 79228162514264056118567239680) =
        UInt256.ofNat ((2 : Nat) ^ 48 - 1 + (2 ^ 256 - 2 ^ 96)) := by
    native_decide
  rw [hmask, u256_land_toNat]
  have hmaskLt : (2 : Nat) ^ 48 - 1 + (2 ^ 256 - 2 ^ 96) < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  rw [ulit_toNat' _ hmaskLt]
  rw [nat_land_comm]
  rw [flapperNatLandClearMiddle48 old.toNat old.val.isLt]
  have hq : old.toNat / 2 ^ 96 < 2 ^ 160 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    exact old.val.isLt
  have hsumlt : old.toNat % 2 ^ 48 + old.toNat / 2 ^ 96 * 2 ^ 96 < UInt256.size := by
    have hlowle : old.toNat % 2 ^ 48 ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48))
    have hqle : old.toNat / 2 ^ 96 ≤ 2 ^ 160 - 1 :=
      Nat.le_pred_of_lt hq
    have hqterm :
        old.toNat / 2 ^ 96 * 2 ^ 96 ≤ (2 ^ 160 - 1) * 2 ^ 96 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 48 - 1) + (2 ^ 160 - 1) * 2 ^ 96 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hsumlt]

theorem flapperStorageLocStore_uint48_offset6 (evm : EVM.State)
    (slot val : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨6, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land val flapperUint48Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.mul (UInt256.land val flapperUint48Mask)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
          (UInt256.land
            (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let low := UInt256.land val flapperUint48Mask
  have htakeOldLen :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have htakeLowLen :
      ((EVM.Word.toBytesLEWithSizeProof low).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof low).2]
    norm_num
  have hlowLt : low.toNat < 2 ^ 48 := by
    simpa [low] using flapperUint48Word_lt val
  have hlowClean : UInt256.land low flapperUint48Mask = low := by
    simpa [low] using flapperUint48Mask_clean_right_file val
  have hmulLt : low.toNat * 2 ^ 48 < UInt256.size := by
    calc
      low.toNat * 2 ^ 48 < 2 ^ 48 * 2 ^ 48 :=
        Nat.mul_lt_mul_of_pos_right hlowLt (by norm_num)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  have hq : old.toNat / 2 ^ 96 < 2 ^ 160 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 96 * 2 ^ 160 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    exact old.val.isLt
  have hsumlt :
      old.toNat % 2 ^ 48 + low.toNat * 2 ^ 48 +
          old.toNat / 2 ^ 96 * 2 ^ 96 < UInt256.size := by
    have holdLowle : old.toNat % 2 ^ 48 ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48))
    have hlowle : low.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hqle : old.toNat / 2 ^ 96 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hq
    have hlowterm : low.toNat * 2 ^ 48 ≤ (2 ^ 48 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hlowle
    have hqterm :
        old.toNat / 2 ^ 96 * 2 ^ 96 ≤ (2 ^ 160 - 1) * 2 ^ 96 :=
      Nat.mul_le_mul_right _ hqle
    have hmax :
        (2 ^ 48 - 1) + (2 ^ 48 - 1) * 2 ^ 48 +
            (2 ^ 160 - 1) * 2 ^ 96 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have holdLowLt : old.toNat % 2 ^ 48 < 2 ^ 48 :=
    Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48)
  have holdLowLt96 : old.toNat % 2 ^ 48 < 2 ^ 96 :=
    Nat.lt_trans holdLowLt (by norm_num : 2 ^ 48 < 2 ^ 96)
  have hpreserveLor :
      old.toNat % 2 ^ 48 + old.toNat / 2 ^ 96 * 2 ^ 96 =
        Nat.lor (old.toNat % 2 ^ 48) (old.toNat / 2 ^ 96 * 2 ^ 96) := by
    rw [nat_lor_shift_add (old.toNat % 2 ^ 48) (old.toNat / 2 ^ 96) 96
      holdLowLt96]
  have htwoFieldLt :
      old.toNat % 2 ^ 48 + low.toNat * 2 ^ 48 < 2 ^ 96 := by
    have holdLowLe : old.toNat % 2 ^ 48 ≤ 2 ^ 48 - 1 :=
      Nat.le_pred_of_lt holdLowLt
    have hlowLe : low.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hlowTerm : low.toNat * 2 ^ 48 ≤ (2 ^ 48 - 1) * 2 ^ 48 :=
      Nat.mul_le_mul_right _ hlowLe
    have hmax : (2 ^ 48 - 1) + (2 ^ 48 - 1) * 2 ^ 48 < 2 ^ 96 := by
      norm_num [Nat.pow_add]
    omega
  congr 2
  apply u256_inj
  change fromBytes'
      (List.take 6 (EVM.Word.toBytesLEWithSizeProof old).1 ++
        List.take 6 (EVM.Word.toBytesLEWithSizeProof low).1 ++
        List.drop 12 (EVM.Word.toBytesLEWithSizeProof old).1) =
      (UInt256.lor
          (UInt256.mul low
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
          (UInt256.land
            (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680)) old)).toNat
  rw [fromBytes'_append, fromBytes'_append,
    fromBytes'_take_wordLE_land_mask old 6 (by decide),
    fromBytes'_take_wordLE_land_mask low 6 (by decide),
    fromBytes'_drop_wordLE, List.length_append, htakeOldLen, htakeLowLen]
  rw [show 2 ^ (8 * 6) = 2 ^ 48 by norm_num]
  rw [show 2 ^ (8 * (6 + 6)) = 2 ^ 96 by norm_num]
  rw [show 256 ^ 12 = 2 ^ 96 by norm_num]
  rw [show UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48) =
      UInt256.ofNat (2 ^ 48) by native_decide]
  rw [u256_lor_toNat, u256_mul_toNat, flapperClearUint48Offset6_toNat]
  rw [show (UInt256.ofNat (2 ^ 48)).toNat = 2 ^ 48 by native_decide]
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [show UInt256.ofNat (2 ^ 48 - 1) = flapperUint48Mask by native_decide]
  rw [← flapperUint48Mask_mod_eq_land old, hlowClean]
  rw [hpreserveLor]
  rw [← flapperNatLorAssoc]
  rw [nat_lor_comm (low.toNat * 2 ^ 48) (old.toNat % 2 ^ 48)]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 48) low.toNat 48 holdLowLt]
  rw [nat_lor_shift_add
    (old.toNat % 2 ^ 48 + low.toNat * 2 ^ 48)
    (old.toNat / 2 ^ 96) 96 htwoFieldLt]
  rw [Nat.mod_eq_of_lt hsumlt]
  rw [flapperUint48Mask_mod_eq_land old]
  simp [low]
  ring_nf

theorem flapperFileAuthHashMem_eq (I : ExecutionEnv) (mem : ByteArray) :
    flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory
        (ee := I) (mem := mem) =
      twoWordHashMem (flapperRelyAuthWord I) (UInt256.ofNat 0) mem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory,
    flapperRelyAuthWord, twoWordHashMem, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperFileAuthHashSlot (I : ExecutionEnv) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory
          (ee := I) (mem := mem)) =
      flapperRelyAuthSlot I := by
  rw [flapperFileAuthHashMem_eq]
  simpa [flapperRelyAuthSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyAuthWord I)
      (UInt256.ofNat 0) mem

theorem flapperFileCondHit (lit what : UInt256) (h : what = lit) :
    UInt256.isZero (UInt256.eq lit what) = UInt256.ofNat 0 := by
  rw [h]
  rw [u256_eq_refl]
  decide

theorem flapperFileCondMiss (lit what : UInt256) (h : what ≠ lit) :
    UInt256.isZero (UInt256.eq lit what) ≠ UInt256.ofNat 0 := by
  have heq0 : UInt256.eq lit what = UInt256.ofNat 0 := by
    exact u256_eq_of_ne (by
      intro heq
      exact h heq.symm)
  rw [heq0]
  decide

theorem flapperX_file_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1225⟩
      [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd362⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 64) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 64)
      (by simpa using hsz68) hsize
  have hcondLen :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 64)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd384 := flapperRuntimeBlocks.flapperRuntime_block_362_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd362
  have rd1225 := flapperRuntimeBlocks.flapperRuntime_block_384
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd384
  exact ⟨_, _, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_384_stack,
      flapperFileDataWord, flapperFileWhatWord, calldataWord,
      show ((UInt256.ofNat 32) + (UInt256.ofNat 4)).toNat = 36 by decide,
      show (UInt256.ofNat 4).toNat = 4 by decide] using rd1225⟩

theorem flapperX_file_after_auth_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1318⟩
      [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel]
      (flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory
        (ee := I) (mem := solcFreePtrMem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1225⟩ := flapperX_file_decode_ok
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
          flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory
            (ee := I) (mem := solcFreePtrMem) by rfl]
    rw [flapperFileAuthHashSlot, hauth]
    decide
  obtain ⟨_, _, _, rd1318⟩ := flapperRuntimeBlocks.flapperRuntime_block_1225_taken_packed
    (R := [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondAuth (by jump_dest) rd1225
  exact ⟨_, _, _, rd1318⟩

theorem flapperX_file_auth_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) ≠ UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1225⟩ := flapperX_file_decode_ok
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
          flapperRuntimeBlocks.flapperRuntime_block_1225_taken_memory
            (ee := I) (mem := solcFreePtrMem) by rfl]
    rw [flapperFileAuthHashSlot]
    exact u256_eq_of_ne (by
      intro h
      exact hauth h.symm)
  obtain ⟨_, _, _, rd1249⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1225_fallthrough_packed
      (R := [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondAuth rd1225
  exact flapperRuntimeBlocks.flapperRuntime_block_1249
    (R := [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd1249

theorem flapperX_file_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd362⟩ := hreach
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
  have rd380 := flapperRuntimeBlocks.flapperRuntime_block_362_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd362
  exact flapperRuntimeBlocks.flapperRuntime_block_380
    (R := flapperRuntimeBlocks.flapperRuntime_block_362_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_362_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd380

theorem flapperX_file_beg_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hwhat : flapperFileWhatWord I = flapperFileBegLit)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (UInt256.ofNat 4) (flapperFileDataWord I))
      ByteArray.empty := by
  obtain ⟨_, _, _, rd1318⟩ := flapperX_file_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondBeg :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) = UInt256.ofNat 0 := by
    simpa [flapperFileBegLit] using
      flapperFileCondHit flapperFileBegLit (flapperFileWhatWord I) hwhat
  have rd1333 := flapperRuntimeBlocks.flapperRuntime_block_1318_fallthrough
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondBeg rd1318
  obtain ⟨_, _, rd1543⟩ := flapperRuntimeBlocks.flapperRuntime_block_1333
    (x0 := flapperFileDataWord I) (R := [flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd1333
  have rd360 := flapperRuntimeBlocks.flapperRuntime_block_1543
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (x2 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd1543
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel])
    (by simp only [List.length_singleton]; omega)
    rd360

theorem flapperX_file_ttl_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hbeg : flapperFileWhatWord I ≠ flapperFileBegLit)
    (hwhat : flapperFileWhatWord I = flapperFileTtlLit)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (UInt256.ofNat 5)
        (UInt256.lor (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
          (UInt256.land (UInt256.lnot flapperUint48Mask)
            (storageRead I.codeOwner σ (UInt256.ofNat 5)))))
      ByteArray.empty := by
  obtain ⟨_, _, _, rd1318⟩ := flapperX_file_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondBeg :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileBegLit] using
      flapperFileCondMiss flapperFileBegLit (flapperFileWhatWord I) hbeg
  have rd1342 := flapperRuntimeBlocks.flapperRuntime_block_1318_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondBeg (by jump_dest) rd1318
  have hcondTtl :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) = UInt256.ofNat 0 := by
    simpa [flapperFileTtlLit] using
      flapperFileCondHit flapperFileTtlLit (flapperFileWhatWord I) hwhat
  have rd1357 := flapperRuntimeBlocks.flapperRuntime_block_1342_fallthrough
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTtl rd1342
  obtain ⟨_, _, rd1543⟩ := flapperRuntimeBlocks.flapperRuntime_block_1357
    (x0 := flapperFileDataWord I) (R := [flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd1357
  have rd360 := flapperRuntimeBlocks.flapperRuntime_block_1543
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (x2 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd1543
  simpa [flapperUint48Mask] using
    flapperRuntimeBlocks.flapperRuntime_block_360
      (R := [sel])
      (by simp only [List.length_singleton]; omega)
      rd360

theorem flapperX_file_tau_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hbeg : flapperFileWhatWord I ≠ flapperFileBegLit)
    (httl : flapperFileWhatWord I ≠ flapperFileTtlLit)
    (hwhat : flapperFileWhatWord I = flapperFileTauLit)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (UInt256.ofNat 5)
        (UInt256.lor
          (UInt256.mul (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
            flapperUint48Shift)
          (UInt256.land
            (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
            (storageRead I.codeOwner σ (UInt256.ofNat 5)))))
      ByteArray.empty := by
  obtain ⟨_, _, _, rd1318⟩ := flapperX_file_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondBeg :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileBegLit] using
      flapperFileCondMiss flapperFileBegLit (flapperFileWhatWord I) hbeg
  have rd1342 := flapperRuntimeBlocks.flapperRuntime_block_1318_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondBeg (by jump_dest) rd1318
  have hcondTtl :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileTtlLit] using
      flapperFileCondMiss flapperFileTtlLit (flapperFileWhatWord I) httl
  have rd1386 := flapperRuntimeBlocks.flapperRuntime_block_1342_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTtl (by jump_dest) rd1342
  have hcondTau :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) = UInt256.ofNat 0 := by
    simpa [flapperFileTauLit] using
      flapperFileCondHit flapperFileTauLit (flapperFileWhatWord I) hwhat
  have rd1401 := flapperRuntimeBlocks.flapperRuntime_block_1386_fallthrough
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTau rd1386
  obtain ⟨_, _, rd1543⟩ := flapperRuntimeBlocks.flapperRuntime_block_1401
    (x0 := flapperFileDataWord I) (R := [flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd1401
  have rd360 := flapperRuntimeBlocks.flapperRuntime_block_1543
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (x2 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd1543
  simpa [flapperUint48Mask, flapperUint48Shift] using
    flapperRuntimeBlocks.flapperRuntime_block_360
      (R := [sel])
      (by simp only [List.length_singleton]; omega)
      rd360

theorem flapperX_file_lid_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hbeg : flapperFileWhatWord I ≠ flapperFileBegLit)
    (httl : flapperFileWhatWord I ≠ flapperFileTtlLit)
    (htau : flapperFileWhatWord I ≠ flapperFileTauLit)
    (hwhat : flapperFileWhatWord I = flapperFileLidLit)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (UInt256.ofNat 8) (flapperFileDataWord I))
      ByteArray.empty := by
  obtain ⟨_, _, _, rd1318⟩ := flapperX_file_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondBeg :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileBegLit] using
      flapperFileCondMiss flapperFileBegLit (flapperFileWhatWord I) hbeg
  have rd1342 := flapperRuntimeBlocks.flapperRuntime_block_1318_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondBeg (by jump_dest) rd1318
  have hcondTtl :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileTtlLit] using
      flapperFileCondMiss flapperFileTtlLit (flapperFileWhatWord I) httl
  have rd1386 := flapperRuntimeBlocks.flapperRuntime_block_1342_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTtl (by jump_dest) rd1342
  have hcondTau :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileTauLit] using
      flapperFileCondMiss flapperFileTauLit (flapperFileWhatWord I) htau
  have rd1442 := flapperRuntimeBlocks.flapperRuntime_block_1386_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTau (by jump_dest) rd1386
  have hcondLid :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) = UInt256.ofNat 0 := by
    simpa [flapperFileLidLit] using
      flapperFileCondHit flapperFileLidLit (flapperFileWhatWord I) hwhat
  have rd1457 := flapperRuntimeBlocks.flapperRuntime_block_1442_fallthrough
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLid rd1442
  obtain ⟨_, _, rd1543⟩ := flapperRuntimeBlocks.flapperRuntime_block_1457
    (x0 := flapperFileDataWord I) (R := [flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd1457
  have rd360 := flapperRuntimeBlocks.flapperRuntime_block_1543
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (x2 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd1543
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel])
    (by simp only [List.length_singleton]; omega)
    rd360

theorem flapperX_file_unknown_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz68 : 68 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hbeg : flapperFileWhatWord I ≠ flapperFileBegLit)
    (httl : flapperFileWhatWord I ≠ flapperFileTtlLit)
    (htau : flapperFileWhatWord I ≠ flapperFileTauLit)
    (hlid : flapperFileWhatWord I ≠ flapperFileLidLit)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨362⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd1318⟩ := flapperX_file_after_auth_ok
    (g := g) hsize hsz68 hauth hreach
  have hcondBeg :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileBegLit] using
      flapperFileCondMiss flapperFileBegLit (flapperFileWhatWord I) hbeg
  have rd1342 := flapperRuntimeBlocks.flapperRuntime_block_1318_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondBeg (by jump_dest) rd1318
  have hcondTtl :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileTtlLit] using
      flapperFileCondMiss flapperFileTtlLit (flapperFileWhatWord I) httl
  have rd1386 := flapperRuntimeBlocks.flapperRuntime_block_1342_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTtl (by jump_dest) rd1342
  have hcondTau :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileTauLit] using
      flapperFileCondMiss flapperFileTauLit (flapperFileWhatWord I) htau
  have rd1442 := flapperRuntimeBlocks.flapperRuntime_block_1386_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTau (by jump_dest) rd1386
  have hcondLid :
      UInt256.isZero (UInt256.eq
        (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234))
        (flapperFileWhatWord I)) ≠ UInt256.ofNat 0 := by
    simpa [flapperFileLidLit] using
      flapperFileCondMiss flapperFileLidLit (flapperFileWhatWord I) hlid
  have rd1466 := flapperRuntimeBlocks.flapperRuntime_block_1442_taken
    (x0 := flapperFileDataWord I) (x1 := flapperFileWhatWord I)
    (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLid (by jump_dest) rd1442
  exact flapperRuntimeBlocks.flapperRuntime_block_1466
    (R := [flapperFileDataWord I, flapperFileWhatWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd1466

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256,
    isDynamicABIType, staticABIEncodedSize?, decodeABIValue?, readBytes?,
    hlen0, hge32, readWord?, decodeABIWord?, List.take_take, UInt256.toNat]
  rw [Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · exact_mod_cast
      (ABI.bytesToWord (List.take 32 (List.drop 32 bytes))).val.isLt

theorem decodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64
        DecodeMode.legacySolc05 = none := by
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot0 : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256,
      isDynamicABIType, staticABIEncodedSize?, decodeABIValue?, readBytes?,
      hnot0]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256,
      isDynamicABIType, staticABIEncodedSize?, decodeABIValue?, readBytes?,
      htake0, readWord?, hnot]

theorem flapperDecode_file_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata =
      some (((∅ : Store).insert "what"
        (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (flapperFileWhatWord I))))
        |>.insert "data" (.int (Int.ofNat (flapperFileDataWord I).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"]
    [abiBytes32, abiUInt256] I.calldata =
      some (((∅ : Store).insert "what"
        (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (flapperFileWhatWord I))))
        |>.insert "data" (.int (Int.ofNat (flapperFileDataWord I).toNat)))
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
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = flapperFileWhatWord I := by
    simpa [flapperFileWhatWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) = flapperFileDataWord I := by
    simpa [flapperFileDataWord] using
      decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hbytes4 :
      (I.calldata.toList.drop 4).take 32 =
        EVM.Word.toBytesBE (flapperFileWhatWord I) := by
    calc
      (I.calldata.toList.drop 4).take 32 =
          EVM.Word.toBytesBE
            (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)) := by
        exact (toBytesBE_bytesToWord_of_length htake4).symm
      _ = EVM.Word.toBytesBE (flapperFileWhatWord I) := by
        rw [hword4]
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4) htake36']
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, hbytes4, flapperFileWhatWord]
  rw [hword36]

theorem flapperDecode_file_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode
      (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"]
    [abiBytes32, abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := I.calldata.toList.drop 4)
    (by rw [List.length_drop, htlen]; omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 64)]

theorem flapperDispatch_file {cd : ByteArray}
    (hsel : ((⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some fileTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition, denyTransition])
    (post := [fillTransition, gemTransition, kickTransition, kicksTransition,
      lidTransition, liveTransition, relyTransition, tauTransition, tendTransition,
      tickTransition, ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
  · rw [flapperFileSelectorBytes]
    exact hsel

def flapperFileLocals (what data : UInt256) : Store :=
  ((∅ : Store).insert "what"
    (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)))
    |>.insert "data" (.int (Int.ofNat data.toNat))

theorem flapperFileFixedBytesBeq_true
    (what lit : UInt256) (bytes : List UInt8)
    (hwhat : what = lit) (hbytes : EVM.Word.toBytesBE lit = bytes) :
    ((Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)) ==
      Value.fixedBytes bytes32Width bytes) = true := by
  subst what
  simp [hbytes]

theorem flapperFileFixedBytesBeq_false
    (what lit : UInt256) (bytes : List UInt8)
    (hwhat : what ≠ lit) (hbytes : EVM.Word.toBytesBE lit = bytes) :
    ((Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)) ==
      Value.fixedBytes bytes32Width bytes) = false := by
  have hvalueNe :
      Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what) ≠
        Value.fixedBytes bytes32Width bytes := by
    intro hbad
    injection hbad with _ hlist
    apply hwhat
    apply word_toBytesBE_inj
    calc
      EVM.Word.toBytesBE what = bytes := hlist
      _ = EVM.Word.toBytesBE lit := hbytes.symm
  cases hbeq :
      (Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what) ==
        Value.fixedBytes bytes32Width bytes)
  · rfl
  · exact False.elim (hvalueNe (beq_iff_eq.mp hbeq))

theorem flapperFileWhatGuard_true (evm : EVM.State) (what data lit : UInt256)
    (bytes : List UInt8) (hwhat : what = lit) (hbytes : EVM.Word.toBytesBE lit = bytes) :
    evalExpr? config { contract := contract, locals := flapperFileLocals what data } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bytes)) =
      .ok (.bool true) := by
  have hbeq := flapperFileFixedBytesBeq_true what lit bytes hwhat hbytes
  have hgetWhat :
      (flapperFileLocals what data).get? "what" =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)) := by
    rw [flapperFileLocals]
    rw [store_get_ne ((∅ : Store).insert "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)))
      (k := "data") (a := "what") (.int (Int.ofNat data.toNat)) (by decide)]
    exact store_get_self (∅ : Store) "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what))
  simp only [evalExpr?, hgetWhat, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hbeq]

theorem flapperFileWhatGuard_false (evm : EVM.State) (what data lit : UInt256)
    (bytes : List UInt8) (hwhat : what ≠ lit) (hbytes : EVM.Word.toBytesBE lit = bytes) :
    evalExpr? config { contract := contract, locals := flapperFileLocals what data } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bytes)) =
      .ok (.bool false) := by
  have hbeq := flapperFileFixedBytesBeq_false what lit bytes hwhat hbytes
  have hgetWhat :
      (flapperFileLocals what data).get? "what" =
        some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)) := by
    rw [flapperFileLocals]
    rw [store_get_ne ((∅ : Store).insert "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)))
      (k := "data") (a := "what") (.int (Int.ofNat data.toNat)) (by decide)]
    exact store_get_self (∅ : Store) "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what))
  simp only [evalExpr?, hgetWhat, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hbeq]

theorem flapperFileData_eval (evm : EVM.State) (what data : UInt256) :
    evalExpr? config { contract := contract, locals := flapperFileLocals what data } evm
      (.var "data") = .ok (.int (Int.ofNat data.toNat)) := by
  have hgetData :
      (flapperFileLocals what data).get? "data" =
        some (.int (Int.ofNat data.toNat)) := by
    rw [flapperFileLocals]
    exact store_get_self ((∅ : Store).insert "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)))
      "data" (.int (Int.ofNat data.toNat))
  unfold evalExpr?
  change EvalResult.ofOption EvalError.unboundVariable
      ((flapperFileLocals what data).get? "data") =
    .ok (.int (Int.ofNat data.toNat))
  rw [hgetData]
  rfl

theorem flapperFileWrap48_eval (evm : EVM.State) (what data : UInt256) :
    evalExpr? config { contract := contract, locals := flapperFileLocals what data } evm
      (wrap48 (.var "data")) =
      .ok (.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat)) := by
  have hmod :
      (Int.ofNat data.toNat) % uint48Modulus =
        Int.ofNat (UInt256.land data flapperUint48Mask).toNat := by
    rw [uint48Modulus]
    change (Int.ofNat data.toNat) % (Int.ofNat ((2 : Nat) ^ 48)) =
      Int.ofNat (UInt256.land data flapperUint48Mask).toNat
    calc
      (Int.ofNat data.toNat) % (Int.ofNat ((2 : Nat) ^ 48)) =
          Int.ofNat (data.toNat % (2 : Nat) ^ 48) := by
        exact (Int.natCast_emod data.toNat ((2 : Nat) ^ 48)).symm
      _ = Int.ofNat (UInt256.land data flapperUint48Mask).toNat := by
        exact congrArg Int.ofNat (flapperUint48Mask_mod_eq_land data)
  have hgetData :
      (flapperFileLocals what data).get? "data" =
        some (.int (Int.ofNat data.toNat)) := by
    rw [flapperFileLocals]
    exact store_get_self ((∅ : Store).insert "what"
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE what)))
      "data" (.int (Int.ofNat data.toNat))
  have hnonzero : uint48Modulus ≠ 0 := by
    norm_num [uint48Modulus]
  simp only [wrap48, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hgetData]
  change (if uint48Modulus = 0 then EvalResult.revert
    else EvalResult.ok (Value.int (Int.ofNat data.toNat % uint48Modulus))) =
      EvalResult.ok (Value.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat))
  rw [if_neg hnonzero, hmod]

theorem flapperFileAssignBeg (evm : EVM.State) (what data : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperFileLocals what data } evm
      .storage begRef (.int (Int.ofNat data.toNat)) =
      .ok ({ contract := contract, locals := flapperFileLocals what data },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 4) data) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "beg", steps := [] }
  have hbase : locals.get? "beg" = none := by
    simp [locals, flapperFileLocals]
  have her : evalStorageRef config solm evm begRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, begRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er =
      fun _ => some (wordLoc (⟨4⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨4⟩ : UInt256)) (.int (Int.ofNat data.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 4) data) := by
    simpa [wordLoc, uint256Loc, show (⟨4⟩ : UInt256) = UInt256.ofNat 4 by decide] using
      storageLocStore_uint256 evm (⟨4⟩ : UInt256) data
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperFileAssignTtl (evm : EVM.State) (what data : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperFileLocals what data } evm
      .storage ttlRef (.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat)) =
      .ok ({ contract := contract, locals := flapperFileLocals what data },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor (UInt256.land data flapperUint48Mask)
            (UInt256.land (UInt256.lnot flapperUint48Mask)
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "ttl", steps := [] }
  have hbase : locals.get? "ttl" = none := by
    simp [locals, flapperFileLocals]
  have her : evalStorageRef config solm evm ttlRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint48St]
  have hloc : config.storage.layout er =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨0, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm
          (uint48Loc (⟨5⟩ : UInt256) ⟨0, by decide⟩ (by decide))
          (.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor (UInt256.land data flapperUint48Mask)
            (UInt256.land (UInt256.lnot flapperUint48Mask)
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))) := by
    simpa [show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide] using
      flapperStorageLocStore_uint48_offset0 evm (⟨5⟩ : UInt256) data
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperFileAssignTau (evm : EVM.State) (what data : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperFileLocals what data } evm
      .storage tauRef (.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat)) =
      .ok ({ contract := contract, locals := flapperFileLocals what data },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor
            (UInt256.mul (UInt256.land data flapperUint48Mask)
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
            (UInt256.land
              (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "tau", steps := [] }
  have hbase : locals.get? "tau" = none := by
    simp [locals, flapperFileLocals]
  have her : evalStorageRef config solm evm tauRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint48St]
  have hloc : config.storage.layout er =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm
          (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide))
          (.int (Int.ofNat (UInt256.land data flapperUint48Mask).toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor
            (UInt256.mul (UInt256.land data flapperUint48Mask)
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
            (UInt256.land
              (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))) := by
    simpa [show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide] using
      flapperStorageLocStore_uint48_offset6 evm (⟨5⟩ : UInt256) data
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperFileAssignLid (evm : EVM.State) (what data : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperFileLocals what data } evm
      .storage lidRef (.int (Int.ofNat data.toNat)) =
      .ok ({ contract := contract, locals := flapperFileLocals what data },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 8) data) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "lid", steps := [] }
  have hbase : locals.get? "lid" = none := by
    simp [locals, flapperFileLocals]
  have her : evalStorageRef config solm evm lidRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, lidRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er =
      fun _ => some (wordLoc (⟨8⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨8⟩ : UInt256)) (.int (Int.ofNat data.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 8) data) := by
    simpa [wordLoc, uint256Loc, show (⟨8⟩ : UInt256) = UInt256.ofNat 8 by decide] using
      storageLocStore_uint256 evm (⟨8⟩ : UInt256) data
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperFileBodyRevertsAuth (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body .reverted := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguard :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool false) := by
    exact flapperRelyAuthGuard_false evm locals hbaseWards hauth
  exact ExecFuncBody.execBlockRevert <| by
    simpa [fileTransition, nonpayable, auth, locals, solm] using
      nonpayableSecondRequireReverts (cfg := config) (solm := solm) (evm := evm)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest :=
          [ .ite
              (.binary .eq (.var "what") begParamLit)
              [ .assign .storage begRef (.var "data") ]
              [ .ite
                  (.binary .eq (.var "what") ttlParamLit)
                  [ .assign .storage ttlRef (wrap48 (.var "data")) ]
                  [ .ite
                      (.binary .eq (.var "what") tauParamLit)
                      [ .assign .storage tauRef (wrap48 (.var "data")) ]
                      [ .ite
                          (.binary .eq (.var "what") lidParamLit)
                          [ .assign .storage lidRef (.var "data") ]
                          [ .require (.boolLit false) ] ] ] ] ])
        hwv hguard

theorem flapperFileBodyReturnsBeg (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hwhat : what = flapperFileBegLit) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body
      (.returned { contract := contract, locals := flapperFileLocals what data }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 4) data)
        none) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguardAuth :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hguardBeg :
      evalExpr? config solm evm (.binary .eq (.var "what") begParamLit) =
        .ok (.bool true) := by
    simpa [solm, locals, begParamLit] using
      flapperFileWhatGuard_true evm what data flapperFileBegLit
        ([98, 101, 103] ++ zeroPad29) hwhat flapperFileBegLit_bytes
  have hassignBlock :
      ExecBlock config solm evm [ .assign .storage begRef (.var "data") ]
        (.ok solm
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 4) data)) := by
    exact assignStorageBlock
      (flapperFileData_eval evm what data)
      (flapperFileAssignBeg evm what data)
  exact ExecFuncBody.execBlockOK <| by
    simpa [fileTransition, nonpayable, auth, locals, solm] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) <|
          ExecBlock.consNormal (ExecStmt.iteTrue hguardBeg hassignBlock) ExecBlock.nil

theorem flapperFileBodyReturnsTtl (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hbeg : what ≠ flapperFileBegLit)
    (hwhat : what = flapperFileTtlLit) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body
      (.returned { contract := contract, locals := flapperFileLocals what data }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor (UInt256.land data flapperUint48Mask)
            (UInt256.land (UInt256.lnot flapperUint48Mask)
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5)))))
        none) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let evm' :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
      (UInt256.lor (UInt256.land data flapperUint48Mask)
        (UInt256.land (UInt256.lnot flapperUint48Mask)
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguardAuth :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hguardBeg :
      evalExpr? config solm evm (.binary .eq (.var "what") begParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, begParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileBegLit
        ([98, 101, 103] ++ zeroPad29) hbeg flapperFileBegLit_bytes
  have hguardTtl :
      evalExpr? config solm evm (.binary .eq (.var "what") ttlParamLit) =
        .ok (.bool true) := by
    simpa [solm, locals, ttlParamLit] using
      flapperFileWhatGuard_true evm what data flapperFileTtlLit
        ([116, 116, 108] ++ zeroPad29) hwhat flapperFileTtlLit_bytes
  have hassignBlock :
      ExecBlock config solm evm [ .assign .storage ttlRef (wrap48 (.var "data")) ]
        (.ok solm evm') := by
    simpa [evm'] using
      assignStorageBlock
        (flapperFileWrap48_eval evm what data)
        (flapperFileAssignTtl evm what data)
  have helse :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") ttlParamLit)
            [ .assign .storage ttlRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") tauParamLit)
                [ .assign .storage tauRef (wrap48 (.var "data")) ]
                [ .ite
                    (.binary .eq (.var "what") lidParamLit)
                    [ .assign .storage lidRef (.var "data") ]
                    [ .require (.boolLit false) ] ] ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hguardTtl hassignBlock) ExecBlock.nil
  exact ExecFuncBody.execBlockOK <| by
    simpa [fileTransition, nonpayable, auth, locals, solm, evm'] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) <|
          ExecBlock.consNormal (ExecStmt.iteFalse hguardBeg helse) ExecBlock.nil

theorem flapperFileBodyReturnsTau (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hbeg : what ≠ flapperFileBegLit)
    (httl : what ≠ flapperFileTtlLit)
    (hwhat : what = flapperFileTauLit) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body
      (.returned { contract := contract, locals := flapperFileLocals what data }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
          (UInt256.lor
            (UInt256.mul (UInt256.land data flapperUint48Mask)
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
            (UInt256.land
              (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5)))))
        none) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let evm' :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5)
      (UInt256.lor
        (UInt256.mul (UInt256.land data flapperUint48Mask)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
        (UInt256.land
          (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))))
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguardAuth :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hguardBeg :
      evalExpr? config solm evm (.binary .eq (.var "what") begParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, begParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileBegLit
        ([98, 101, 103] ++ zeroPad29) hbeg flapperFileBegLit_bytes
  have hguardTtl :
      evalExpr? config solm evm (.binary .eq (.var "what") ttlParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, ttlParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileTtlLit
        ([116, 116, 108] ++ zeroPad29) httl flapperFileTtlLit_bytes
  have hguardTau :
      evalExpr? config solm evm (.binary .eq (.var "what") tauParamLit) =
        .ok (.bool true) := by
    simpa [solm, locals, tauParamLit] using
      flapperFileWhatGuard_true evm what data flapperFileTauLit
        ([116, 97, 117] ++ zeroPad29) hwhat flapperFileTauLit_bytes
  have hassignBlock :
      ExecBlock config solm evm [ .assign .storage tauRef (wrap48 (.var "data")) ]
        (.ok solm evm') := by
    simpa [evm'] using
      assignStorageBlock
        (flapperFileWrap48_eval evm what data)
        (flapperFileAssignTau evm what data)
  have helseTau :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") tauParamLit)
            [ .assign .storage tauRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") lidParamLit)
                [ .assign .storage lidRef (.var "data") ]
                [ .require (.boolLit false) ] ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hguardTau hassignBlock) ExecBlock.nil
  have helseTtl :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") ttlParamLit)
            [ .assign .storage ttlRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") tauParamLit)
                [ .assign .storage tauRef (wrap48 (.var "data")) ]
                [ .ite
                    (.binary .eq (.var "what") lidParamLit)
                    [ .assign .storage lidRef (.var "data") ]
                    [ .require (.boolLit false) ] ] ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hguardTtl helseTau) ExecBlock.nil
  exact ExecFuncBody.execBlockOK <| by
    simpa [fileTransition, nonpayable, auth, locals, solm, evm'] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) <|
          ExecBlock.consNormal (ExecStmt.iteFalse hguardBeg helseTtl) ExecBlock.nil

theorem flapperFileBodyReturnsLid (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hbeg : what ≠ flapperFileBegLit)
    (httl : what ≠ flapperFileTtlLit)
    (htau : what ≠ flapperFileTauLit)
    (hwhat : what = flapperFileLidLit) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body
      (.returned { contract := contract, locals := flapperFileLocals what data }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 8) data)
        none) := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 8) data
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguardAuth :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hguardBeg :
      evalExpr? config solm evm (.binary .eq (.var "what") begParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, begParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileBegLit
        ([98, 101, 103] ++ zeroPad29) hbeg flapperFileBegLit_bytes
  have hguardTtl :
      evalExpr? config solm evm (.binary .eq (.var "what") ttlParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, ttlParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileTtlLit
        ([116, 116, 108] ++ zeroPad29) httl flapperFileTtlLit_bytes
  have hguardTau :
      evalExpr? config solm evm (.binary .eq (.var "what") tauParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, tauParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileTauLit
        ([116, 97, 117] ++ zeroPad29) htau flapperFileTauLit_bytes
  have hguardLid :
      evalExpr? config solm evm (.binary .eq (.var "what") lidParamLit) =
        .ok (.bool true) := by
    simpa [solm, locals, lidParamLit] using
      flapperFileWhatGuard_true evm what data flapperFileLidLit
        ([108, 105, 100] ++ zeroPad29) hwhat flapperFileLidLit_bytes
  have hassignBlock :
      ExecBlock config solm evm [ .assign .storage lidRef (.var "data") ]
        (.ok solm evm') := by
    simpa [evm'] using
      assignStorageBlock
        (flapperFileData_eval evm what data)
        (flapperFileAssignLid evm what data)
  have helseLid :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") lidParamLit)
            [ .assign .storage lidRef (.var "data") ]
            [ .require (.boolLit false) ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hguardLid hassignBlock) ExecBlock.nil
  have helseTau :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") tauParamLit)
            [ .assign .storage tauRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") lidParamLit)
                [ .assign .storage lidRef (.var "data") ]
                [ .require (.boolLit false) ] ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hguardTau helseLid) ExecBlock.nil
  have helseTtl :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") ttlParamLit)
            [ .assign .storage ttlRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") tauParamLit)
                [ .assign .storage tauRef (wrap48 (.var "data")) ]
                [ .ite
                    (.binary .eq (.var "what") lidParamLit)
                    [ .assign .storage lidRef (.var "data") ]
                    [ .require (.boolLit false) ] ] ] ]
        (.ok solm evm') := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hguardTtl helseTau) ExecBlock.nil
  exact ExecFuncBody.execBlockOK <| by
    simpa [fileTransition, nonpayable, auth, locals, solm, evm'] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) <|
          ExecBlock.consNormal (ExecStmt.iteFalse hguardBeg helseTtl) ExecBlock.nil

theorem flapperFileBodyRevertsUnknown (evm : EVM.State) (what data : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hbeg : what ≠ flapperFileBegLit)
    (httl : what ≠ flapperFileTtlLit)
    (htau : what ≠ flapperFileTauLit)
    (hlid : what ≠ flapperFileLidLit) :
    ExecTransitionBody config contract evm (flapperFileLocals what data)
      fileTransition.body .reverted := by
  let locals := flapperFileLocals what data
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperFileLocals]
  have hguardAuth :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hguardBeg :
      evalExpr? config solm evm (.binary .eq (.var "what") begParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, begParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileBegLit
        ([98, 101, 103] ++ zeroPad29) hbeg flapperFileBegLit_bytes
  have hguardTtl :
      evalExpr? config solm evm (.binary .eq (.var "what") ttlParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, ttlParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileTtlLit
        ([116, 116, 108] ++ zeroPad29) httl flapperFileTtlLit_bytes
  have hguardTau :
      evalExpr? config solm evm (.binary .eq (.var "what") tauParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, tauParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileTauLit
        ([116, 97, 117] ++ zeroPad29) htau flapperFileTauLit_bytes
  have hguardLid :
      evalExpr? config solm evm (.binary .eq (.var "what") lidParamLit) =
        .ok (.bool false) := by
    simpa [solm, locals, lidParamLit] using
      flapperFileWhatGuard_false evm what data flapperFileLidLit
        ([108, 105, 100] ++ zeroPad29) hlid flapperFileLidLit_bytes
  have hfalse :
      evalExpr? config solm evm (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hrequire :
      ExecBlock config solm evm [ .require (.boolLit false) ] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hfalse)
  have helseLid :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") lidParamLit)
            [ .assign .storage lidRef (.var "data") ]
            [ .require (.boolLit false) ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hguardLid hrequire)
  have helseTau :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") tauParamLit)
            [ .assign .storage tauRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") lidParamLit)
                [ .assign .storage lidRef (.var "data") ]
                [ .require (.boolLit false) ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hguardTau helseLid)
  have helseTtl :
      ExecBlock config solm evm
        [ .ite
            (.binary .eq (.var "what") ttlParamLit)
            [ .assign .storage ttlRef (wrap48 (.var "data")) ]
            [ .ite
                (.binary .eq (.var "what") tauParamLit)
                [ .assign .storage tauRef (wrap48 (.var "data")) ]
                [ .ite
                    (.binary .eq (.var "what") lidParamLit)
                    [ .assign .storage lidRef (.var "data") ]
                    [ .require (.boolLit false) ] ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hguardTtl helseTau)
  exact ExecFuncBody.execBlockRevert <| by
    simpa [fileTransition, nonpayable, auth, locals, solm] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) <|
          ExecBlock.consRevert (ExecStmt.iteFalse hguardBeg helseTtl)

theorem flapperInitStorageLoad_eq
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot : UInt256) :
    Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner slot =
      storageRead I.codeOwner σ_evm slot := by
  have hmap :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot := by
    exact storageLoad_accountMapEquiv
      (evm1 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (evm2 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simpa [initState] using hAccounts)
      I.codeOwner slot
  have hread :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner slot =
        storageRead I.codeOwner σ_evm slot := by
    simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      storageRead_eq]
  exact hmap.symm.trans hread

theorem flapperFileBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 5))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨362⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I
    (⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_file (cd := I.calldata) hselLit
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecRaw := flapperDecode_file_ok (I := I) hsz68
    have hdec :
        decodeCalldataWithMode config.abiDecodeMode
          (fileTransition.params.map Param.name)
          (transitionSignature fileTransition).paramTypes I.calldata =
        some (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I)) := by
      simpa [flapperFileLocals] using hdecRaw
    by_cases hauthEvm : storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) =
        UInt256.ofNat 1
    · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let what := flapperFileWhatWord I
      let data := flapperFileDataWord I
      have hloadAuthEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        simpa [evmSolm, initState] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperRelyAuthSlot I)
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) = UInt256.ofNat 1 := by
        rw [hloadAuthEq]
        exact hauthEvm
      have henc : returnEquiv ByteArray.empty none fileTransition.returnType := by
        simpa [fileTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl rfl encodeReturnValues_nil)
      by_cases hbeg : what = flapperFileBegLit
      · have hbody :
            ExecTransitionBody config contract evmSolm
              (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
              fileTransition.body
              (.returned
                { contract := contract,
                  locals := flapperFileLocals (flapperFileWhatWord I)
                    (flapperFileDataWord I) }
                (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                  (UInt256.ofNat 4) (flapperFileDataWord I))
                none) := by
          simpa [evmSolm, what, data] using
            flapperFileBodyReturnsBeg evmSolm what data
              (by simp only [evmSolm, initState]; exact hwv) hauthSolm hbeg
        have hCreated :
            cA =
              (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                (UInt256.ofNat 4) (flapperFileDataWord I)).createdAccounts := by
          rw [storageStore_createdAccounts]
          simp [evmSolm, initState]
        have hAccounts' :
            accountMapEquiv
              (storageWrite I.codeOwner σ_evm (UInt256.ofNat 4) (flapperFileDataWord I))
              (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                (UInt256.ofNat 4) (flapperFileDataWord I)).accountMap := by
          rw [storageWrite_eq, storageStore_accountMap]
          simpa [evmSolm, initState] using
            accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 4)
              (flapperFileDataWord I) hAccounts
        exact (flapperX_file_beg_ok (g := Sat256.ofUInt256 g) hsize hsz68 hperm hauthEvm
            (by simpa [what] using hbeg) hreach)
          |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts' henc
      · by_cases httl : what = flapperFileTtlLit
        · let evmWord :=
            UInt256.lor (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
              (UInt256.land (UInt256.lnot flapperUint48Mask)
                (storageRead I.codeOwner σ_evm (UInt256.ofNat 5)))
          let solmWord :=
            UInt256.lor (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
              (UInt256.land (UInt256.lnot flapperUint48Mask)
                (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                  (UInt256.ofNat 5)))
          have hslot5Eq :
              Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                  (UInt256.ofNat 5) =
                storageRead I.codeOwner σ_evm (UInt256.ofNat 5) := by
            simpa [evmSolm, initState] using
              flapperInitStorageLoad_eq
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hAccounts (UInt256.ofNat 5)
          have hwordEq : solmWord = evmWord := by
            simp [solmWord, evmWord, hslot5Eq]
          have hbody :
              ExecTransitionBody config contract evmSolm
                (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
                fileTransition.body
                (.returned
                  { contract := contract,
                    locals := flapperFileLocals (flapperFileWhatWord I)
                      (flapperFileDataWord I) }
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    (UInt256.ofNat 5) solmWord)
                  none) := by
            simpa [evmSolm, what, data, solmWord] using
              flapperFileBodyReturnsTtl evmSolm what data
                (by simp only [evmSolm, initState]; exact hwv) hauthSolm hbeg httl
          have hCreated :
              cA =
                (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                  (UInt256.ofNat 5) solmWord).createdAccounts := by
            rw [storageStore_createdAccounts]
            simp [evmSolm, initState]
          have hAccounts' :
              accountMapEquiv
                (storageWrite I.codeOwner σ_evm (UInt256.ofNat 5) evmWord)
                (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                  (UInt256.ofNat 5) solmWord).accountMap := by
            rw [storageWrite_eq, storageStore_accountMap]
            simpa [evmSolm, initState, hwordEq] using
              accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 5)
                evmWord hAccounts
          have hx := flapperX_file_ttl_ok (g := Sat256.ofUInt256 g) hsize hsz68 hperm
            hauthEvm (by simpa [what] using hbeg) (by simpa [what] using httl) hreach
          simpa [evmWord] using
            hx.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts' henc
        · by_cases htau : what = flapperFileTauLit
          · let evmWord :=
              UInt256.lor
                (UInt256.mul (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
                  flapperUint48Shift)
                (UInt256.land
                  (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
                  (storageRead I.codeOwner σ_evm (UInt256.ofNat 5)))
            let solmWord :=
              UInt256.lor
                (UInt256.mul (UInt256.land (flapperFileDataWord I) flapperUint48Mask)
                  (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
                (UInt256.land
                  (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
                  (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                    (UInt256.ofNat 5)))
            have hslot5Eq :
                Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
                    (UInt256.ofNat 5) =
                  storageRead I.codeOwner σ_evm (UInt256.ofNat 5) := by
              simpa [evmSolm, initState] using
                flapperInitStorageLoad_eq
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hAccounts (UInt256.ofNat 5)
            have hwordEq : solmWord = evmWord := by
              simp [solmWord, evmWord, flapperUint48Shift, hslot5Eq]
            have hbody :
                ExecTransitionBody config contract evmSolm
                  (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
                  fileTransition.body
                  (.returned
                    { contract := contract,
                      locals := flapperFileLocals (flapperFileWhatWord I)
                        (flapperFileDataWord I) }
                    (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                      (UInt256.ofNat 5) solmWord)
                    none) := by
              simpa [evmSolm, what, data, solmWord] using
                flapperFileBodyReturnsTau evmSolm what data
                  (by simp only [evmSolm, initState]; exact hwv) hauthSolm hbeg httl htau
            have hCreated :
                cA =
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    (UInt256.ofNat 5) solmWord).createdAccounts := by
              rw [storageStore_createdAccounts]
              simp [evmSolm, initState]
            have hAccounts' :
                accountMapEquiv
                  (storageWrite I.codeOwner σ_evm (UInt256.ofNat 5) evmWord)
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    (UInt256.ofNat 5) solmWord).accountMap := by
              rw [storageWrite_eq, storageStore_accountMap]
              simpa [evmSolm, initState, hwordEq] using
                accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 5)
                  evmWord hAccounts
            have hx := flapperX_file_tau_ok (g := Sat256.ofUInt256 g) hsize hsz68 hperm
              hauthEvm (by simpa [what] using hbeg) (by simpa [what] using httl)
              (by simpa [what] using htau) hreach
            simpa [evmWord] using
              hx.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts' henc
          · by_cases hlid : what = flapperFileLidLit
            · have hbody :
                  ExecTransitionBody config contract evmSolm
                    (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
                    fileTransition.body
                    (.returned
                      { contract := contract,
                        locals := flapperFileLocals (flapperFileWhatWord I)
                          (flapperFileDataWord I) }
                      (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                        (UInt256.ofNat 8) (flapperFileDataWord I))
                      none) := by
                simpa [evmSolm, what, data] using
                  flapperFileBodyReturnsLid evmSolm what data
                    (by simp only [evmSolm, initState]; exact hwv) hauthSolm
                    hbeg httl htau hlid
              have hCreated :
                  cA =
                    (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                      (UInt256.ofNat 8) (flapperFileDataWord I)).createdAccounts := by
                rw [storageStore_createdAccounts]
                simp [evmSolm, initState]
              have hAccounts' :
                  accountMapEquiv
                    (storageWrite I.codeOwner σ_evm (UInt256.ofNat 8) (flapperFileDataWord I))
                    (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                      (UInt256.ofNat 8) (flapperFileDataWord I)).accountMap := by
                rw [storageWrite_eq, storageStore_accountMap]
                simpa [evmSolm, initState] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 8)
                    (flapperFileDataWord I) hAccounts
              exact (flapperX_file_lid_ok (g := Sat256.ofUInt256 g) hsize hsz68 hperm
                  hauthEvm (by simpa [what] using hbeg) (by simpa [what] using httl)
                  (by simpa [what] using htau) (by simpa [what] using hlid) hreach)
                |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts' henc
            · have hbody :
                  ExecTransitionBody config contract evmSolm
                    (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
                    fileTransition.body .reverted := by
                simpa [evmSolm, what, data] using
                  flapperFileBodyRevertsUnknown evmSolm what data
                    (by simp only [evmSolm, initState]; exact hwv) hauthSolm
                    hbeg httl htau hlid
              exact (flapperX_file_unknown_revert (g := Sat256.ofUInt256 g) hsize hsz68
                  hauthEvm (by simpa [what] using hbeg) (by simpa [what] using httl)
                  (by simpa [what] using htau) (by simpa [what] using hlid) hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
    · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let what := flapperFileWhatWord I
      let data := flapperFileDataWord I
      have hloadAuthEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        simpa [evmSolm, initState] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperRelyAuthSlot I)
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) ≠ UInt256.ofNat 1 := by
        intro hbad
        exact hauthEvm (by rw [← hloadAuthEq]; exact hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm
            (flapperFileLocals (flapperFileWhatWord I) (flapperFileDataWord I))
            fileTransition.body .reverted := by
        simpa [evmSolm, what, data] using
          flapperFileBodyRevertsAuth evmSolm what data
            (by simp only [evmSolm, initState]; exact hwv) hauthSolm
      exact (flapperX_file_auth_revert (g := Sat256.ofUInt256 g) hsize hsz68 hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := flapperDecode_file_none_short (I := I) hsz4 hshort
    have hrev := flapperX_file_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
