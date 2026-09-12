import Benchmarks.Dss.Flapper.Deal
import Benchmarks.Dss.Flapper.RuntimeBlocks_004
import Benchmarks.Dss.Flapper.RuntimeBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

abbrev flapperTendIdWord (I : ExecutionEnv) : UInt256 :=
  flapperDealIdWord I

def flapperTendLotArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def flapperTendBidArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

def flapperTendLocals (id lot bid : UInt256) : Store :=
  (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat))).insert "lot"
    (.int (Int.ofNat lot.toNat))).insert "bid" (.int (Int.ofNat bid.toNat))

def flapperTendLocalsBidOne (id lot bid bidOne : UInt256) : Store :=
  (flapperTendLocals id lot bid).insert "bidOne" (.int (Int.ofNat bidOne.toNat))

def flapperTendLocalsBegBid (id lot bid bidOne begBid : UInt256) : Store :=
  (flapperTendLocalsBidOne id lot bid bidOne).insert "begBid"
    (.int (Int.ofNat begBid.toNat))

def flapperTendLocalsAfterRefund
    (id lot bid bidOne begBid : UInt256) : Store :=
  (flapperTendLocalsBegBid id lot bid bidOne begBid).insert "_refundRet"
    (collapseReturns [])

def flapperTendLocalsAfterPay (locals : Store) : Store :=
  locals.insert "_payRet" (collapseReturns [])

def flapperTendLocalsTic (locals : Store) (tic : UInt256) : Store :=
  locals.insert "tic_" (.int (Int.ofNat tic.toNat))

theorem flapperTendLocalsBidOne_get_id
    (id lot bid bidOne : UInt256) :
    (flapperTendLocalsBidOne id lot bid bidOne).get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
  unfold flapperTendLocalsBidOne flapperTendLocals
  let sId : Store := (∅ : Store).insert "id" (.int (Int.ofNat id.toNat))
  let sLot : Store := sId.insert "lot" (.int (Int.ofNat lot.toNat))
  let sBid : Store := sLot.insert "bid" (.int (Int.ofNat bid.toNat))
  change (sBid.insert "bidOne" (.int (Int.ofNat bidOne.toNat))).get? "id" =
    some (.int (Int.ofNat id.toNat))
  rw [store_get_ne sBid (k := "bidOne") (a := "id")
    (.int (Int.ofNat bidOne.toNat)) (by decide)]
  change (sLot.insert "bid" (.int (Int.ofNat bid.toNat))).get? "id" =
    some (.int (Int.ofNat id.toNat))
  rw [store_get_ne sLot (k := "bid") (a := "id")
    (.int (Int.ofNat bid.toNat)) (by decide)]
  change (sId.insert "lot" (.int (Int.ofNat lot.toNat))).get? "id" =
    some (.int (Int.ofNat id.toNat))
  rw [store_get_ne sId (k := "lot") (a := "id")
    (.int (Int.ofNat lot.toNat)) (by decide)]
  exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat))

theorem flapperTendLocalsBidOne_get_bid
    (id lot bid bidOne : UInt256) :
    (flapperTendLocalsBidOne id lot bid bidOne).get? "bid" =
      some (.int (Int.ofNat bid.toNat)) := by
  unfold flapperTendLocalsBidOne flapperTendLocals
  let sId : Store := (∅ : Store).insert "id" (.int (Int.ofNat id.toNat))
  let sLot : Store := sId.insert "lot" (.int (Int.ofNat lot.toNat))
  let sBid : Store := sLot.insert "bid" (.int (Int.ofNat bid.toNat))
  change (sBid.insert "bidOne" (.int (Int.ofNat bidOne.toNat))).get? "bid" =
    some (.int (Int.ofNat bid.toNat))
  rw [store_get_ne sBid (k := "bidOne") (a := "bid")
    (.int (Int.ofNat bidOne.toNat)) (by decide)]
  exact store_get_self sLot "bid" (.int (Int.ofNat bid.toNat))

theorem flapperTendLocalsBidOne_get_bidOne
    (id lot bid bidOne : UInt256) :
    (flapperTendLocalsBidOne id lot bid bidOne).get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
  unfold flapperTendLocalsBidOne
  exact store_get_self (flapperTendLocals id lot bid) "bidOne"
    (.int (Int.ofNat bidOne.toNat))

theorem flapperTendLocalsBidOne_get_none
    (id lot bid bidOne : UInt256) {name : Ident}
    (hid : ("id" == name) = false) (hlot : ("lot" == name) = false)
    (hbid : ("bid" == name) = false) (hbidOne : ("bidOne" == name) = false) :
    (flapperTendLocalsBidOne id lot bid bidOne).get? name = none := by
  unfold flapperTendLocalsBidOne flapperTendLocals
  rw [store_get_ne4 (∅ : Store)
    (.int (Int.ofNat id.toNat)) (.int (Int.ofNat lot.toNat))
    (.int (Int.ofNat bid.toNat)) (.int (Int.ofNat bidOne.toNat))
    (k1 := "id") (k2 := "lot") (k3 := "bid") (k4 := "bidOne")
    (a := name) hid hlot hbid hbidOne]
  simp

theorem flapperTendLocalsBegBid_get_id
    (id lot bid bidOne begBid : UInt256) :
    (flapperTendLocalsBegBid id lot bid bidOne begBid).get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
  unfold flapperTendLocalsBegBid
  rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
    (k := "begBid") (a := "id") (.int (Int.ofNat begBid.toNat)) (by decide)]
  exact flapperTendLocalsBidOne_get_id id lot bid bidOne

theorem flapperTendLocalsBegBid_get_bidOne
    (id lot bid bidOne begBid : UInt256) :
    (flapperTendLocalsBegBid id lot bid bidOne begBid).get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
  unfold flapperTendLocalsBegBid
  rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
    (k := "begBid") (a := "bidOne") (.int (Int.ofNat begBid.toNat)) (by decide)]
  exact flapperTendLocalsBidOne_get_bidOne id lot bid bidOne

theorem flapperTendLocalsBegBid_get_bid
    (id lot bid bidOne begBid : UInt256) :
    (flapperTendLocalsBegBid id lot bid bidOne begBid).get? "bid" =
      some (.int (Int.ofNat bid.toNat)) := by
  unfold flapperTendLocalsBegBid
  rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
    (k := "begBid") (a := "bid") (.int (Int.ofNat begBid.toNat)) (by decide)]
  exact flapperTendLocalsBidOne_get_bid id lot bid bidOne

theorem flapperTendLocalsBegBid_get_begBid
    (id lot bid bidOne begBid : UInt256) :
    (flapperTendLocalsBegBid id lot bid bidOne begBid).get? "begBid" =
      some (.int (Int.ofNat begBid.toNat)) := by
  unfold flapperTendLocalsBegBid
  exact store_get_self (flapperTendLocalsBidOne id lot bid bidOne) "begBid"
    (.int (Int.ofNat begBid.toNat))

theorem flapperTendLocalsBegBid_get_none
    (id lot bid bidOne begBid : UInt256) {name : Ident}
    (hid : ("id" == name) = false) (hlot : ("lot" == name) = false)
    (hbid : ("bid" == name) = false) (hbidOne : ("bidOne" == name) = false)
    (hbegBid : ("begBid" == name) = false) :
    (flapperTendLocalsBegBid id lot bid bidOne begBid).get? name = none := by
  unfold flapperTendLocalsBegBid
  rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
    (k := "begBid") (a := name) (.int (Int.ofNat begBid.toNat)) hbegBid]
  exact flapperTendLocalsBidOne_get_none id lot bid bidOne hid hlot hbid hbidOne

abbrev flapperTendBaseSlot (id : UInt256) : UInt256 :=
  flapperDealBaseSlot id

abbrev flapperTendPackedSlot (id : UInt256) : UInt256 :=
  flapperDealPackedSlot id

abbrev flapperTendLiveWordOfState (evm : EVM.State) : UInt256 :=
  flapperDealLiveWordOfState evm

abbrev flapperTendGemWordOfState (evm : EVM.State) : UInt256 :=
  flapperDealGemWordOfState evm

def flapperTendBegWordOfState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 4)

def flapperTendTtlWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
    flapperUint48Mask

abbrev flapperTendLotWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealLotWordOfState evm id

abbrev flapperTendBidWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealBidWordOfState evm id

abbrev flapperTendPackedWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealPackedWordOfState evm id

abbrev flapperTendGuyWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealGuyWordOfState evm id

abbrev flapperTendTicWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealTicWordOfState evm id

abbrev flapperTendEndWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  flapperDealEndWordOfState evm id

abbrev flapperTendTimestampWordOfState (evm : EVM.State) : UInt256 :=
  flapperDealTimestampWordOfState evm

def flapperTendNowWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land (flapperTendTimestampWordOfState evm) flapperUint48Mask

def flapperTendNewTicWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (flapperTendTimestampWordOfState evm + flapperTendTtlWordOfState evm)
    flapperUint48Mask

def flapperTendBidOneWordOfState (_evm : EVM.State) (_id bid : UInt256) : UInt256 :=
  UInt256.mul bid (UInt256.ofNat 1000000000000000000)

def flapperTendBegBidWordOfState (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.mul (flapperTendBegWordOfState evm) (flapperTendBidWordOfState evm id)

def flapperTendPayAmtWordOfState (evm : EVM.State) (id bid : UInt256) : UInt256 :=
  UInt256.sub bid (flapperTendBidWordOfState evm id)

def flapperTendPackedTicWord (old newTic : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old
      (UInt256.lnot (UInt256.shiftLeft flapperUint48Mask (UInt256.ofNat 160))))
    (UInt256.mul flapperUint48Shift160
      (UInt256.land flapperUint48Mask newTic))

theorem flapperNatLandClearTic48 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 160 - 1 + (2 ^ 256 - 2 ^ 208)) =
      n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208 := by
  have hmaskLor :
      (2 : Nat) ^ 160 - 1 + (2 ^ 256 - 2 ^ 208) =
        Nat.lor (2 ^ 160 - 1) ((2 ^ 48 - 1) * 2 ^ 208) := by
    rw [nat_lor_shift_add (2 ^ 160 - 1) (2 ^ 48 - 1) 208]
    · norm_num [Nat.pow_add]
    · norm_num
  have htargetLor :
      n % 2 ^ 160 + n / 2 ^ 208 * 2 ^ 208 =
        Nat.lor (n % 2 ^ 160) (n / 2 ^ 208 * 2 ^ 208) := by
    rw [nat_lor_shift_add (n % 2 ^ 160) (n / 2 ^ 208) 208]
    exact Nat.lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 160))
      (by norm_num : 2 ^ 160 < 2 ^ 208)
  rw [hmaskLor, htargetLor]
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& ((2 ^ 160 - 1) ||| ((2 ^ 48 - 1) * 2 ^ 208))).testBit i =
    ((n % 2 ^ 160) ||| (n / 2 ^ 208 * 2 ^ 208)).testBit i
  rw [Nat.testBit_and]
  rw [Nat.testBit_or]
  rw [Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_two_pow_sub_one]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi160 : i < 160
  · have hi208 : i < 208 := by omega
    simp [hi160, hi208]
  · by_cases hi208 : i < 208
    · have hnot208le : ¬ 208 ≤ i := by omega
      simp [hi160, hnot208le]
    · have h208i : 208 ≤ i := Nat.le_of_not_gt hi208
      by_cases hi256 : i < 256
      · have hsub48 : i - 208 < 48 := by omega
        simp [hi160, h208i, hsub48]
        exact (divPow_testBit n 208 i h208i).symm
      · have hnbit : n.testBit i = false := by
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
            (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (by omega)))
        have hsub48 : ¬ i - 208 < 48 := by omega
        have hq : n / 2 ^ 208 < 2 ^ 48 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
          exact hn
        have hdivbit : (n / 2 ^ 208).testBit (i - 208) = false := by
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hq
            (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) (by omega)))
        simp [hi160, h208i, hsub48, hnbit]
        simpa [show 2 ^ 208 =
            411376139330301510538742295639337626245683966408394965837152256 by
          norm_num] using hdivbit

theorem flapperClearUint48Offset20_toNat (old : UInt256) :
    (UInt256.land old
        (UInt256.lnot (UInt256.shiftLeft flapperUint48Mask (UInt256.ofNat 160)))).toNat =
      old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 := by
  have hmask :
      UInt256.lnot (UInt256.shiftLeft flapperUint48Mask (UInt256.ofNat 160)) =
        UInt256.ofNat ((2 : Nat) ^ 160 - 1 + (2 ^ 256 - 2 ^ 208)) := by
    native_decide
  rw [hmask, uland_toNat]
  have hmaskLt : (2 : Nat) ^ 160 - 1 + (2 ^ 256 - 2 ^ 208) < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  rw [ulit_toNat' _ hmaskLt]
  change Nat.land old.toNat ((2 : Nat) ^ 160 - 1 + (2 ^ 256 - 2 ^ 208)) =
    old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208
  rw [flapperNatLandClearTic48 old.toNat old.val.isLt]

theorem flapperStorageLocStore_uint48_offset20 (evm : EVM.State)
    (slot val : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨20, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land val flapperUint48Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (flapperTendPackedTicWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let low := UInt256.land val flapperUint48Mask
  have htakeOldLen :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 20).length = 20 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have htakeLowLen :
      ((EVM.Word.toBytesLEWithSizeProof low).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof low).2]
    norm_num
  have hlowLt : low.toNat < 2 ^ 48 := by
    simpa [low] using flapperUint48Word_lt val
  have hlowClean : UInt256.land flapperUint48Mask low = low := by
    rw [u256_land_comm flapperUint48Mask low]
    simpa [low] using flapperUint48Mask_clean_right_file val
  have hlowCleanRight : UInt256.land low flapperUint48Mask = low := by
    simpa [low] using flapperUint48Mask_clean_right_file val
  have hmulLt : low.toNat * 2 ^ 160 < UInt256.size := by
    calc
      low.toNat * 2 ^ 160 < 2 ^ 48 * 2 ^ 160 :=
        Nat.mul_lt_mul_of_pos_right hlowLt (by norm_num)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  have hmulLt' : 2 ^ 160 * low.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hmulLt
  have hq : old.toNat / 2 ^ 208 < 2 ^ 48 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 208 * 2 ^ 48 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    exact old.val.isLt
  have hsumlt :
      old.toNat % 2 ^ 160 + low.toNat * 2 ^ 160 +
          old.toNat / 2 ^ 208 * 2 ^ 208 < UInt256.size := by
    have holdLowle : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 160))
    have hlowle : low.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hqle : old.toNat / 2 ^ 208 ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hq
    have hlowterm : low.toNat * 2 ^ 160 ≤ (2 ^ 48 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hlowle
    have hqterm :
        old.toNat / 2 ^ 208 * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hqle
    have hmax :
        (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 160 +
            (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have holdLowLt : old.toNat % 2 ^ 160 < 2 ^ 160 :=
    Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 160)
  have holdLowLt208 : old.toNat % 2 ^ 160 < 2 ^ 208 :=
    Nat.lt_trans holdLowLt (by norm_num : 2 ^ 160 < 2 ^ 208)
  have hpreserveLor :
      old.toNat % 2 ^ 160 + old.toNat / 2 ^ 208 * 2 ^ 208 =
        Nat.lor (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 208 * 2 ^ 208) := by
    rw [nat_lor_shift_add (old.toNat % 2 ^ 160) (old.toNat / 2 ^ 208) 208
      holdLowLt208]
  have htwoFieldLt :
      old.toNat % 2 ^ 160 + low.toNat * 2 ^ 160 < 2 ^ 208 := by
    have holdLowLe : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 :=
      Nat.le_pred_of_lt holdLowLt
    have hlowLe : low.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hlowTerm : low.toNat * 2 ^ 160 ≤ (2 ^ 48 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hlowLe
    have hmax : (2 ^ 160 - 1) + (2 ^ 48 - 1) * 2 ^ 160 < 2 ^ 208 := by
      norm_num [Nat.pow_add]
    omega
  congr 2
  apply u256_inj
  change fromBytes'
      (List.take 20 (EVM.Word.toBytesLEWithSizeProof old).1 ++
        List.take 6 (EVM.Word.toBytesLEWithSizeProof low).1 ++
        List.drop 26 (EVM.Word.toBytesLEWithSizeProof old).1) =
      (flapperTendPackedTicWord old val).toNat
  rw [fromBytes'_append, fromBytes'_append,
    fromBytes'_take_wordLE_land_mask old 20 (by decide),
    fromBytes'_take_wordLE_land_mask low 6 (by decide),
    fromBytes'_drop_wordLE, List.length_append, htakeOldLen, htakeLowLen]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 2 ^ (8 * (20 + 6)) = 2 ^ 208 by norm_num]
  rw [show 256 ^ 26 = 2 ^ 208 by norm_num]
  unfold flapperTendPackedTicWord
  rw [u256_lor_toNat, u256_mul_toNat, flapperClearUint48Offset20_toNat]
  rw [show flapperUint48Shift160 = UInt256.ofNat (2 ^ 160) by native_decide]
  rw [show (UInt256.ofNat (2 ^ 160)).toNat = 2 ^ 160 by native_decide]
  rw [show UInt256.ofNat (2 ^ (8 * 6) - 1) = flapperUint48Mask by native_decide]
  rw [hlowCleanRight]
  rw [show UInt256.land flapperUint48Mask val = low by
    simp [low, u256_land_comm]]
  rw [Nat.mod_eq_of_lt hmulLt']
  rw [Nat.mul_comm (2 ^ 160) low.toNat]
  rw [← flapperLow160Mask_mod_eq_land old]
  rw [hpreserveLor]
  rw [flapperNatLorAssoc]
  rw [nat_lor_comm (old.toNat / 2 ^ 208 * 2 ^ 208) (low.toNat * 2 ^ 160)]
  rw [← flapperNatLorAssoc]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 160) low.toNat 160 holdLowLt]
  rw [nat_lor_shift_add
    (old.toNat % 2 ^ 160 + low.toNat * 2 ^ 160)
    (old.toNat / 2 ^ 208) 208 htwoFieldLt]
  rw [Nat.mod_eq_of_lt hsumlt]
  ring_nf

abbrev flapperTendBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealBidWord σ I

abbrev flapperTendGemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealGemWord σ I

def flapperTendBegWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 4)

def flapperTendTtlWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Mask

abbrev flapperTendLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealLotWord σ I

abbrev flapperTendPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealPackedWord σ I

abbrev flapperTendGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealGuyWord σ I

abbrev flapperTendTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealTicWord σ I

abbrev flapperTendEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flapperDealEndWord σ I

abbrev flapperTendTimestampWord (I : ExecutionEnv) : UInt256 :=
  flapperDealTimestampWord I

def flapperTendNowWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperTendTimestampWord I) flapperUint48Mask

def flapperTendNewTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperTendTimestampWord I + flapperTendTtlWord σ I)
    flapperUint48Mask

abbrev flapperTendOneWord : UInt256 :=
  UInt256.ofNat 1000000000000000000

theorem flapperTendOneWord_toNat :
    flapperTendOneWord.toNat = 1000000000000000000 := by
  unfold flapperTendOneWord
  exact ulit_toNat' 1000000000000000000 (by norm_num [UInt256.size])

def flapperTendBidOneWord (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (flapperTendBidArgWord I) flapperTendOneWord

def flapperTendBegBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (flapperTendBegWord σ I) (flapperTendBidWord σ I)

def flapperTendPayAmtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (flapperTendBidArgWord I) (flapperTendBidWord σ I)

abbrev flapperTendScratchMem (id : UInt256) (mem : ByteArray) : ByteArray :=
  flapperDealScratchMem id mem

def flapperTendMoveCallMemFrom
    (fromWord toWord amtWord : UInt256) (base : ByteArray) : ByteArray :=
  amtWord.toByteArray.write 0
    (toWord.toByteArray.write 0
      (fromWord.toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32)
    196 32

def flapperTendRefundCallMemFrom
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) : ByteArray :=
  flapperTendMoveCallMemFrom (UInt256.ofNat I.source.val)
    (flapperTendGuyWord σ I) (flapperTendBidWord σ I) base

def flapperTendPayCallMemFrom
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) : ByteArray :=
  flapperTendMoveCallMemFrom (UInt256.ofNat I.source.val)
    (UInt256.ofNat I.codeOwner.val) (flapperTendPayAmtWord σ I) base

def flapperTendMoveCallRest
    (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) : List UInt256 :=
  [UInt256.ofNat 228, UInt256.ofNat 3140843579, flapperTendGemWord σ I,
    flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
    UInt256.ofNat 360, sel]

def flapperTendAfterRefundWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I))
    (UInt256.lor (UInt256.ofNat I.source.val)
      (UInt256.land (UInt256.lnot solcAddrMask)
        (storageRead I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I)))))

def flapperTendAfterPayWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner σ (flapperTendBaseSlot (flapperTendIdWord I))
    (flapperTendBidArgWord I)

def flapperTendAfterTicWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I))
    (flapperTendPackedTicWord
      (storageRead I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I)))
      (flapperTendNewTicWord σ I))

theorem flapperTendAfterRefundWorld_eq_setAddress (σ : AccountMap)
    (I : ExecutionEnv) :
    flapperTendAfterRefundWorld σ I =
      storageWrite I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I))
        (setAddressOffset0Word
          (storageRead I.codeOwner σ (flapperTendPackedSlot (flapperTendIdWord I)))
          (UInt256.ofNat I.source.val)) := by
  let slot := flapperTendPackedSlot (flapperTendIdWord I)
  unfold flapperTendAfterRefundWorld setAddressOffset0Word
  change storageWrite I.codeOwner σ slot
      (UInt256.lor (UInt256.ofNat I.source.val)
        (UInt256.land (UInt256.lnot solcAddrMask)
          (storageRead I.codeOwner σ slot))) =
    storageWrite I.codeOwner σ slot
      (UInt256.lor
        (UInt256.land (storageRead I.codeOwner σ slot)
          (UInt256.lnot solcAddrMask))
        (UInt256.land (UInt256.ofNat I.source.val) solcAddrMask))
  have hsourceToNat : (UInt256.ofNat I.source.val).toNat = I.source.val := by
    have hword : I.source.val < UInt256.size := by
      exact lt_of_lt_of_le I.source.isLt (by decide)
    simpa using ulit_toNat' I.source.val hword
  have hcanon : (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
    rw [hsourceToNat]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using
      I.source.isLt
  rw [solcAddrMask_clean hcanon]
  rw [u256_land_comm (UInt256.lnot solcAddrMask)
    (storageRead I.codeOwner σ slot)]
  exact congrArg (fun value => storageWrite I.codeOwner σ slot value)
    (u256_lor_comm (UInt256.ofNat I.source.val)
      (UInt256.land (storageRead I.codeOwner σ slot)
        (UInt256.lnot solcAddrMask)))

theorem flapperTendStorageLoad_eq_of_stateRel
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
  exact flapperDealStorageLoad_eq_of_stateRel (g := g) hState slot

theorem flapperTendGemWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendGemWordOfState evm = flapperTendGemWord σworld I := by
  have hload := flapperTendStorageLoad_eq_of_stateRel (g := g) hState
    (UInt256.ofNat 3)
  simp [flapperTendGemWordOfState, flapperDealGemWordOfState,
    flapperYankGemWordOfState, flapperTendGemWord, flapperDealGemWord,
    flapperYankGemWord, hload]

theorem flapperTendBidWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendBidWordOfState evm (flapperTendIdWord I) =
      flapperTendBidWord σworld I := by
  have hload := flapperTendStorageLoad_eq_of_stateRel (g := g) hState
    (flapperTendBaseSlot (flapperTendIdWord I))
  simpa [flapperTendBidWordOfState, flapperDealBidWordOfState,
    flapperYankBidWordOfState, flapperTendBidWord, flapperDealBidWord,
    flapperYankBidWord, flapperTendBaseSlot, flapperDealBaseSlot,
    flapperTendIdWord, flapperDealIdWord] using hload

theorem flapperTendPackedWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendPackedWordOfState evm (flapperTendIdWord I) =
      flapperTendPackedWord σworld I := by
  have hload := flapperTendStorageLoad_eq_of_stateRel (g := g) hState
    (flapperTendPackedSlot (flapperTendIdWord I))
  simpa [flapperTendPackedWordOfState, flapperDealPackedWordOfState,
    flapperYankPackedWordOfState, flapperTendPackedWord, flapperDealPackedWord,
    flapperYankPackedWord, flapperTendPackedSlot, flapperDealPackedSlot,
    flapperYankPackedSlot, flapperTendBaseSlot, flapperDealBaseSlot,
    flapperTendIdWord, flapperDealIdWord] using hload

theorem flapperTendGuyWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendGuyWordOfState evm (flapperTendIdWord I) =
      flapperTendGuyWord σworld I := by
  have hpacked := flapperTendPackedWordOfState_eq_of_stateRel (g := g) hState
  simp [flapperTendGuyWordOfState, flapperDealGuyWordOfState,
    flapperYankGuyWordOfState, flapperTendGuyWord, flapperDealGuyWord,
    flapperYankGuyWord, hpacked, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm]

theorem flapperTendTtlWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendTtlWordOfState evm = flapperTendTtlWord σworld I := by
  have hload := flapperTendStorageLoad_eq_of_stateRel (g := g) hState
    (UInt256.ofNat 5)
  simp [flapperTendTtlWordOfState, flapperTendTtlWord, hload]

theorem flapperTendTimestampWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendTimestampWordOfState evm = flapperTendTimestampWord I := by
  simp [flapperTendTimestampWordOfState, flapperTendTimestampWord,
    flapperDealTimestampWordOfState, flapperDealTimestampWord, hState.env]

theorem flapperTendNowWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendNowWordOfState evm = flapperTendNowWord I := by
  simp [flapperTendNowWordOfState, flapperTendNowWord,
    flapperTendTimestampWordOfState_eq_of_stateRel (g := g) hState]

theorem flapperTendNewTicWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendNewTicWordOfState evm = flapperTendNewTicWord σworld I := by
  simp [flapperTendNewTicWordOfState, flapperTendNewTicWord,
    flapperTendTimestampWordOfState_eq_of_stateRel (g := g) hState,
    flapperTendTtlWordOfState_eq_of_stateRel (g := g) hState]

theorem flapperTendPayAmtWordOfState_eq_of_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    flapperTendPayAmtWordOfState evm (flapperTendIdWord I)
        (flapperTendBidArgWord I) =
      flapperTendPayAmtWord σworld I := by
  simp [flapperTendPayAmtWordOfState, flapperTendPayAmtWord,
    flapperTendBidWordOfState_eq_of_stateRel (g := g) hState]

theorem flapperTendAfterRefund_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, flapperTendAfterRefundWorld σworld I)
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (flapperTendPackedSlot (flapperTendIdWord I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (flapperTendPackedSlot (flapperTendIdWord I)))
          (UInt256.ofNat evm.executionEnv.source.val))) := by
  let slot := flapperTendPackedSlot (flapperTendIdWord I)
  have hload := flapperTendStorageLoad_eq_of_stateRel (g := g) hState slot
  have hloadI :
      Solm.EVM.storageLoad evm I.codeOwner slot =
        storageRead I.codeOwner σworld slot := by
    simpa [hState.env] using hload
  have hstore := hState.storageStore_codeOwner slot
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (UInt256.ofNat evm.executionEnv.source.val))
  simpa [slot, flapperTendAfterRefundWorld_eq_setAddress, storageWrite_eq,
    hState.env, hloadI] using hstore

theorem flapperTendAfterPay_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, flapperTendAfterPayWorld σworld I)
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (flapperTendBaseSlot (flapperTendIdWord I))
        (flapperTendBidArgWord I)) := by
  have hstore := hState.storageStore_codeOwner
    (flapperTendBaseSlot (flapperTendIdWord I)) (flapperTendBidArgWord I)
  simpa [flapperTendAfterPayWorld, storageWrite_eq, hState.env] using hstore

theorem flapperTendAfterTic_stateRel
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {evm : EVM.State}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm) :
    CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, flapperTendAfterTicWorld σworld I)
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (flapperTendPackedSlot (flapperTendIdWord I))
        (flapperTendPackedTicWord
          (flapperTendPackedWordOfState evm (flapperTendIdWord I))
          (flapperTendNewTicWordOfState evm))) := by
  let slot := flapperTendPackedSlot (flapperTendIdWord I)
  have hpacked := flapperTendPackedWordOfState_eq_of_stateRel (g := g) hState
  have hnew := flapperTendNewTicWordOfState_eq_of_stateRel (g := g) hState
  have hstore := hState.storageStore_codeOwner slot
    (flapperTendPackedTicWord
      (flapperTendPackedWordOfState evm (flapperTendIdWord I))
      (flapperTendNewTicWordOfState evm))
  simpa [slot, flapperTendAfterTicWorld, storageWrite_eq, hState.env, hpacked,
    hnew] using hstore

theorem flapperTendScratchMem_size_ge_96 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size) :
    96 ≤ (flapperTendScratchMem id mem).size := by
  simpa [flapperTendScratchMem] using
    flapperDealScratchMem_size_ge_96 id mem hmem

theorem flapperTendScratchMem_read64 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperTendScratchMem id mem).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  simpa [flapperTendScratchMem] using
    flapperDealScratchMem_read64 id mem hmem hread

theorem flapperTendScratchMem_mload64 (id : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    memLoad (UInt256.ofNat 64) (flapperTendScratchMem id mem) =
      UInt256.ofNat 128 := by
  simpa [flapperTendScratchMem] using
    flapperDealScratchMem_mload64 id mem hmem hread

theorem flapperTendMoveCallMemFromSelector_size_ge_160
    (base : ByteArray) :
    160 ≤ (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded flapperDealMoveSelectorWord
    base 128

theorem flapperTendMoveCallMemFromFrom_size_ge_164
    (fromWord : UInt256) (base : ByteArray) :
    164 ≤ (fromWord.toByteArray.write 0
      (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
      132 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded fromWord
    (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32) 132

theorem flapperTendMoveCallMemFromTo_size_ge_196
    (fromWord toWord : UInt256) (base : ByteArray) :
    196 ≤ (toWord.toByteArray.write 0
      (fromWord.toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded toWord
    (fromWord.toByteArray.write 0
      (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
      132 32) 164

theorem flapperTendMoveCallMemFrom_size_ge_228
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    228 ≤ (flapperTendMoveCallMemFrom fromWord toWord amtWord base).size := by
  unfold flapperTendMoveCallMemFrom
  exact toByteArray_write_size_ge_off_add32_unbounded amtWord
    (toWord.toByteArray.write 0
      (fromWord.toByteArray.write 0
        (flapperDealMoveSelectorWord.toByteArray.write 0 base 128 32)
        132 32)
      164 32) 196

theorem flapperTendMoveCallMemFrom_read64
    (fromWord toWord amtWord : UInt256) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperTendMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded amtWord _ 196 64
    (by
      have h := flapperTendMoveCallMemFromTo_size_ge_196 fromWord toWord base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded toWord _ 164 64
    (by
      have h := flapperTendMoveCallMemFromFrom_size_ge_164 fromWord base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded fromWord _ 132 64
    (by
      have h := flapperTendMoveCallMemFromSelector_size_ge_160 base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded flapperDealMoveSelectorWord _
    128 64 (by omega) (by omega)]
  exact hread

theorem flapperTendRefundCallMemFrom_size_ge_96
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    96 ≤ (flapperTendRefundCallMemFrom σ I base).size := by
  unfold flapperTendRefundCallMemFrom
  have hsize := flapperTendMoveCallMemFrom_size_ge_228
    (UInt256.ofNat I.source.val) (flapperTendGuyWord σ I)
    (flapperTendBidWord σ I) base
  omega

theorem flapperTendRefundCallMemFrom_read64
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    (flapperTendRefundCallMemFrom σ I base).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperTendRefundCallMemFrom
  exact flapperTendMoveCallMemFrom_read64
    (UInt256.ofNat I.source.val) (flapperTendGuyWord σ I)
    (flapperTendBidWord σ I) base hbase hread

theorem flapperTendMoveCallMemFrom_mload64
    (fromWord toWord amtWord : UInt256) (base : ByteArray)
    (hbase : 96 ≤ base.size)
    (hread : base.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128)) :
    memLoad (UInt256.ofNat 64)
        (flapperTendMoveCallMemFrom fromWord toWord amtWord base) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperTendMoveCallMemFrom_size_ge_228 fromWord toWord amtWord base
    omega)]
  rw [flapperTendMoveCallMemFrom_read64 fromWord toWord amtWord base hbase hread]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperTendMoveCallMemFrom_read196
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        196 32 =
      UInt256.toByteArray amtWord := by
  unfold flapperTendMoveCallMemFrom
  exact toByteArray_write_read_back_of_gap_unbounded amtWord _ 196

theorem flapperTendMoveCallMemFrom_read164
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        164 32 =
      UInt256.toByteArray toWord := by
  unfold flapperTendMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded amtWord _ 196 164
    (by
      have h := flapperTendMoveCallMemFromTo_size_ge_196 fromWord toWord base
      omega)
    (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded toWord _ 164

theorem flapperTendMoveCallMemFrom_read132
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        132 32 =
      UInt256.toByteArray fromWord := by
  unfold flapperTendMoveCallMemFrom
  rw [toByteArray_write_read_below_of_gap_unbounded amtWord _ 196 132
    (by
      have h := flapperTendMoveCallMemFromTo_size_ge_196 fromWord toWord base
      omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded toWord _ 164 132
    (by
      have h := flapperTendMoveCallMemFromFrom_size_ge_164 fromWord base
      omega)
    (by omega)]
  exact toByteArray_write_read_back_of_gap_unbounded fromWord _ 132

theorem flapperTendMoveCallMemFrom_read128_4
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        128 4 =
      moveSelector := by
  unfold flapperTendMoveCallMemFrom
  rw [toByteArray_write_read_below_len_of_gap amtWord _ 196 128 4
    (by
      have h := flapperTendMoveCallMemFromTo_size_ge_196 fromWord toWord base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 196 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_below_len_of_gap toWord _ 164 128 4
    (by
      have h := flapperTendMoveCallMemFromFrom_size_ge_164 fromWord base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 164 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_below_len_of_gap fromWord _ 132 128 4
    (by
      have h := flapperTendMoveCallMemFromSelector_size_ge_160 base
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have hU : 132 < USize.size := by native_decide
      omega)]
  rw [toByteArray_write_read_window_of_gap_unbounded flapperDealMoveSelectorWord
    base 128 0 4 (by norm_num) (by norm_num) (by norm_num)]
  exact flapperDealMoveSelectorPrefix

theorem flapperTendMoveCallMemFrom_read128_100
    (fromWord toWord amtWord : UInt256) (base : ByteArray) :
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base).readWithPadding
        128 100 =
      moveSelector ++ UInt256.toByteArray fromWord ++
        UInt256.toByteArray toWord ++ UInt256.toByteArray amtWord := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperTendMoveCallMemFrom_size_ge_228 fromWord toWord amtWord base
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperTendMoveCallMemFrom_size_ge_228 fromWord toWord amtWord base
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split
    (flapperTendMoveCallMemFrom fromWord toWord amtWord base) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperTendMoveCallMemFrom_size_ge_228 fromWord toWord amtWord base
      omega)]
  rw [flapperTendMoveCallMemFrom_read128_4,
    flapperTendMoveCallMemFrom_read132,
    flapperTendMoveCallMemFrom_read164,
    flapperTendMoveCallMemFrom_read196]
  simp [ByteArray.append_assoc]

theorem flapperEncodeValue_accountAddress (addrWord : AccountAddress) :
    encodeABIValue? addr (.address addrWord) =
      some (EVM.Word.toBytesBE (UInt256.ofNat addrWord.val)) := by
  have hword : EVM.word addrWord.val = UInt256.ofNat addrWord.val := by
    apply u256_inj
    unfold EVM.word EVM.uintN UInt256.ofNat UInt256.toNat
    simp only [Fin.ofNat]
    change addrWord.val % EVM.twoPow 256 = addrWord.val % UInt256.size
    simp [EVM.twoPow, UInt256.size]
  simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
  rw [hword]

theorem flapperTendRefundMoveEncodeFrom_eq
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    config.externalABI.encode? "move"
        [.address I.source,
          .address (AccountAddress.ofNat (flapperTendGuyWord σ I).toNat),
          .int (Int.ofNat (flapperTendBidWord σ I).toNat)] =
      some ((flapperTendRefundCallMemFrom σ I base).readWithPadding 128 100) := by
  unfold flapperTendRefundCallMemFrom
  rw [flapperTendMoveCallMemFrom_read128_100]
  change externalABI.encode? "move"
        [.address I.source,
          .address (AccountAddress.ofNat (flapperTendGuyWord σ I).toNat),
          .int (Int.ofNat (flapperTendBidWord σ I).toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (flapperTendGuyWord σ I) ++
        UInt256.toByteArray (flapperTendBidWord σ I))
  have hencSource :
      encodeABIValue? addr (.address I.source) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) :=
    flapperEncodeValue_accountAddress I.source
  have hcanonGuy : (flapperTendGuyWord σ I).toNat < EVM.addressModulus := by
    simpa [flapperTendGuyWord, flapperDealGuyWord, flapperYankGuyWord,
      flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask] using
      solcAddrMask_result_canonical (flapperYankPackedWord σ I)
  have hencGuy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (flapperTendGuyWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperTendGuyWord σ I)) :=
    flapperEncodeValue_addr (flapperTendGuyWord σ I) hcanonGuy
  have hencBid :
      encodeABIValue? uint256
          (.int (Int.ofNat (flapperTendBidWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperTendBidWord σ I)) :=
    flapperEncodeValue_uint256 (flapperTendBidWord σ I)
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.source,
            .address (AccountAddress.ofNat (flapperTendGuyWord σ I).toNat),
            .int (Int.ofNat (flapperTendBidWord σ I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val) ++
          EVM.Word.toBytesBE (flapperTendGuyWord σ I) ++
          EVM.Word.toBytesBE (flapperTendBidWord σ I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencSource,
      hencGuy, hencBid, hdynAddr, hdynUint, bind, Option.bind,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem flapperTendPayMoveEncodeFrom_eq
    (σ : AccountMap) (I : ExecutionEnv) (base : ByteArray) :
    config.externalABI.encode? "move"
        [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (flapperTendPayAmtWord σ I).toNat)] =
      some ((flapperTendPayCallMemFrom σ I base).readWithPadding 128 100) := by
  unfold flapperTendPayCallMemFrom
  rw [flapperTendMoveCallMemFrom_read128_100]
  change externalABI.encode? "move"
        [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (flapperTendPayAmtWord σ I).toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.source.val) ++
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (flapperTendPayAmtWord σ I))
  have hencSource :
      encodeABIValue? addr (.address I.source) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) :=
    flapperEncodeValue_accountAddress I.source
  have hencOwner :
      encodeABIValue? addr (.address I.codeOwner) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) :=
    flapperEncodeValue_accountAddress I.codeOwner
  have hencPay :
      encodeABIValue? uint256
          (.int (Int.ofNat (flapperTendPayAmtWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (flapperTendPayAmtWord σ I)) :=
    flapperEncodeValue_uint256 (flapperTendPayAmtWord σ I)
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.source, .address I.codeOwner,
            .int (Int.ofNat (flapperTendPayAmtWord σ I).toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val) ++
          EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (flapperTendPayAmtWord σ I)) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencSource,
      hencOwner, hencPay, hdynAddr, hdynUint, bind, Option.bind,
      Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem flapperTendRuntimeRefundCallMem_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem) = UInt256.ofNat 128) :
    flapperRuntimeBlocks.flapperRuntime_block_2433_memory
        (ee := I) (mem := mem) (σ := σ) (x2 := flapperTendIdWord I) =
      flapperTendRefundCallMemFrom σ I
        (flapperTendScratchMem (flapperTendIdWord I) mem) := by
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot, flapperTendScratchMem,
      flapperDealScratchMem, show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  simp [flapperRuntimeBlocks.flapperRuntime_block_2433_memory,
    flapperTendRefundCallMemFrom, flapperTendMoveCallMemFrom, flapperTendScratchMem,
    flapperDealScratchMem, hbaseRaw, hhashRaw, flapperTendBidWord,
    flapperDealBidWord, flapperYankBidWord, flapperTendGuyWord,
    flapperDealGuyWord, flapperYankGuyWord, flapperTendPackedWord,
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

theorem flapperTendRuntimeRefundCallStack_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) (mem : ByteArray)
    (hscratch : 96 ≤ (flapperTendScratchMem (flapperTendIdWord I) mem).size)
    (hread : (flapperTendScratchMem (flapperTendIdWord I) mem).readWithPadding
      64 32 = UInt256.toByteArray (UInt256.ofNat 128)) :
    flapperRuntimeBlocks.flapperRuntime_block_2433_stack
        (ee := I) (mem := mem) (σ := σ)
        (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
        (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel]) =
      (UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel) := by
  have h64 : (UInt256.ofNat 64).toNat <
      (flapperTendScratchMem (flapperTendIdWord I) mem).size := by
    rw [show (UInt256.ofNat 64).toNat = 64 by decide]
    omega
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem) = UInt256.ofNat 128 :=
    by
      unfold memLoad
      exact mloadWordValue_of_readWithPadding h64 hread
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot, flapperTendScratchMem,
      flapperDealScratchMem, show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  have hcallMem :
      flapperRuntimeBlocks.flapperRuntime_block_2433_memory
          (ee := I) (mem := mem) (σ := σ) (x2 := flapperTendIdWord I) =
        flapperTendRefundCallMemFrom σ I
          (flapperTendScratchMem (flapperTendIdWord I) mem) :=
    flapperTendRuntimeRefundCallMem_eq_from σ I mem hbase
  have hcallFrom :
      memLoad (UInt256.ofNat 64)
        (flapperTendRefundCallMemFrom σ I
          (flapperTendScratchMem (flapperTendIdWord I) mem)) =
        UInt256.ofNat 128 := by
    unfold flapperTendRefundCallMemFrom
    exact flapperTendMoveCallMemFrom_mload64
      (UInt256.ofNat I.source.val) (flapperTendGuyWord σ I)
      (flapperTendBidWord σ I) (flapperTendScratchMem (flapperTendIdWord I) mem)
      hscratch hread
  have hcallFromExplicit :
      memLoad (UInt256.ofNat 64)
        ((storageRead I.codeOwner σ
              (flapperTendBaseSlot (flapperTendIdWord I))).toByteArray.write 0
          ((solcAddrMask.land
                (storageRead I.codeOwner σ
                  (flapperTendBaseSlot (flapperTendIdWord I) + UInt256.ofNat 2))).toByteArray.write
            0
            ((UInt256.ofNat I.source.val).toByteArray.write 0
              (((UInt256.ofNat 3140843579).shiftLeft (UInt256.ofNat 224)).toByteArray.write
                0
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32)
                128 32)
              132 32)
            164 32)
          196 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendRefundCallMemFrom, flapperTendMoveCallMemFrom,
      flapperDealMoveSelectorWord, flapperYankMoveSelectorWord, flapperTendBidWord,
      flapperDealBidWord, flapperYankBidWord, flapperTendGuyWord, flapperDealGuyWord,
      flapperYankGuyWord, flapperTendPackedWord, flapperDealPackedWord,
      flapperYankPackedWord, flapperAddressMask_eq_solcAddrMask, u256_land_comm,
      hbaseRaw, hhashRaw,
      show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) = solcAddrMask by decide,
      show (UInt256.ofNat 128).toNat = 128 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide] using
      hcallFrom
  have hcallFromRaw :
      memLoad (UInt256.ofNat 64)
          (flapperRuntimeBlocks.flapperRuntime_block_2433_memory
            (ee := I) (mem := mem) (σ := σ) (x2 := flapperTendIdWord I)) =
        UInt256.ofNat 128 := by
    rw [hcallMem]
    exact hcallFrom
  simp [flapperRuntimeBlocks.flapperRuntime_block_2433_stack,
    flapperRuntimeBlocks.flapperRuntime_block_2433_memory, hbaseRaw, hhashRaw,
    hcallFromRaw, hcallFromExplicit, flapperTendMoveCallRest, flapperTendBidWord,
    flapperDealBidWord, flapperYankBidWord, flapperTendGuyWord, flapperDealGuyWord, flapperYankGuyWord,
    flapperTendPackedWord, flapperDealPackedWord, flapperYankPackedWord,
    flapperTendGemWord, flapperYankGemWord, flapperAddressMask_eq_solcAddrMask,
    u256_land_comm,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) =
        UInt256.ofNat 0 by decide,
    show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem flapperTendRuntimePayCallMem_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem) = UInt256.ofNat 128) :
    flapperRuntimeBlocks.flapperRuntime_block_2598_memory
        (ee := I) (mem := mem) (σ := σ)
        (x0 := flapperTendBidArgWord I) (x2 := flapperTendIdWord I) =
      flapperTendPayCallMemFrom σ I
        (flapperTendScratchMem (flapperTendIdWord I) mem) := by
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot, flapperTendScratchMem,
      flapperDealScratchMem, show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  simp [flapperRuntimeBlocks.flapperRuntime_block_2598_memory,
    flapperTendPayCallMemFrom, flapperTendMoveCallMemFrom, flapperTendScratchMem,
    flapperDealScratchMem, hbaseRaw, hhashRaw, flapperTendPayAmtWord,
    flapperTendBidWord, flapperDealBidWord, flapperYankBidWord,
    flapperAddressMask_eq_solcAddrMask,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem flapperTendRuntimePayCallStack_eq_from
    (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) (mem : ByteArray)
    (hscratch : 96 ≤ (flapperTendScratchMem (flapperTendIdWord I) mem).size)
    (hread : (flapperTendScratchMem (flapperTendIdWord I) mem).readWithPadding
      64 32 = UInt256.toByteArray (UInt256.ofNat 128)) :
    flapperRuntimeBlocks.flapperRuntime_block_2598_stack
        (ee := I) (mem := mem) (σ := σ)
        (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
        (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel]) =
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel) := by
  have h64 : (UInt256.ofNat 64).toNat <
      (flapperTendScratchMem (flapperTendIdWord I) mem).size := by
    rw [show (UInt256.ofNat 64).toNat = 64 by decide]
    omega
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem) = UInt256.ofNat 128 :=
    by
      unfold memLoad
      exact mloadWordValue_of_readWithPadding h64 hread
  have hbaseRaw :
      memLoad (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using hbase
  have hhashRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot, flapperTendScratchMem,
      flapperDealScratchMem, show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  have hcallMem :
      flapperRuntimeBlocks.flapperRuntime_block_2598_memory
          (ee := I) (mem := mem) (σ := σ)
          (x0 := flapperTendBidArgWord I) (x2 := flapperTendIdWord I) =
        flapperTendPayCallMemFrom σ I
          (flapperTendScratchMem (flapperTendIdWord I) mem) :=
    flapperTendRuntimePayCallMem_eq_from σ I mem hbase
  have hcallFrom :
      memLoad (UInt256.ofNat 64)
        (flapperTendPayCallMemFrom σ I
          (flapperTendScratchMem (flapperTendIdWord I) mem)) =
        UInt256.ofNat 128 := by
    unfold flapperTendPayCallMemFrom
    exact flapperTendMoveCallMemFrom_mload64
      (UInt256.ofNat I.source.val) (UInt256.ofNat I.codeOwner.val)
      (flapperTendPayAmtWord σ I) (flapperTendScratchMem (flapperTendIdWord I) mem)
      hscratch hread
  have hcallFromExplicit :
      memLoad (UInt256.ofNat 64)
        (((flapperTendBidArgWord I).sub
              (storageRead I.codeOwner σ
                (flapperTendBaseSlot (flapperTendIdWord I)))).toByteArray.write
          0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            ((UInt256.ofNat I.source.val).toByteArray.write 0
              (((UInt256.ofNat 3140843579).shiftLeft (UInt256.ofNat 224)).toByteArray.write
                0
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 mem 0 32) 32 32)
                128 32)
              132 32)
            164 32)
          196 32) =
        UInt256.ofNat 128 := by
    simpa [flapperTendPayCallMemFrom, flapperTendMoveCallMemFrom,
      flapperDealMoveSelectorWord, flapperYankMoveSelectorWord, flapperTendPayAmtWord,
      flapperTendBidWord, flapperDealBidWord, flapperYankBidWord, hbaseRaw, hhashRaw,
      show (UInt256.ofNat 128).toNat = 128 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
      show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide] using
      hcallFrom
  have hcallFromRaw :
      memLoad (UInt256.ofNat 64)
          (flapperRuntimeBlocks.flapperRuntime_block_2598_memory
            (ee := I) (mem := mem) (σ := σ)
            (x0 := flapperTendBidArgWord I) (x2 := flapperTendIdWord I)) =
        UInt256.ofNat 128 := by
    rw [hcallMem]
    exact hcallFrom
  simp [flapperRuntimeBlocks.flapperRuntime_block_2598_stack,
    flapperRuntimeBlocks.flapperRuntime_block_2598_memory, hbaseRaw, hhashRaw,
    hcallFromRaw, hcallFromExplicit, flapperTendMoveCallRest, flapperTendPayAmtWord,
    flapperTendBidWord, flapperDealBidWord, flapperYankBidWord,
    flapperTendGemWord, flapperYankGemWord, flapperAddressMask_eq_solcAddrMask,
    show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show (UInt256.sub
        (UInt256.ofNat 1461501637330902918203684832716283019655932542976)
        (UInt256.ofNat 1)) = solcAddrMask by decide,
    show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) =
        UInt256.ofNat 0 by decide,
    show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
    show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem decodeScalarWordsWithMode_uint256_uint256_uint256_ok {mode : DecodeMode}
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeScalarWordsWithMode? mode [abiUInt256, abiUInt256, abiUInt256] bytes 0 =
      some
        [ .int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
          .int (Int.ofNat
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
          .int (Int.ofNat
            (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := mode) (bytes := bytes) (start := 0) (by simpa using hlen0)]
  simp only [Option.bind, bind, Nat.zero_add]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := mode) (bytes := bytes) (start := 32) hlen32]
  simp only [List.drop_zero, Option.bind, bind]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := mode) (bytes := bytes) (start := 64) hlen64]

theorem decodeScalarWordsWithMode_uint256_uint256_uint256_none_short {mode : DecodeMode}
    {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWordsWithMode? mode [abiUInt256, abiUInt256, abiUInt256] bytes 0 = none := by
  by_cases hlen0 : 32 ≤ bytes.length
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    by_cases hlen32 : 64 ≤ bytes.length
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      simp only [decodeScalarWordsWithMode?]
      rw [decodeScalarWordWithMode_uint256_ok
        (mode := mode) (bytes := bytes) (start := 0) (by simpa using htake0)]
      simp only [Option.bind, bind, Nat.zero_add]
      rw [decodeScalarWordWithMode_uint256_ok
        (mode := mode) (bytes := bytes) (start := 32) htake32]
      simp only [List.drop_zero, Option.bind, bind]
      rw [decodeScalarWordWithMode_uint256_none_short
        (mode := mode) (bytes := bytes) (start := 64) htake64n]
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
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

theorem flapperDecode_tend_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata =
      some (flapperTendLocals (flapperTendIdWord I)
        (flapperTendLotArgWord I) (flapperTendBidArgWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata =
    some (flapperTendLocals (flapperTendIdWord I)
      (flapperTendLotArgWord I) (flapperTendBidArgWord I))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.drop_drop, List.length_take, List.length_drop, htlen]
    omega
  have htake68 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.drop_drop, List.length_take, List.length_drop, htlen]
    omega
  have hword4 :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = flapperTendIdWord I := by
    simpa [flapperTendIdWord, flapperDealIdWord, flapperYankIdWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
        flapperTendLotArgWord I := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      flapperTendLotArgWord] using
      decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32) =
        flapperTendBidArgWord I := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      flapperTendBidArgWord] using
      decode_word_at_eq I.calldata 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ["id", "lot", "bid"])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [decodeScalarWordsWithMode_uint256_uint256_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4) htake36 htake68]
  change decodeCalldata.insertValues ["id", "lot", "bid"]
      [ .int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat) ]
      ∅ =
    some (flapperTendLocals (flapperTendIdWord I)
      (flapperTendLotArgWord I) (flapperTendBidArgWord I))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues, flapperTendLocals]

theorem flapperDecode_tend_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode
      (tendTransition.params.map Param.name)
      (transitionSignature tendTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id", "lot", "bid"]
      [abiUInt256, abiUInt256, abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ["id", "lot", "bid"])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [decodeScalarWordsWithMode_uint256_uint256_uint256_none_short
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (by rw [List.length_drop, htlen]; omega)]

theorem flapperDispatch_tend {cd : ByteArray}
    (hsel : ((⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some tendTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition])
    (post := [tickTransition, ttlTransition, vatTransition, wardsTransition,
      yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [flapperTendSelectorBytes]
    exact hsel

theorem flapperSelectorDispatch_tend {cd : ByteArray}
    (hsel : ((⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some tendTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList]
  rw [show contract.transitions =
      [begTransition, bidsTransition, cageTransition, dealTransition,
        denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
        kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition] ++
      tendTransition ::
      [tickTransition, ttlTransition, vatTransition, wardsTransition,
        yankTransition] by rfl]
  refine dispatchList_eq_some_of_split ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [flapperTendSelectorBytes]
    exact hsel

theorem flapperTendIntWordBeq_true (a b : UInt256) (h : a = b) :
    ((Value.int (Int.ofNat a.toNat)) == Value.int (Int.ofNat b.toNat)) = true := by
  subst b
  simp

theorem flapperTendIntWordBeq_false (a b : UInt256) (h : a ≠ b) :
    ((Value.int (Int.ofNat a.toNat)) == Value.int (Int.ofNat b.toNat)) = false := by
  cases hbeq : ((Value.int (Int.ofNat a.toNat)) == Value.int (Int.ofNat b.toNat))
  · rfl
  · exfalso
    apply h
    have hv := beq_iff_eq.mp hbeq
    injection hv with hint
    apply u256_inj
    exact Int.ofNat.inj hint

theorem flapperTendAddressZeroBeq_true (w : UInt256) (h : w = UInt256.ofNat 0) :
    ((Value.address (AccountAddress.ofNat w.toNat)) ==
      Value.address (AccountAddress.ofNat 0)) = true := by
  subst w
  decide

theorem flapperTendAddressZeroBeq_false (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) (h : w ≠ UInt256.ofNat 0) :
    ((Value.address (AccountAddress.ofNat w.toNat)) ==
      Value.address (AccountAddress.ofNat 0)) = false := by
  cases hbeq : ((Value.address (AccountAddress.ofNat w.toNat)) ==
      Value.address (AccountAddress.ofNat 0))
  · rfl
  · exfalso
    have hv := beq_iff_eq.mp hbeq
    injection hv with haddr
    exact flapperAccountAddress_ofNat_ne_zero_of_canonical hcanon h haddr

theorem flapperTendVarId_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.var "id") =
      .ok (.int (Int.ofNat id.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperTendLocals
  rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat))).insert
    "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
    (.int (Int.ofNat bid.toNat)) (by decide)]
  rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
    (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
  exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat))

theorem flapperTendVarLot_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.var "lot") =
      .ok (.int (Int.ofNat lot.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperTendLocals
  rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat))).insert
    "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "lot")
    (.int (Int.ofNat bid.toNat)) (by decide)]
  exact store_get_self ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
    "lot" (.int (Int.ofNat lot.toNat))

theorem flapperTendVarBid_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.var "bid") =
      .ok (.int (Int.ofNat bid.toNat)) := by
  apply flapperKickVarInt_eval
  unfold flapperTendLocals
  exact store_get_self
    (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat))).insert "lot"
      (.int (Int.ofNat lot.toNat))) "bid" (.int (Int.ofNat bid.toNat))

theorem flapperTendLiveGuard_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  exact flapperKickLiveGuard_eval_true evm (flapperTendLocals id lot bid)
    (by simp [flapperTendLocals]) hlive

theorem flapperTendLiveGuard_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (hlive : flapperTendLiveWordOfState evm ≠ UInt256.ofNat 1) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  exact flapperKickLiveGuard_eval_false evm (flapperTendLocals id lot bid)
    (by simp [flapperTendLocals]) hlive

theorem flapperTendBegStorage_eval_of_locals (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "beg" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage begRef) =
      .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "beg", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm begRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, begRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨4⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256]
  simp [flapperTendBegWordOfState,
    show (⟨4⟩ : UInt256) = UInt256.ofNat 4 by decide]

theorem flapperTendTtlStorage_eval_of_locals (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "ttl" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ttlRef) =
      .ok (.int (Int.ofNat (flapperTendTtlWordOfState evm).toNat)) := by
  let er : EvaledStorageRef := { base := "ttl", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm ttlRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint48St]
  have hloc : config.storage.layout er =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨0, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint48_offset0]
  simp [flapperTendTtlWordOfState,
    show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide, u256_land_comm]

theorem flapperTendGemStorage_eval_of_locals (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "gem" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat (flapperTendGemWordOfState evm).toNat)) := by
  simpa [flapperTendGemWordOfState] using
    flapperDealGem_eval_of_base evm locals hbase

theorem flapperTendBidStorage_eval_of_locals (evm : EVM.State) (locals : Store)
    (id : UInt256)
    (hbase : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herBid :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "bid") = .ok erBid := by
    simp [erBid, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperTendBaseSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperTendBaseSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herBid) (hty := htyBid) (hloc := hlocBid),
    flapperStorageLocLoad_uint256]
  simp [flapperTendBidWordOfState, flapperDealBidWordOfState,
    flapperYankBidWordOfState, flapperTendBaseSlot, flapperDealBaseSlot]

theorem flapperTendGuyStorage_eval_of_locals (evm : EVM.State) (locals : Store)
    (id : UInt256)
    (hbase : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat
        (flapperTendGuyWordOfState evm id).toNat)) := by
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herGuy :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyGuy : storageTypeAt? contract.storage erGuy =
      some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperTendPackedSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := herGuy) (hty := htyGuy) (hloc := hlocGuy),
    flapperStorageLocLoad_address]
  simp [flapperTendGuyWordOfState, flapperDealGuyWordOfState,
    flapperYankGuyWordOfState, flapperDealPackedWordOfState,
    flapperYankPackedWordOfState, flapperTendPackedSlot, flapperDealPackedSlot,
    flapperYankPackedSlot, flapperAddressMask_eq_solcAddrMask]

theorem flapperTendNow48_eval (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (flapperTendNowWordOfState evm).toNat)) := by
  simpa [flapperTendNowWordOfState, flapperTendTimestampWordOfState,
    flapperDealTimestampWordOfState, flapperTickNowWordOfState,
    flapperTickTimestampWordOfState] using
    flapperTickNow48_eval evm locals

theorem flapperTendNewTic_eval (evm : EVM.State) (locals : Store)
    (hbaseTtl : locals.get? "ttl" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
      .ok (.int (Int.ofNat (flapperTendNewTicWordOfState evm).toNat)) := by
  let nowWord := flapperTendNowWordOfState evm
  let ttlWord := flapperTendTtlWordOfState evm
  have httlLt : ttlWord.toNat < 2 ^ 48 := by
    simpa [ttlWord, flapperTendTtlWordOfState] using
      flapperUint48Word_lt
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
  have hmod :
      (Int.ofNat nowWord.toNat + Int.ofNat ttlWord.toNat) % uint48Modulus =
        Int.ofNat (flapperTendNewTicWordOfState evm).toNat := by
    rw [uint48Modulus]
    change (Int.ofNat (nowWord.toNat + ttlWord.toNat)) %
        (Int.ofNat ((2 : Nat) ^ 48)) =
      Int.ofNat (flapperTendNewTicWordOfState evm).toNat
    calc
      (Int.ofNat (nowWord.toNat + ttlWord.toNat)) %
          (Int.ofNat ((2 : Nat) ^ 48)) =
        Int.ofNat ((nowWord.toNat + ttlWord.toNat) % (2 : Nat) ^ 48) := by
          exact (Int.natCast_emod (nowWord.toNat + ttlWord.toNat)
            ((2 : Nat) ^ 48)).symm
      _ = Int.ofNat (flapperTendNewTicWordOfState evm).toNat := by
        exact congrArg Int.ofNat
          (by
            simpa [nowWord, ttlWord, flapperTendNowWordOfState,
              flapperTendNewTicWordOfState] using
              flapperUint48Low_add_mod
                (flapperTendTimestampWordOfState evm)
                (flapperTendTtlWordOfState evm) httlLt)
  have hnonzero : uint48Modulus ≠ 0 := by
    norm_num [uint48Modulus]
  simp only [wrap48, evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [flapperTendNow48_eval evm locals]
  have hTtlEval := flapperTendTtlStorage_eval_of_locals evm locals hbaseTtl
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTtlEval
  rw [hTtlEval]
  change (if uint48Modulus = 0 then EvalResult.revert
    else EvalResult.ok (Value.int
      ((Int.ofNat nowWord.toNat + Int.ofNat ttlWord.toNat) % uint48Modulus))) =
    EvalResult.ok (Value.int (Int.ofNat (flapperTendNewTicWordOfState evm).toNat))
  rw [if_neg hnonzero, hmod]

theorem flapperTendSourceWord_toNat (addr : AccountAddress) :
    (UInt256.ofNat addr.val).toNat = addr.val := by
  have hword : addr.val < UInt256.size := by
    exact lt_of_lt_of_le addr.isLt (by decide)
  simpa using ulit_toNat' addr.val hword

theorem flapperTendSourceWord_canonical (addr : AccountAddress) :
    (UInt256.ofNat addr.val).toNat < EVM.addressModulus := by
  rw [flapperTendSourceWord_toNat]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using addr.isLt

theorem flapperTendAccountAddress_ofNat_eq_of_canonical {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus)
    (hb : b.toNat < EVM.addressModulus)
    (haddr : AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat) :
    a = b := by
  apply u256_inj
  have hval := congrArg Fin.val haddr
  have hmod : a.toNat % AccountAddress.size = b.toNat % AccountAddress.size := by
    simpa [AccountAddress.ofNat, Fin.ofNat] using hval
  have haLt : a.toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using ha
  have hbLt : b.toNat < AccountAddress.size := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hb
  simpa [Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] using hmod

theorem flapperTendGemExtGuard_true_of_locals (evm : EVM.State)
    (locals : Store)
    (hbaseGem : locals.get? "gem" = none)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) ≠
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let targetWord := flapperTendGemWordOfState evm
  have hreceiver := flapperTendGemStorage_eval_of_locals evm locals hbaseGem
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

theorem flapperTendGemExtGuard_false_of_locals (evm : EVM.State)
    (locals : Store)
    (hbaseGem : locals.get? "gem" = none)
    (hcodeSize :
      extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) =
        UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let targetWord := flapperTendGemWordOfState evm
  have hreceiver := flapperTendGemStorage_eval_of_locals evm locals hbaseGem
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

theorem flapperTendRefundArgs_eval_of_locals (evm : EVM.State)
    (locals : Store) (id : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
      .ok [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (flapperTendGuyWordOfState evm id).toNat),
        .int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)] := by
  have hGuyEval :=
    flapperTendGuyStorage_eval_of_locals evm locals id hbaseBids hgetId
  have hBidEval :=
    flapperTendBidStorage_eval_of_locals evm locals id hbaseBids hgetId
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval hBidEval
  simp only [evalExprs?, evalExpr?, sender, envValue, EvalResult.bind, bind, pure]
  rw [hGuyEval, hBidEval]

theorem flapperTendPayAmt_eval_of_locals (evm : EVM.State)
    (locals : Store) (id bid : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hgetBid : locals.get? "bid" = some (.int (Int.ofNat bid.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
        (wrap256 (.binary .sub (.var "bid")
          (.storage (bidsF (.var "id") "bid")))) =
      .ok (.int (Int.ofNat (flapperTendPayAmtWordOfState evm id bid).toNat)) := by
  let oldBid := flapperTendBidWordOfState evm id
  have hBidVar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    unfold evalExpr?
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "bid") =
      .ok (.int (Int.ofNat bid.toNat))
    rw [hgetBid]
    rfl
  have hOldBidEval :=
    flapperTendBidStorage_eval_of_locals evm locals id hbaseBids hgetId
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hBidVar hOldBidEval
  have hmod :
      (Int.ofNat bid.toNat - Int.ofNat oldBid.toNat) % wordModulus =
        Int.ofNat (UInt256.sub bid oldBid).toNat := by
    by_cases hle : oldBid.toNat ≤ bid.toNat
    · have hsubNat :
          (UInt256.sub bid oldBid).toNat = bid.toNat - oldBid.toNat :=
        usub_toNat (a := bid) (b := oldBid) hle
      have hdiffLt : bid.toNat - oldBid.toNat < UInt256.size :=
        lt_of_le_of_lt (Nat.sub_le bid.toNat oldBid.toNat) bid.val.isLt
      have hsubInt :
          Int.ofNat bid.toNat - Int.ofNat oldBid.toNat =
            Int.ofNat (bid.toNat - oldBid.toNat) := by
        exact (Int.ofNat_sub hle).symm
      rw [hsubInt]
      rw [wordModulus]
      change (Int.ofNat (bid.toNat - oldBid.toNat)) %
          Int.ofNat ((2 : Nat) ^ 256) =
        Int.ofNat (UInt256.sub bid oldBid).toNat
      calc
        (Int.ofNat (bid.toNat - oldBid.toNat)) %
            Int.ofNat ((2 : Nat) ^ 256) =
          Int.ofNat ((bid.toNat - oldBid.toNat) % (2 : Nat) ^ 256) := by
            exact (Int.natCast_emod (bid.toNat - oldBid.toNat)
              ((2 : Nat) ^ 256)).symm
        _ = Int.ofNat (UInt256.sub bid oldBid).toNat := by
          rw [Nat.mod_eq_of_lt (by simpa [UInt256.size] using hdiffLt)]
          rw [← hsubNat]
    · have hlt : bid.toNat < oldBid.toNat := Nat.lt_of_not_ge hle
      have hsubNat :
          (UInt256.sub bid oldBid).toNat =
            UInt256.size + bid.toNat - oldBid.toNat :=
        usub_toNat_underflow (a := bid) (b := oldBid) hlt
      have hold : oldBid.toNat < UInt256.size := oldBid.val.isLt
      have hleSum : oldBid.toNat ≤ UInt256.size + bid.toNat := by omega
      rw [wordModulus]
      change (Int.ofNat bid.toNat - Int.ofNat oldBid.toNat) %
          Int.ofNat ((2 : Nat) ^ 256) =
        Int.ofNat (UInt256.sub bid oldBid).toNat
      rw [Int.emod_eq_add_self_emod]
      rw [Int.emod_eq_of_lt]
      · rw [hsubNat]
        calc
          Int.ofNat bid.toNat - Int.ofNat oldBid.toNat +
              Int.ofNat ((2 : Nat) ^ 256) =
            Int.ofNat (UInt256.size + bid.toNat) - Int.ofNat oldBid.toNat := by
              simp [UInt256.size]
              ring
          _ = Int.ofNat ((UInt256.size + bid.toNat) - oldBid.toNat) := by
            exact (Int.ofNat_sub hleSum).symm
      · simp [UInt256.size] at hold ⊢
        omega
      · simp [UInt256.size] at hold ⊢
        omega
  have hnonzero : wordModulus ≠ 0 := by
    norm_num [wordModulus]
  simp only [wrap256, evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hBidVar, hOldBidEval]
  change (if wordModulus = 0 then EvalResult.revert
    else EvalResult.ok
      (Value.int ((Int.ofNat bid.toNat - Int.ofNat oldBid.toNat) %
        wordModulus))) =
    EvalResult.ok
      (Value.int (Int.ofNat (flapperTendPayAmtWordOfState evm id bid).toNat))
  rw [if_neg hnonzero, hmod]
  simp [oldBid, flapperTendPayAmtWordOfState]

theorem flapperTendPayArgs_eval_of_locals (evm : EVM.State)
    (locals : Store) (id bid : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hgetBid : locals.get? "bid" = some (.int (Int.ofNat bid.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
        [sender, thisAddr,
          wrap256 (.binary .sub (.var "bid")
            (.storage (bidsF (.var "id") "bid")))] =
      .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
        .int (Int.ofNat (flapperTendPayAmtWordOfState evm id bid).toNat)] := by
  have hPay := flapperTendPayAmt_eval_of_locals evm locals id bid
    hbaseBids hgetId hgetBid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hPay
  simp only [evalExprs?, evalExpr?, sender, thisAddr, envValue, EvalResult.bind,
    bind, pure]
  rw [hPay]

theorem flapperTendSenderNeGuy_eval_false_of_locals (evm : EVM.State)
    (locals : Store) (id : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hsame :
      UInt256.ofNat evm.executionEnv.source.val =
        flapperTendGuyWordOfState evm id) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
      .ok (.bool false) := by
  let guy := flapperTendGuyWordOfState evm id
  have hGuyEval :=
    flapperTendGuyStorage_eval_of_locals evm locals id hbaseBids hgetId
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval
  have haddr : evm.executionEnv.source = AccountAddress.ofNat guy.toNat := by
    apply Fin.ext
    have hnat : evm.executionEnv.source.val = guy.toNat := by
      rw [← flapperTendSourceWord_toNat evm.executionEnv.source, hsame]
    have hguyLt : guy.toNat < AccountAddress.size := by
      have hguyCanon : guy.toNat < EVM.addressModulus := by
        simpa [guy, flapperTendGuyWordOfState, flapperDealGuyWordOfState,
          flapperYankGuyWordOfState, flapperDealPackedWordOfState,
          flapperYankPackedWordOfState] using
          solcAddrMask_result_canonical (flapperYankPackedWordOfState evm id)
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hguyCanon
    simp [AccountAddress.ofNat, hnat, Nat.mod_eq_of_lt hguyLt]
  simp only [evalExpr?, sender, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuyEval]
  simp [guy, haddr]

theorem flapperTendSenderNeGuy_eval_true_of_locals (evm : EVM.State)
    (locals : Store) (id : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hdiff :
      UInt256.ofNat evm.executionEnv.source.val ≠
        flapperTendGuyWordOfState evm id) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
      .ok (.bool true) := by
  let sourceWord := UInt256.ofNat evm.executionEnv.source.val
  let guy := flapperTendGuyWordOfState evm id
  have hGuyEval :=
    flapperTendGuyStorage_eval_of_locals evm locals id hbaseBids hgetId
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuyEval
  have hsourceAddr :
      AccountAddress.ofNat sourceWord.toNat = evm.executionEnv.source := by
    apply Fin.ext
    simp [sourceWord, AccountAddress.ofNat, flapperTendSourceWord_toNat]
  have hsourceCanon : sourceWord.toNat < EVM.addressModulus := by
    simpa [sourceWord] using flapperTendSourceWord_canonical evm.executionEnv.source
  have hguyCanon : guy.toNat < EVM.addressModulus := by
    simpa [guy, flapperTendGuyWordOfState, flapperDealGuyWordOfState,
      flapperYankGuyWordOfState, flapperDealPackedWordOfState,
      flapperYankPackedWordOfState] using
      solcAddrMask_result_canonical (flapperYankPackedWordOfState evm id)
  have haddrNe :
      evm.executionEnv.source ≠ AccountAddress.ofNat guy.toNat := by
    intro haddr
    apply hdiff
    have haddrWords :
        AccountAddress.ofNat sourceWord.toNat =
          AccountAddress.ofNat guy.toNat := by
      rw [hsourceAddr]
      exact haddr
    simpa [sourceWord, guy] using
      flapperTendAccountAddress_ofNat_eq_of_canonical hsourceCanon hguyCanon haddrWords
  have hvalueNe :
      Value.address evm.executionEnv.source ≠
        Value.address (AccountAddress.ofNat guy.toNat) := by
    intro h
    injection h with haddr
    exact haddrNe haddr
  have hbeq :
      ((Value.address evm.executionEnv.source) ==
          Value.address (AccountAddress.ofNat guy.toNat)) = false := by
    cases h :
        ((Value.address evm.executionEnv.source) ==
          Value.address (AccountAddress.ofNat guy.toNat))
    · rfl
    · exact False.elim (hvalueNe (beq_iff_eq.mp h))
  simp only [evalExpr?, sender, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuyEval]
  simp [guy, hbeq]

theorem flapperTendTicLocal_eval (evm : EVM.State) (locals : Store)
    (tic : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocalsTic locals tic }
        evm (.var "tic_") =
      .ok (.int (Int.ofNat tic.toNat)) := by
  unfold evalExpr?
  change EvalResult.ofOption EvalError.unboundVariable
      ((flapperTendLocalsTic locals tic).get? "tic_") =
    .ok (.int (Int.ofNat tic.toNat))
  unfold flapperTendLocalsTic
  rw [store_get_self]
  rfl

theorem flapperTendTicCheckedGuard_eval_true (evm : EVM.State)
    (locals : Store) (tic : UInt256)
    (hwrap : ¬ tic.toNat < (flapperTendNowWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocalsTic locals tic }
        evm (.binary .ge (.var "tic_") now48) =
      .ok (.bool true) := by
  have hTicLocal := flapperTendTicLocal_eval evm locals tic
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicLocal
  have hNowEval := flapperTendNow48_eval evm (flapperTendLocalsTic locals tic)
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicLocal, hNowEval]
  have hgeNat : (flapperTendNowWordOfState evm).toNat ≤ tic.toNat := by
    omega
  simpa [evalBinaryOp?] using hgeNat

theorem flapperTendTicCheckedGuard_eval_false (evm : EVM.State)
    (locals : Store) (tic : UInt256)
    (hwrap : tic.toNat < (flapperTendNowWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocalsTic locals tic }
        evm (.binary .ge (.var "tic_") now48) =
      .ok (.bool false) := by
  have hTicLocal := flapperTendTicLocal_eval evm locals tic
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicLocal
  have hNowEval := flapperTendNow48_eval evm (flapperTendLocalsTic locals tic)
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicLocal, hNowEval]
  have hnotNat : ¬ (flapperTendNowWordOfState evm).toNat ≤ tic.toNat := by
    omega
  simpa [evalBinaryOp?] using hnotNat

theorem flapperTendAssignBid_of_locals (evm : EVM.State) (locals : Store)
    (id bid : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    assignStorageRef? config
      { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat bid.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendBaseSlot id) bid) := by
  let solm : Frame := { contract := contract, locals := locals }
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
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
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperTendBaseSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperTendBaseSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (flapperTendBaseSlot id))
          (.int (Int.ofNat bid.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendBaseSlot id) bid) := by
    simpa [wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (flapperTendBaseSlot id) bid
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "bid")
      (.int (Int.ofNat bid.toNat)) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperTendBaseSlot id) bid)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbaseBids) (her := herBid) (hty := htyBid) (hloc := hlocBid)
    (hstore := hstore)

theorem flapperTendAssignGuy_of_locals (evm : EVM.State) (locals : Store)
    (id : UInt256)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    assignStorageRef? config
      { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "guy") (.address evm.executionEnv.source) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendPackedSlot id)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperTendPackedSlot id))
            (UInt256.ofNat evm.executionEnv.source.val))) := by
  let solm : Frame := { contract := contract, locals := locals }
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herGuy : evalStorageRef config solm evm
      (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [solm, erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyGuy : storageTypeAt? contract.storage erGuy = some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperTendPackedSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    change addrLoc
        (uInt256OfByteArray (ffi.KEC
          (id.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2) =
      addrLoc (solcMappingSlot (UInt256.ofNat 1) id + UInt256.ofNat 2)
    rfl
  have hstore :
      storageLocStore evm (addrLoc (flapperTendPackedSlot id))
          (.address evm.executionEnv.source) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendPackedSlot id)
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (flapperTendPackedSlot id))
            (UInt256.ofNat evm.executionEnv.source.val))) :=
    flapperKickStorageLocStore_address_source evm (flapperTendPackedSlot id)
  change assignStorageRef? config solm evm .storage (bidsF (.var "id") "guy")
      (.address evm.executionEnv.source) =
    .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (flapperTendPackedSlot id)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (flapperTendPackedSlot id))
        (UInt256.ofNat evm.executionEnv.source.val)))
  exact assignStorageRef_storage_scalar_value (ty := .elem .address)
    (hbase := hbaseBids) (her := herGuy) (hty := htyGuy) (hloc := hlocGuy)
    (hscalar := by trivial) (hstore := hstore)

theorem flapperTendAssignTic_of_locals (evm : EVM.State) (locals : Store)
    (id tic : UInt256)
    (hclean : UInt256.land tic flapperUint48Mask = tic)
    (hbaseBids : locals.get? "bids" = none)
    (hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    assignStorageRef? config
      { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "tic") (.int (Int.ofNat tic.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendPackedSlot id)
          (flapperTendPackedTicWord
            (flapperTendPackedWordOfState evm id) tic)) := by
  let solm : Frame := { contract := contract, locals := locals }
  let erTic : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "tic"] }
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herTic : evalStorageRef config solm evm
      (bidsF (.var "id") "tic") = .ok erTic := by
    simp [solm, erTic, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyTic : storageTypeAt? contract.storage erTic =
      some (.elem (.int uint48Int)) := by
    simp [erTic, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocTic : config.storage.layout erTic =
      fun _ => some (uint48Loc (flapperTendPackedSlot id)
        ⟨20, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTic,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (id.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) id + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide)
    rfl
  have hstore :
      storageLocStore evm
          (uint48Loc (flapperTendPackedSlot id) ⟨20, by decide⟩ (by decide))
          (.int (Int.ofNat tic.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTendPackedSlot id)
          (flapperTendPackedTicWord (flapperTendPackedWordOfState evm id) tic)) := by
    simpa [flapperTendPackedWordOfState, flapperDealPackedWordOfState,
      flapperYankPackedWordOfState, hclean] using
      flapperStorageLocStore_uint48_offset20 evm (flapperTendPackedSlot id) tic
  simpa [solm] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
      (hbase := hbaseBids) (her := herTic) (hty := htyTic) (hloc := hlocTic)
      (hstore := hstore)

theorem flapperTendMul256_eval_ok {evm : EVM.State} {frame : Frame}
    {xExpr yExpr : Expr} {x y : UInt256}
    (hx : evalExpr? config frame evm xExpr =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config frame evm yExpr =
      .ok (.int (Int.ofNat y.toNat)))
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config frame evm (mul256 xExpr yExpr) =
      .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
  have hprod :
      Int.ofNat x.toNat * Int.ofNat y.toNat =
        Int.ofNat (x.toNat * y.toNat) := by
    norm_num
  have hmulNat : (UInt256.mul x y).toNat = x.toNat * y.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  have hleft :
      decide (Int.ofNat x.toNat * Int.ofNat y.toNat < 0) = false := by
    exact decide_eq_false (by
      intro hneg
      have hnonneg : 0 ≤ Int.ofNat x.toNat * Int.ofNat y.toNat := by
        exact mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      omega)
  have hright :
      decide (Int.ofNat x.toNat * Int.ofNat y.toNat ≥ (2 : Int) ^ 256) = false := by
    exact decide_eq_false (by
      intro hge
      have hfitInt :
          Int.ofNat (x.toNat * y.toNat) < (2 : Int) ^ 256 := by
        exact Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit)
      rw [hprod] at hge
      omega)
  simp only [mul256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hx, hy]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [hleft, hright]
  simp [hprod, hmulNat]

theorem flapperTendMul256_eval_revert {evm : EVM.State} {frame : Frame}
    {xExpr yExpr : Expr} {x y : UInt256}
    (hx : evalExpr? config frame evm xExpr =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config frame evm yExpr =
      .ok (.int (Int.ofNat y.toNat)))
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? config frame evm (mul256 xExpr yExpr) = .revert := by
  have hprod :
      Int.ofNat x.toNat * Int.ofNat y.toNat =
        Int.ofNat (x.toNat * y.toNat) := by
    norm_num
  have hright :
      decide (Int.ofNat x.toNat * Int.ofNat y.toNat ≥ (2 : Int) ^ 256) = true := by
    exact decide_eq_true (by
      rw [hprod]
      exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  simp only [mul256, u256, uint256Int, evalExpr?, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hx, hy]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [hright]
  simp

theorem flapperTendVarInt_eval_of_get {evm : EVM.State} {locals : Store}
    {name : Ident} {word : UInt256}
    (hget : locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat word.toNat)) := by
  exact flapperKickVarInt_eval hget

theorem flapperTendEvalEqInt_true {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr} {x y : Int}
    (hlhs : evalExpr? config frame evm lhs = .ok (.int x))
    (hrhs : evalExpr? config frame evm rhs = .ok (.int y))
    (hxy : x = y) :
    evalExpr? config frame evm (.binary .eq lhs rhs) = .ok (.bool true) := by
  subst y
  unfold evalExpr?
  rw [hlhs, hrhs]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem flapperTendEvalEqInt_false {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr} {x y : Int}
    (hlhs : evalExpr? config frame evm lhs = .ok (.int x))
    (hrhs : evalExpr? config frame evm rhs = .ok (.int y))
    (hxy : x ≠ y) :
    evalExpr? config frame evm (.binary .eq lhs rhs) = .ok (.bool false) := by
  unfold evalExpr?
  rw [hlhs, hrhs]
  simp [EvalResult.bind, bind, evalBinaryOp?, hxy]

theorem flapperTendEvalGeInt_true {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr} {x y : Int}
    (hlhs : evalExpr? config frame evm lhs = .ok (.int x))
    (hrhs : evalExpr? config frame evm rhs = .ok (.int y))
    (hxy : y ≤ x) :
    evalExpr? config frame evm (.binary .ge lhs rhs) = .ok (.bool true) := by
  unfold evalExpr?
  rw [hlhs, hrhs]
  simp [EvalResult.bind, bind, evalBinaryOp?, hxy]

theorem flapperTendEvalGeInt_false {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr} {x y : Int}
    (hlhs : evalExpr? config frame evm lhs = .ok (.int x))
    (hrhs : evalExpr? config frame evm rhs = .ok (.int y))
    (hxy : ¬ y ≤ x) :
    evalExpr? config frame evm (.binary .ge lhs rhs) = .ok (.bool false) := by
  unfold evalExpr?
  rw [hlhs, hrhs]
  simp [EvalResult.bind, bind, evalBinaryOp?, hxy]

theorem flapperTendEvalDivInt {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr} {x y : Int}
    (hlhs : evalExpr? config frame evm lhs = .ok (.int x))
    (hrhs : evalExpr? config frame evm rhs = .ok (.int y))
    (hy : y ≠ 0) :
    evalExpr? config frame evm (.binary .div lhs rhs) =
      .ok (.int (x / y)) := by
  unfold evalExpr?
  rw [hlhs, hrhs]
  simp [EvalResult.bind, bind, evalBinaryOp?, hy]

theorem flapperTendEvalOr_true_left {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config frame evm lhs = .ok (.bool true)) :
    evalExpr? config frame evm (.binary .or lhs rhs) = .ok (.bool true) := by
  unfold evalExpr?
  rw [hlhs]
  rfl

theorem flapperTendEvalOr_true_right {evm : EVM.State} {frame : Frame}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config frame evm lhs = .ok (.bool false))
    (hrhs : evalExpr? config frame evm rhs = .ok (.bool true)) :
    evalExpr? config frame evm (.binary .or lhs rhs) = .ok (.bool true) := by
  unfold evalExpr?
  rw [hlhs, hrhs]
  rfl

theorem flapperTendCheckedMulGuard_eval_true {evm : EVM.State} {frame : Frame}
    {name : Ident} {xExpr yExpr : Expr} {x y : UInt256}
    (hget : frame.locals.get? name =
      some (.int (Int.ofNat (UInt256.mul x y).toNat)))
    (hx : evalExpr? config frame evm xExpr =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config frame evm yExpr =
      .ok (.int (Int.ofNat y.toNat)))
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config frame evm
        (.binary .or
          (.binary .eq yExpr (.intLit 0))
          (.binary .eq (.binary .div (.var name) yExpr) xExpr)) =
      .ok (.bool true) := by
  let lhs : Expr := .binary .eq yExpr (.intLit 0)
  let rhs : Expr := .binary .eq (.binary .div (.var name) yExpr) xExpr
  have hzeroEval :
      evalExpr? config frame evm (.intLit 0) = .ok (.int 0) := by
    unfold evalExpr?
    rfl
  by_cases hyZero : y = UInt256.ofNat 0
  · have hyEq : Int.ofNat y.toNat = 0 := by
      subst y
      decide
    have hLeft : evalExpr? config frame evm lhs = .ok (.bool true) :=
      flapperTendEvalEqInt_true hy hzeroEval hyEq
    simpa [lhs, rhs] using
      flapperTendEvalOr_true_left (frame := frame) (lhs := lhs) (rhs := rhs) hLeft
  · have hyNat : y.toNat ≠ 0 := by
      intro hzero
      exact hyZero (u256_inj hzero)
    have hyInt : Int.ofNat y.toNat ≠ 0 := Int.ofNat_ne_zero.mpr hyNat
    have hLeft : evalExpr? config frame evm lhs = .ok (.bool false) :=
      flapperTendEvalEqInt_false hy hzeroEval hyInt
    have hvar :
        evalExpr? config frame evm (.var name) =
      .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
      unfold evalExpr?
      rw [hget]
      rfl
    have hmulNat :
        (UInt256.mul x y).toNat = x.toNat * y.toNat := by
      rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
    have hdivInt :
        Int.ofNat (UInt256.mul x y).toNat / Int.ofNat y.toNat =
          Int.ofNat x.toNat := by
      rw [hmulNat]
      rw [show Int.ofNat (x.toNat * y.toNat) =
          Int.ofNat x.toNat * Int.ofNat y.toNat by norm_num]
      exact Int.mul_ediv_cancel (Int.ofNat x.toNat) hyInt
    have hDiv :
        evalExpr? config frame evm (.binary .div (.var name) yExpr) =
          .ok (.int (Int.ofNat x.toNat)) := by
      have hDivRaw := flapperTendEvalDivInt hvar hy hyInt
      rwa [hdivInt] at hDivRaw
    have hRight : evalExpr? config frame evm rhs = .ok (.bool true) :=
      flapperTendEvalEqInt_true hDiv hx rfl
    simpa [lhs, rhs] using
      flapperTendEvalOr_true_right (frame := frame) (lhs := lhs) (rhs := rhs)
        hLeft hRight

theorem flapperTendFloorGuard_eval_true (evm : EVM.State)
    (id lot bid bidOne begBid : UInt256)
    (hfloor : begBid.toNat ≤ bidOne.toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperTendLocalsBegBid id lot bid bidOne begBid } evm
        (.binary .ge (.var "bidOne") (.var "begBid")) =
      .ok (.bool true) := by
  let locals := flapperTendLocalsBegBid id lot bid bidOne begBid
  let frame : Frame := { contract := contract, locals := locals }
  have hgetBidOne : locals.get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
    unfold locals flapperTendLocalsBegBid
    rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
      (k := "begBid") (a := "bidOne")
      (.int (Int.ofNat begBid.toNat)) (by decide)]
    unfold flapperTendLocalsBidOne
    exact store_get_self (flapperTendLocals id lot bid) "bidOne"
      (.int (Int.ofNat bidOne.toNat))
  have hgetBegBid : locals.get? "begBid" =
      some (.int (Int.ofNat begBid.toNat)) := by
    unfold locals flapperTendLocalsBegBid
    exact store_get_self (flapperTendLocalsBidOne id lot bid bidOne) "begBid"
      (.int (Int.ofNat begBid.toNat))
  have hBidOne :
      evalExpr? config frame evm (.var "bidOne") =
        .ok (.int (Int.ofNat bidOne.toNat)) :=
    flapperTendVarInt_eval_of_get (evm := evm) hgetBidOne
  have hBegBid :
      evalExpr? config frame evm (.var "begBid") =
        .ok (.int (Int.ofNat begBid.toNat)) :=
    flapperTendVarInt_eval_of_get (evm := evm) hgetBegBid
  have hgeInt : Int.ofNat begBid.toNat ≤ Int.ofNat bidOne.toNat :=
    Int.ofNat_le.mpr hfloor
  simpa [frame, locals] using
    flapperTendEvalGeInt_true hBidOne hBegBid hgeInt

theorem flapperTendFloorGuard_eval_false (evm : EVM.State)
    (id lot bid bidOne begBid : UInt256)
    (hfloor : bidOne.toNat < begBid.toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperTendLocalsBegBid id lot bid bidOne begBid } evm
        (.binary .ge (.var "bidOne") (.var "begBid")) =
      .ok (.bool false) := by
  let locals := flapperTendLocalsBegBid id lot bid bidOne begBid
  let frame : Frame := { contract := contract, locals := locals }
  have hgetBidOne : locals.get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
    unfold locals flapperTendLocalsBegBid
    rw [store_get_ne (flapperTendLocalsBidOne id lot bid bidOne)
      (k := "begBid") (a := "bidOne")
      (.int (Int.ofNat begBid.toNat)) (by decide)]
    unfold flapperTendLocalsBidOne
    exact store_get_self (flapperTendLocals id lot bid) "bidOne"
      (.int (Int.ofNat bidOne.toNat))
  have hgetBegBid : locals.get? "begBid" =
      some (.int (Int.ofNat begBid.toNat)) := by
    unfold locals flapperTendLocalsBegBid
    exact store_get_self (flapperTendLocalsBidOne id lot bid bidOne) "begBid"
      (.int (Int.ofNat begBid.toNat))
  have hBidOne :
      evalExpr? config frame evm (.var "bidOne") =
        .ok (.int (Int.ofNat bidOne.toNat)) :=
    flapperTendVarInt_eval_of_get (evm := evm) hgetBidOne
  have hBegBid :
      evalExpr? config frame evm (.var "begBid") =
        .ok (.int (Int.ofNat begBid.toNat)) :=
    flapperTendVarInt_eval_of_get (evm := evm) hgetBegBid
  have hnotGeInt : ¬ Int.ofNat begBid.toNat ≤ Int.ofNat bidOne.toNat := by
    intro hge
    have hgeNat : begBid.toNat ≤ bidOne.toNat := Int.ofNat_le.mp hge
    omega
  simpa [frame, locals] using
    flapperTendEvalGeInt_false hBidOne hBegBid hnotGeInt

theorem flapperTendLotStorage_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (flapperTendLotWordOfState evm id).toNat)) := by
  let locals := flapperTendLocals id lot bid
  let erLot : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "lot"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTendLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    simpa [locals] using
      (show (flapperTendLocals id lot bid).get? "id" =
        some (.int (Int.ofNat id.toNat)) from by
        unfold flapperTendLocals
        rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          |>.insert "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
          (.int (Int.ofNat bid.toNat)) (by decide)]
        rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
        exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat)))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herLot :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "lot") = .ok erLot := by
    simp [erLot, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyLot : storageTypeAt? contract.storage erLot =
      some (.elem (.int uint256Int)) := by
    simp [erLot, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocLot : config.storage.layout erLot =
      fun _ => some (wordLoc (flapperTendBaseSlot id + UInt256.ofNat 1)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erLot,
      bidsBase, mapSlot, solcMappingSlot, flapperTendBaseSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herLot) (hty := htyLot) (hloc := hlocLot),
    flapperStorageLocLoad_uint256]
  simp [locals, flapperTendLotWordOfState, flapperDealLotWordOfState,
    flapperTendBaseSlot]

theorem flapperTendBidStorage_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
  let locals := flapperTendLocals id lot bid
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "bid"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTendLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    simpa [locals] using
      (show (flapperTendLocals id lot bid).get? "id" =
        some (.int (Int.ofNat id.toNat)) from by
        unfold flapperTendLocals
        rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          |>.insert "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
          (.int (Int.ofNat bid.toNat)) (by decide)]
        rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
        exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat)))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herBid :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "bid") = .ok erBid := by
    simp [erBid, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (flapperTendBaseSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot, flapperTendBaseSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase)
    (her := herBid) (hty := htyBid) (hloc := hlocBid),
    flapperStorageLocLoad_uint256]
  simp [locals, flapperTendBidWordOfState, flapperDealBidWordOfState,
    flapperYankBidWordOfState, flapperTendBaseSlot, flapperDealBaseSlot]

theorem flapperTendGuyStorage_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat
        (flapperTendGuyWordOfState evm id).toNat)) := by
  let locals := flapperTendLocals id lot bid
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "guy"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTendLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    simpa [locals] using
      (show (flapperTendLocals id lot bid).get? "id" =
        some (.int (Int.ofNat id.toNat)) from by
        unfold flapperTendLocals
        rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          |>.insert "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
          (.int (Int.ofNat bid.toNat)) (by decide)]
        rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
        exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat)))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herGuy :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "guy") = .ok erGuy := by
    simp [erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyGuy : storageTypeAt? contract.storage erGuy =
      some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc (flapperTendPackedSlot id)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    rfl
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase)
    (her := herGuy) (hty := htyGuy) (hloc := hlocGuy),
    flapperStorageLocLoad_address]
  simp [locals, flapperTendGuyWordOfState, flapperDealGuyWordOfState,
    flapperYankGuyWordOfState, flapperDealPackedWordOfState,
    flapperYankPackedWordOfState, flapperTendPackedSlot, flapperDealPackedSlot,
    flapperYankPackedSlot, flapperAddressMask_eq_solcAddrMask]

theorem flapperTendTicStorage_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (flapperTendTicWordOfState evm id).toNat)) := by
  let locals := flapperTendLocals id lot bid
  let erTic : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "tic"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTendLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    simpa [locals] using
      (show (flapperTendLocals id lot bid).get? "id" =
        some (.int (Int.ofNat id.toNat)) from by
        unfold flapperTendLocals
        rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          |>.insert "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
          (.int (Int.ofNat bid.toNat)) (by decide)]
        rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
        exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat)))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herTic :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "tic") = .ok erTic := by
    simp [erTic, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyTic : storageTypeAt? contract.storage erTic =
      some (.elem (.int uint48Int)) := by
    simp [erTic, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocTic : config.storage.layout erTic =
      fun _ => some (uint48Loc (flapperTendPackedSlot id)
        ⟨20, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTic,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (id.toByteArray ++ (UInt256.ofNat 1).toByteArray)) + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) id + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide)
    rfl
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase)
    (her := herTic) (hty := htyTic) (hloc := hlocTic),
    flapperStorageLocLoad_uint48_offset20]
  simp [locals, flapperTendTicWordOfState, flapperDealTicWordOfState,
    flapperDealPackedWordOfState, flapperYankPackedWordOfState,
    flapperTendPackedSlot, flapperDealPackedSlot, flapperYankPackedSlot]

theorem flapperTendEndStorage_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (flapperTendEndWordOfState evm id).toNat)) := by
  let locals := flapperTendLocals id lot bid
  let erEnd : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat id.toNat)), .field "end"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTendLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat id.toNat)) := by
    simpa [locals] using
      (show (flapperTendLocals id lot bid).get? "id" =
        some (.int (Int.ofNat id.toNat)) from by
        unfold flapperTendLocals
        rw [store_get_ne (((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          |>.insert "lot" (.int (Int.ofNat lot.toNat))) (k := "bid") (a := "id")
          (.int (Int.ofNat bid.toNat)) (by decide)]
        rw [store_get_ne ((∅ : Store).insert "id" (.int (Int.ofNat id.toNat)))
          (k := "lot") (a := "id") (.int (Int.ofNat lot.toNat)) (by decide)]
        exact store_get_self (∅ : Store) "id" (.int (Int.ofNat id.toNat)))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat id.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herEnd :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "end") = .ok erEnd := by
    simp [erEnd, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, hbase, hgetIdElem]
  have htyEnd : storageTypeAt? contract.storage erEnd =
      some (.elem (.int uint48Int)) := by
    simp [erEnd, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑id.toNat : Int)) = id := by
    simpa using keyValueToWord_uint256 id
  have hlocEnd : config.storage.layout erEnd =
      fun _ => some (uint48Loc (flapperTendPackedSlot id)
        ⟨26, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erEnd,
      bidsBase, mapSlot, solcMappingSlot, flapperTendPackedSlot,
      flapperTendBaseSlot, flapperDealPackedSlot, flapperDealBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (id.toByteArray ++ (UInt256.ofNat 1).toByteArray)) + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) id + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)
    rfl
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase)
    (her := herEnd) (hty := htyEnd) (hloc := hlocEnd),
    flapperStorageLocLoad_uint48_offset26]
  simp [locals, flapperTendEndWordOfState, flapperDealEndWordOfState,
    flapperDealPackedWordOfState, flapperYankPackedWordOfState,
    flapperTendPackedSlot, flapperDealPackedSlot, flapperYankPackedSlot]

theorem flapperTendZeroAddr_eval (evm : EVM.State) (id lot bid : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, evalExpr?, addrSt, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem flapperTendGuyNeZero_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
      .ok (.bool true) := by
  have hGuy := flapperTendGuyStorage_eval evm id lot bid
  have hZero := flapperTendZeroAddr_eval evm id lot bid
  have hcanon : (flapperTendGuyWordOfState evm id).toNat < EVM.addressModulus := by
    simpa [flapperTendGuyWordOfState, flapperDealGuyWordOfState,
      flapperYankGuyWordOfState, flapperDealPackedWordOfState,
      flapperYankPackedWordOfState, flapperAddressMask_eq_solcAddrMask] using
      solcAddrMask_result_canonical (flapperYankPackedWordOfState evm id)
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuy hZero
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuy, hZero]
  have hbeq := flapperTendAddressZeroBeq_false
    (flapperTendGuyWordOfState evm id) hcanon hguy
  simp [evalBinaryOp?, hbeq]

theorem flapperTendGuyNeZero_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (hguy : flapperTendGuyWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
      .ok (.bool false) := by
  have hGuy := flapperTendGuyStorage_eval evm id lot bid
  have hZero := flapperTendZeroAddr_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hGuy hZero
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGuy, hZero]
  have hbeq := flapperTendAddressZeroBeq_true
    (flapperTendGuyWordOfState evm id) hguy
  simp [evalBinaryOp?, hbeq]

theorem flapperTendTicGt_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (htic :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
      .ok (.bool true) := by
  have hTicEval := flapperTendTicStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  have hprop :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (flapperTendTicWordOfState evm id).toNat := by
    simpa [flapperTendTimestampWordOfState, flapperDealTimestampWordOfState] using htic
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp [envValue, hprop]

theorem flapperTendTicGt_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (htic :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
      .ok (.bool false) := by
  have hTicEval := flapperTendTicStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  have hprop :
      ¬ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (flapperTendTicWordOfState evm id).toNat := by
    intro hlt
    exact htic (by
      simpa [flapperTendTimestampWordOfState, flapperDealTimestampWordOfState] using hlt)
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp [envValue, hprop]

theorem flapperTendTicEqZero_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (htic : flapperTendTicWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool true) := by
  have hTicEval := flapperTendTicStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_true (flapperTendTicWordOfState evm id) htic]

theorem flapperTendTicEqZero_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (htic : flapperTendTicWordOfState evm id ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool false) := by
  have hTicEval := flapperTendTicStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_false (flapperTendTicWordOfState evm id) htic]

theorem flapperTendTimingGuard_eval_true_tic (evm : EVM.State)
    (id lot bid : UInt256)
    (htic :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  have hGt := flapperTendTicGt_eval_true evm id lot bid htic
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hGt
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGt]

theorem flapperTendTimingGuard_eval_true_zero (evm : EVM.State)
    (id lot bid : UInt256)
    (hticGt :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat)
    (hticZero : flapperTendTicWordOfState evm id = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool true) := by
  have hGt := flapperTendTicGt_eval_false evm id lot bid hticGt
  have hEq := flapperTendTicEqZero_eval_true evm id lot bid hticZero
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hGt hEq
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGt, hEq]

theorem flapperTendTimingGuard_eval_false (evm : EVM.State)
    (id lot bid : UInt256)
    (hticGt :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat)
    (hticZero : flapperTendTicWordOfState evm id ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
      .ok (.bool false) := by
  have hGt := flapperTendTicGt_eval_false evm id lot bid hticGt
  have hEq := flapperTendTicEqZero_eval_false evm id lot bid hticZero
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?] at hGt hEq
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hGt, hEq]

theorem flapperTendEndGt_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool true) := by
  have hEndEval := flapperTendEndStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (flapperTendEndWordOfState evm id).toNat := by
    simpa [flapperTendTimestampWordOfState, flapperDealTimestampWordOfState] using hend
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperTendEndGt_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (hend :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool false) := by
  have hEndEval := flapperTendEndStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      ¬ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (flapperTendEndWordOfState evm id).toNat := by
    intro hlt
    exact hend (by
      simpa [flapperTendTimestampWordOfState, flapperDealTimestampWordOfState] using hlt)
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperTendLotEq_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (hlot : lot = flapperTendLotWordOfState evm id) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
      .ok (.bool true) := by
  have hLotVar := flapperTendVarLot_eval evm id lot bid
  have hLotStorage := flapperTendLotStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLotVar hLotStorage
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLotVar, hLotStorage]
  have hbeq := flapperTendIntWordBeq_true lot
    (flapperTendLotWordOfState evm id) hlot
  have hnat : lot.toNat = (flapperTendLotWordOfState evm id).toNat := by
    rw [hlot]
  simp [evalBinaryOp?, hbeq, hnat]

theorem flapperTendLotEq_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (hlot : lot ≠ flapperTendLotWordOfState evm id) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
      .ok (.bool false) := by
  have hLotVar := flapperTendVarLot_eval evm id lot bid
  have hLotStorage := flapperTendLotStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hLotVar hLotStorage
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hLotVar, hLotStorage]
  have hbeq := flapperTendIntWordBeq_false lot
    (flapperTendLotWordOfState evm id) hlot
  have hnat : ¬ lot.toNat = (flapperTendLotWordOfState evm id).toNat := by
    intro hnat
    exact hlot (u256_inj hnat)
  simp [evalBinaryOp?, hbeq, hnat]

theorem flapperTendBidGt_eval_true (evm : EVM.State) (id lot bid : UInt256)
    (hbid : (flapperTendBidWordOfState evm id).toNat < bid.toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
      .ok (.bool true) := by
  have hBidVar := flapperTendVarBid_eval evm id lot bid
  have hBidStorage := flapperTendBidStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hBidVar hBidStorage
  have hprop : (flapperTendBidWordOfState evm id).toNat < bid.toNat := hbid
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hBidVar, hBidStorage]
  simp [hprop]

theorem flapperTendBidGt_eval_false (evm : EVM.State) (id lot bid : UInt256)
    (hbid : ¬ (flapperTendBidWordOfState evm id).toNat < bid.toNat) :
    evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
      .ok (.bool false) := by
  have hBidVar := flapperTendVarBid_eval evm id lot bid
  have hBidStorage := flapperTendBidStorage_eval evm id lot bid
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hBidVar hBidStorage
  have hprop : ¬ (flapperTendBidWordOfState evm id).toNat < bid.toNat := hbid
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hBidVar, hBidStorage]
  simp [hprop]

@[simp] theorem flapperTendRuntimeGuyRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1))
        (storageRead I.codeOwner σ
          ((UInt256.ofNat 2) +
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperTendIdWord I).toByteArray.write 0 mem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)))) =
      flapperTendGuyWord σ I := by
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperYankBaseSlot (flapperTendIdWord I) := by
    simpa [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  rw [hhash]
  rw [show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask by decide]
  rw [u256_land_comm]
  simp [flapperTendGuyWord, flapperDealGuyWord, flapperYankGuyWord,
    flapperYankPackedWord, flapperTendIdWord, flapperDealIdWord,
    flapperYankPackedSlot, flapperAddressMask_eq_solcAddrMask, u256_add_comm]

@[simp] theorem flapperTendRuntimeTicRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.land (UInt256.ofNat 281474976710655)
        (UInt256.div
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 mem
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32))))
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))) =
      flapperTendTicWord σ I := by
  simpa only [flapperTendTicWord, flapperTendIdWord, flapperDealIdWord,
    flapperUint48Shift160] using
    flapperDealRuntimeTicRaw_eq σ I mem

@[simp] theorem flapperTendRuntimeEndRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.land (UInt256.ofNat 281474976710655)
        (UInt256.div
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 mem
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32))))
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))) =
      flapperTendEndWord σ I := by
  simpa only [flapperTendEndWord, flapperTendIdWord, flapperDealIdWord,
    flapperUint48Shift208] using
    flapperDealRuntimeEndRaw_eq σ I mem

@[simp] theorem flapperTendRuntimeLotRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    storageRead I.codeOwner σ
        ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) =
      flapperTendLotWord σ I := by
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperYankBaseSlot (flapperTendIdWord I) := by
    simpa [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  rw [hhash]
  simp [flapperTendLotWord, flapperDealLotWord, flapperTendBaseSlot,
    flapperDealBaseSlot, flapperTendIdWord, flapperDealIdWord]

@[simp] theorem flapperTendRuntimeBidRaw_eq
    (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    storageRead I.codeOwner σ
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32)) =
      flapperTendBidWord σ I := by
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperYankBaseSlot (flapperTendIdWord I) := by
    simpa [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  rw [hhash]
  simp [flapperTendBidWord, flapperDealBidWord, flapperYankBidWord,
    flapperTendIdWord, flapperDealIdWord]

theorem flapperX_tend_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz100 : 100 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1630)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd524⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 96) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 96)
      (by simpa using hsz100) hsize
  have hcondLen :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 96)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd546 := flapperRuntimeBlocks.flapperRuntime_block_524_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd524
  have rd1630 := flapperRuntimeBlocks.flapperRuntime_block_546
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd546
  exact ⟨_, _, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_546_stack,
      flapperTendBidArgWord, flapperTendLotArgWord, flapperTendIdWord,
      flapperDealIdWord, flapperYankIdWord, calldataWord,
      show (UInt256.ofNat 64 + UInt256.ofNat 4).toNat = 68 by decide,
      show (UInt256.ofNat 4 + UInt256.ofNat 32).toNat = 36 by decide] using rd1630⟩

theorem flapperX_tend_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd524⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 96) = UInt256.ofNat 1 := by
    apply ult_one
    rw [usub_ofNat_word_toNat
      (c := UInt256.ofNat 4)
      (by change 4 ≤ I.calldata.size; omega) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 96)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd542 := flapperRuntimeBlocks.flapperRuntime_block_524_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd524
  exact flapperRuntimeBlocks.flapperRuntime_block_542
    (R := flapperRuntimeBlocks.flapperRuntime_block_524_fallthrough_stack
      (ee := I) (R := [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_524_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd542

theorem flapperX_tend_live_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) ≠ UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 1630)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1630⟩ := hdecode
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 7)) =
        UInt256.ofNat 0 :=
    u256_eq_of_ne (by intro h; exact hlive h.symm)
  obtain ⟨_, _, rd1641⟩ := flapperRuntimeBlocks.flapperRuntime_block_1630_fallthrough
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLive rd1630
  exact flapperRuntimeBlocks.flapperRuntime_block_1641
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd1641

theorem flapperX_tend_live_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlive : storageRead I.codeOwner σ (UInt256.ofNat 7) = UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 1630)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 1704)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1630⟩ := hdecode
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 7)) ≠
        UInt256.ofNat 0 := by
    rw [hlive]
    decide
  obtain ⟨aw, k, C, rd1704⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1630_taken_packed
      (R := flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLive (by jump_dest) rd1630
  exact ⟨aw, k, C, rd1704⟩

theorem flapperX_tend_guy_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hguy : flapperTendGuyWord σ I = UInt256.ofNat 0)
    (h1704 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1704)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd1704⟩ := h1704
  have hcondGuy :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 solcFreePtrMem
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)))) =
        UInt256.ofNat 0 := by
    simpa [hguy] using flapperTendRuntimeGuyRaw_eq σ I solcFreePtrMem
  obtain ⟨_, _, rd1736⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1704_fallthrough
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondGuy rd1704
  exact flapperRuntimeBlocks.flapperRuntime_block_1736
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_1704_fallthrough_memory,
        flapperTendScratchMem, flapperDealScratchMem] using rd1736)

theorem flapperX_tend_guy_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hguy : flapperTendGuyWord σ I ≠ UInt256.ofNat 0)
    (h1704 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1704)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      solcFreePtrMem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1802)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) solcFreePtrMem) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1704⟩ := h1704
  have hcondGuy :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1))
          (storageRead I.codeOwner σ
            ((UInt256.ofNat 2) +
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((UInt256.ofNat 1).toByteArray.write 0
                  ((flapperTendIdWord I).toByteArray.write 0 solcFreePtrMem
                    (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32)))) ≠
        UInt256.ofNat 0 := by
    intro hzero
    apply hguy
    rw [← flapperTendRuntimeGuyRaw_eq σ I solcFreePtrMem]
    exact hzero
  obtain ⟨aw', k, C, rd1802⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1704_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondGuy (by jump_dest) rd1704
  exact ⟨aw', k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1704_taken_memory,
      flapperTendScratchMem, flapperDealScratchMem] using rd1802⟩

theorem flapperX_tend_tic_gt_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray}
    (htic : (flapperTendTimestampWord I).toNat < (flapperTendTicWord σ I).toNat)
    (h1802 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1802)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1960)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1802⟩ := h1802
  have hgt :
      UInt256.gt (flapperTendTicWord σ I) (UInt256.ofNat I.header.timestamp) =
        UInt256.ofNat 1 := by
    simpa [flapperTendTimestampWord, flapperDealTimestampWord] using
      ugt_one htic
  have hcondTic :
      UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    rw [flapperTendRuntimeTicRaw_eq σ I mem, hgt]
    decide
  obtain ⟨aw1879, _, _, rd1879raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1802_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondTic (by jump_dest) rd1802
  obtain ⟨aw1960, k, C, rd1960⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1879_taken_packed
      (x0 := UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp))
      (R := flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondTic (by jump_dest)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_1802_taken_stack,
          flapperRuntimeBlocks.flapperRuntime_block_1802_taken_memory,
          flapperTendScratchMem, flapperDealScratchMem] using rd1879raw)
  exact ⟨aw1960, k, C, rd1960⟩

theorem flapperX_tend_tic_zero_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hticNot :
      ¬ (flapperTendTimestampWord I).toNat < (flapperTendTicWord σ I).toNat)
    (hticZero : flapperTendTicWord σ I = UInt256.ofNat 0)
    (h1802 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1802)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1960)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I)
        (flapperTendScratchMem (flapperTendIdWord I) mem))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1802⟩ := h1802
  have hle :
      (flapperTendTicWord σ I).toNat ≤
        (flapperTendTimestampWord I).toNat := by
    exact le_of_not_gt hticNot
  have hgt :
      UInt256.gt (flapperTendTicWord σ I) (UInt256.ofNat I.header.timestamp) =
        UInt256.ofNat 0 := by
    simpa [flapperTendTimestampWord, flapperDealTimestampWord] using
      ugt_zero hle
  have hcondTic :
      UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp) = UInt256.ofNat 0 := by
    rw [flapperTendRuntimeTicRaw_eq σ I mem, hgt]
  obtain ⟨aw1844, _, _, rd1844raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondTic rd1802
  obtain ⟨aw1879, _, _, rd1879raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1844_packed
      (x1 := flapperTendBidArgWord I)
      (x2 := flapperTendLotArgWord I) (x3 := flapperTendIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_stack,
          flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_memory,
          flapperTendScratchMem, flapperDealScratchMem] using
          rd1844raw)
  have hcondZero :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0
                        (flapperTendScratchMem (flapperTendIdWord I) mem)
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) ≠
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeTicRaw_eq σ I
      (flapperTendScratchMem (flapperTendIdWord I) mem), hticZero]
    decide
  obtain ⟨aw1960, k, C, rd1960⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1879_taken_packed
      (x0 := UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0
                        (flapperTendScratchMem (flapperTendIdWord I) mem)
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))))
      (R := flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondZero (by jump_dest)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_1844_stack,
          flapperRuntimeBlocks.flapperRuntime_block_1844_memory,
          flapperTendScratchMem, flapperDealScratchMem] using rd1879raw)
  exact ⟨aw1960, k, C, rd1960⟩

theorem flapperX_tend_timing_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hticNot :
      ¬ (flapperTendTimestampWord I).toNat < (flapperTendTicWord σ I).toNat)
    (hticNe : flapperTendTicWord σ I ≠ UInt256.ofNat 0)
    (h1802 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1802)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd1802⟩ := h1802
  have hle :
      (flapperTendTicWord σ I).toNat ≤
        (flapperTendTimestampWord I).toNat := le_of_not_gt hticNot
  have hgt :
      UInt256.gt (flapperTendTicWord σ I) (UInt256.ofNat I.header.timestamp) =
        UInt256.ofNat 0 := by
    simpa [flapperTendTimestampWord, flapperDealTimestampWord] using
      ugt_zero hle
  have hcondTic :
      UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))
          (UInt256.ofNat I.header.timestamp) = UInt256.ofNat 0 := by
    rw [flapperTendRuntimeTicRaw_eq σ I mem, hgt]
  obtain ⟨aw1844, _, _, rd1844raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondTic rd1802
  obtain ⟨aw1879, _, _, rd1879raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1844_packed
      (x1 := flapperTendBidArgWord I)
      (x2 := flapperTendLotArgWord I) (x3 := flapperTendIdWord I)
      (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_stack,
          flapperRuntimeBlocks.flapperRuntime_block_1802_fallthrough_memory,
          flapperTendScratchMem, flapperDealScratchMem] using
          rd1844raw)
  have hcondZero :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0
                        (flapperTendScratchMem (flapperTendIdWord I) mem)
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) =
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeTicRaw_eq σ I
      (flapperTendScratchMem (flapperTendIdWord I) mem)]
    exact isZero_eq_zero_of_ne hticNe
  have rd1884 :=
    flapperRuntimeBlocks.flapperRuntime_block_1879_fallthrough
      (x0 := UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0
                        (flapperTendScratchMem (flapperTendIdWord I) mem)
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))))
      (R := flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondZero
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_1844_stack,
          flapperRuntimeBlocks.flapperRuntime_block_1844_memory,
          flapperTendScratchMem, flapperDealScratchMem] using rd1879raw)
  exact flapperRuntimeBlocks.flapperRuntime_block_1884
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd1884

theorem flapperX_tend_end_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hend :
      ¬ (flapperTendTimestampWord I).toNat < (flapperTendEndWord σ I).toNat)
    (h1960 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1960)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd1960⟩ := h1960
  have hle :
      (flapperTendEndWord σ I).toNat ≤
        (flapperTendTimestampWord I).toNat := le_of_not_gt hend
  have hgt :
      UInt256.gt (flapperTendEndWord σ I) (UInt256.ofNat I.header.timestamp) =
        UInt256.ofNat 0 := by
    simpa [flapperTendTimestampWord, flapperDealTimestampWord] using
      ugt_zero hle
  have hcondEnd :
      UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) = UInt256.ofNat 0 := by
    rw [flapperTendRuntimeEndRaw_eq σ I mem, hgt]
  obtain ⟨_, _, rd2001⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1960_fallthrough
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondEnd rd1960
  exact flapperRuntimeBlocks.flapperRuntime_block_2001
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_1960_fallthrough_memory,
        flapperTendScratchMem, flapperDealScratchMem] using rd2001)

theorem flapperX_tend_end_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hend :
      (flapperTendTimestampWord I).toNat < (flapperTendEndWord σ I).toNat)
    (h1960 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1960)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2077)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd1960⟩ := h1960
  have hgt :
      UInt256.gt (flapperTendEndWord σ I) (UInt256.ofNat I.header.timestamp) =
        UInt256.ofNat 1 := by
    simpa [flapperTendTimestampWord, flapperDealTimestampWord] using
      ugt_one hend
  have hcondEnd :
      UInt256.gt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTendIdWord I).toByteArray.write 0 mem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    rw [flapperTendRuntimeEndRaw_eq σ I mem, hgt]
    decide
  obtain ⟨aw2077, k, C, rd2077⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_1960_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondEnd (by jump_dest) rd1960
  exact ⟨aw2077, k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1960_taken_memory,
      flapperTendScratchMem, flapperDealScratchMem] using rd2077⟩

theorem flapperX_tend_lot_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hlot : flapperTendLotArgWord I ≠ flapperTendLotWord σ I)
    (h2077 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2077)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd2077⟩ := h2077
  have hcondLot :
      UInt256.eq (flapperTendLotArgWord I)
          (storageRead I.codeOwner σ
            ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperTendIdWord I).toByteArray.write 0 mem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1))) =
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeLotRaw_eq σ I mem]
    exact u256_eq_of_ne hlot
  obtain ⟨_, _, rd2103⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2077_fallthrough
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLot rd2077
  exact flapperRuntimeBlocks.flapperRuntime_block_2103
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_2077_fallthrough_memory,
        flapperTendScratchMem, flapperDealScratchMem] using rd2103)

theorem flapperX_tend_lot_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hlot : flapperTendLotArgWord I = flapperTendLotWord σ I)
    (h2077 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2077)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2179)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd2077⟩ := h2077
  have hcondLot :
      UInt256.eq (flapperTendLotArgWord I)
          (storageRead I.codeOwner σ
            ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperTendIdWord I).toByteArray.write 0 mem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1))) ≠
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeLotRaw_eq σ I mem, hlot]
    rw [u256_eq_refl (flapperTendLotWord σ I)]
    decide
  obtain ⟨aw2179, k, C, rd2179⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2077_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondLot (by jump_dest) rd2077
  exact ⟨aw2179, k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2077_taken_memory,
      flapperTendScratchMem, flapperDealScratchMem] using rd2179⟩

theorem flapperX_tend_bid_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hbid :
      ¬ (flapperTendBidWord σ I).toNat < (flapperTendBidArgWord I).toNat)
    (h2179 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2179)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd2179⟩ := h2179
  have hle :
      (flapperTendBidArgWord I).toNat ≤
        (flapperTendBidWord σ I).toNat := le_of_not_gt hbid
  have hgt :
      UInt256.gt (flapperTendBidArgWord I) (flapperTendBidWord σ I) =
        UInt256.ofNat 0 := ugt_zero hle
  have hcondBid :
      UInt256.gt (flapperTendBidArgWord I)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperTendIdWord I).toByteArray.write 0 mem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) =
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeBidRaw_eq σ I mem, hgt]
  obtain ⟨_, _, rd2201⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2179_fallthrough
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondBid rd2179
  exact flapperRuntimeBlocks.flapperRuntime_block_2201
    (R := flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
      UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_2179_fallthrough_memory,
        flapperTendScratchMem, flapperDealScratchMem] using rd2201)

theorem flapperX_tend_bid_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hbid :
      (flapperTendBidWord σ I).toNat < (flapperTendBidArgWord I).toNat)
    (h2179 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2179)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      (flapperTendBidArgWord I :: flapperTendLotArgWord I :: flapperTendIdWord I ::
        UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd2179⟩ := h2179
  have hgt :
      UInt256.gt (flapperTendBidArgWord I) (flapperTendBidWord σ I) =
        UInt256.ofNat 1 := ugt_one hbid
  have hcondBid :
      UInt256.gt (flapperTendBidArgWord I)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 1).toByteArray.write 0
                ((flapperTendIdWord I).toByteArray.write 0 mem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ UInt256.ofNat 0 := by
    rw [flapperTendRuntimeBidRaw_eq σ I mem, hgt]
    decide
  obtain ⟨aw2270, k, C, rd2270⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2179_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondBid (by jump_dest) rd2179
  exact ⟨aw2270, k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2179_taken_memory,
      flapperTendScratchMem, flapperDealScratchMem] using rd2270⟩

theorem flapperTendMulDiv_eq_left_of_fit (x y : UInt256)
    (hy : y ≠ UInt256.ofNat 0)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) y = x := by
  apply u256_inj
  have hyNat : y.toNat ≠ 0 := by
    intro hzero
    exact hy (u256_inj hzero)
  have hyPos : 0 < y.toNat := Nat.pos_of_ne_zero hyNat
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  rw [Nat.mul_comm x.toNat y.toNat]
  exact Nat.mul_div_right x.toNat hyPos

theorem flapperTendMulDiv_ne_left_of_overflow (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul x y) y ≠ x := by
  intro hdiv
  have hyNat : y.toNat ≠ 0 := by
    intro hzero
    have hprod : x.toNat * y.toNat = 0 := by simp [hzero]
    have hpos : 0 < UInt256.size := by native_decide
    omega
  have hdivNat := congrArg UInt256.toNat hdiv
  rw [udiv_toNat, u256_mul_toNat] at hdivNat
  have hle :
      x.toNat * y.toNat ≤ (x.toNat * y.toNat % UInt256.size) := by
    calc
      x.toNat * y.toNat =
          (x.toNat * y.toNat % UInt256.size / y.toNat) * y.toNat := by
            rw [hdivNat]
      _ ≤ x.toNat * y.toNat % UInt256.size :=
            Nat.div_mul_le_self _ _
  have hmodLt :
      x.toNat * y.toNat % UInt256.size < x.toNat * y.toNat := by
    have hpos : 0 < UInt256.size := by native_decide
    exact lt_of_lt_of_le (Nat.mod_lt _ hpos) hover
  omega

theorem flapperX_tend_checkedMul_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {x y dest : UInt256} {R : List UInt256}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hstack : R.length + 9 ≤ 1024)
    (hvalidDest : (D_J flapperBytecode 0).contains dest = true)
    (h4894 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 4894)
      (y :: x :: dest :: R) mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) dest (UInt256.mul x y :: R)
      mem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw, _, _, rd4894⟩ := h4894
  by_cases hy : y = UInt256.ofNat 0
  · subst y
    have hcond4894 : UInt256.isZero (UInt256.ofNat 0) ≠ UInt256.ofNat 0 := by
      decide
    obtain ⟨aw4921, _, _, rd4921raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4894_taken_packed
        (x0 := UInt256.ofNat 0) (R := x :: dest :: R)
        (by simp only [List.length_cons]; omega)
        hcond4894 (by jump_dest) rd4894
    obtain ⟨aw4930, _, _, rd4930raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4921_taken_packed
        (x0 := UInt256.isZero (UInt256.ofNat 0))
        (R := UInt256.ofNat 0 :: UInt256.ofNat 0 :: x :: dest :: R)
        (by simp only [List.length_cons]; omega)
        hcond4894 (by jump_dest)
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4894_taken_stack] using
            rd4921raw)
    obtain ⟨awDest, k, C, rdDest⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4930_packed
        (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 0) (x2 := x)
        (x3 := dest) (R := R)
        (by omega)
        hvalidDest
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4921_taken_stack] using
            rd4930raw)
    have hmulZero : UInt256.mul x (UInt256.ofNat 0) = UInt256.ofNat 0 := by
      apply u256_inj
      rw [u256_mul_toNat, show (UInt256.ofNat 0).toNat = 0 by decide]
      simp
    exact ⟨awDest, k, C, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_4930_stack, hmulZero] using
        rdDest⟩
  · have hcond4894 : UInt256.isZero y = UInt256.ofNat 0 :=
      isZero_eq_zero_of_ne hy
    obtain ⟨aw4904, _, _, rd4904raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4894_fallthrough_packed
        (x0 := y) (R := x :: dest :: R)
        (by simp only [List.length_cons]; omega)
        hcond4894 rd4894
    obtain ⟨aw4918, _, _, rd4918raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4904_taken_packed
        (x0 := UInt256.isZero y) (x1 := UInt256.ofNat 0) (x2 := y) (x3 := x)
        (R := dest :: R)
        (by simp only [List.length_cons]; omega)
        hy (by jump_dest)
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4894_fallthrough_stack,
            hcond4894] using rd4904raw)
    obtain ⟨aw4921, _, _, rd4921raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4918_packed
        (x0 := UInt256.mul x y) (x1 := y) (x2 := x)
        (R := UInt256.mul x y :: y :: x :: dest :: R)
        (by simp only [List.length_cons]; omega)
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4904_taken_stack] using
            rd4918raw)
    have hdiv : UInt256.div (UInt256.mul x y) y = x :=
      flapperTendMulDiv_eq_left_of_fit x y hy hfit
    have hcond4921 :
        UInt256.eq (UInt256.div (UInt256.mul x y) y) x ≠ UInt256.ofNat 0 := by
      rw [hdiv, u256_eq_refl]
      decide
    obtain ⟨aw4930, _, _, rd4930raw⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4921_taken_packed
        (x0 := UInt256.eq (UInt256.div (UInt256.mul x y) y) x)
        (R := UInt256.mul x y :: y :: x :: dest :: R)
        (by simp only [List.length_cons]; omega)
        hcond4921 (by jump_dest)
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4918_stack] using
            rd4921raw)
    obtain ⟨awDest, k, C, rdDest⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_4930_packed
        (x0 := UInt256.mul x y) (x1 := y) (x2 := x) (x3 := dest)
        (R := R)
        (by omega)
        hvalidDest
        (by
          simpa [flapperRuntimeBlocks.flapperRuntime_block_4921_taken_stack] using
            rd4930raw)
    exact ⟨awDest, k, C, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_4930_stack] using rdDest⟩

theorem flapperX_tend_checkedMul_overflow_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {mem : ByteArray} {x y dest : UInt256} {R : List UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (hstack : R.length + 9 ≤ 1024)
    (h4894 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 4894)
      (y :: x :: dest :: R) mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd4894⟩ := h4894
  have hy : y ≠ UInt256.ofNat 0 := by
    intro hzero
    subst y
    have hpos : 0 < UInt256.size := by native_decide
    rw [show (UInt256.ofNat 0).toNat = 0 by decide, Nat.mul_zero] at hover
    omega
  have hcond4894 : UInt256.isZero y = UInt256.ofNat 0 :=
    isZero_eq_zero_of_ne hy
  obtain ⟨aw4904, _, _, rd4904raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4894_fallthrough_packed
      (x0 := y) (R := x :: dest :: R)
      (by simp only [List.length_cons]; omega)
      hcond4894 rd4894
  obtain ⟨aw4918, _, _, rd4918raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4904_taken_packed
      (x0 := UInt256.isZero y) (x1 := UInt256.ofNat 0) (x2 := y) (x3 := x)
      (R := dest :: R)
      (by simp only [List.length_cons]; omega)
      hy (by jump_dest)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_4894_fallthrough_stack,
          hcond4894] using rd4904raw)
  obtain ⟨aw4921, _, _, rd4921raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_4918_packed
      (x0 := UInt256.mul x y) (x1 := y) (x2 := x)
      (R := UInt256.mul x y :: y :: x :: dest :: R)
      (by simp only [List.length_cons]; omega)
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_4904_taken_stack] using
          rd4918raw)
  have hdivNe : UInt256.div (UInt256.mul x y) y ≠ x :=
    flapperTendMulDiv_ne_left_of_overflow x y hover
  have hcond4921 :
      UInt256.eq (UInt256.div (UInt256.mul x y) y) x = UInt256.ofNat 0 :=
    u256_eq_of_ne hdivNe
  have rd4926 :=
    flapperRuntimeBlocks.flapperRuntime_block_4921_fallthrough
      (x0 := UInt256.eq (UInt256.div (UInt256.mul x y) y) x)
      (R := UInt256.mul x y :: y :: x :: dest :: R)
      (by simp only [List.length_cons]; omega)
      hcond4921
      (by
        simpa [flapperRuntimeBlocks.flapperRuntime_block_4918_stack] using
          rd4921raw)
  exact flapperRuntimeBlocks.flapperRuntime_block_4926
    (R := UInt256.mul x y :: y :: x :: dest :: R)
    (by simp only [List.length_cons]; omega)
    rd4926

theorem flapperX_tend_begBid_overflow_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hover :
      UInt256.size ≤
        (flapperTendBegWord σ I).toNat * (flapperTendBidWord σ I).toNat)
    (h2270 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw, _, _, rd2270⟩ := h2270
  obtain ⟨aw4894, _, _, rd4894raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2270_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := [UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd2270
  have h4894 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 4894)
      (flapperTendBidWord σ I :: flapperTendBegWord σ I ::
        UInt256.ofNat 2298 ::
        [flapperTendBidArgWord I, flapperTendLotArgWord I,
          flapperTendIdWord I, UInt256.ofNat 360, sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw ByteArray.empty
      (cA, σ) k C := by
    exact ⟨aw4894, _, _, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_2270_stack,
        flapperRuntimeBlocks.flapperRuntime_block_2270_memory,
        flapperTendScratchMem, flapperTendBegWord] using rd4894raw⟩
  exact flapperX_tend_checkedMul_overflow_revert
    (x := flapperTendBegWord σ I) (y := flapperTendBidWord σ I)
    (dest := UInt256.ofNat 2298)
    (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
      flapperTendIdWord I, UInt256.ofNat 360, sel])
    hover (by simp only [List.length_cons, List.length_nil]; omega) h4894

theorem flapperX_tend_begBid_ok_to_bidOne_check {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hfit :
      (flapperTendBegWord σ I).toNat * (flapperTendBidWord σ I).toNat <
        UInt256.size)
    (h2270 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 4894)
      (flapperTendOneWord :: flapperTendBidArgWord I :: UInt256.ofNat 2316 ::
        flapperTendBegBidWord σ I :: flapperTendBidArgWord I ::
        flapperTendLotArgWord I :: flapperTendIdWord I :: UInt256.ofNat 360 ::
        [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨aw, _, _, rd2270⟩ := h2270
  obtain ⟨aw4894, _, _, rd4894raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2270_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := [UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd2270
  have h4894 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 4894)
      (flapperTendBidWord σ I :: flapperTendBegWord σ I ::
        UInt256.ofNat 2298 ::
        [flapperTendBidArgWord I, flapperTendLotArgWord I,
          flapperTendIdWord I, UInt256.ofNat 360, sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw ByteArray.empty
      (cA, σ) k C := by
    exact ⟨aw4894, _, _, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_2270_stack,
        flapperRuntimeBlocks.flapperRuntime_block_2270_memory,
        flapperTendScratchMem, flapperTendBegWord] using rd4894raw⟩
  obtain ⟨aw2298, k2298, C2298, rd2298raw⟩ :=
    flapperX_tend_checkedMul_ok
      (x := flapperTendBegWord σ I) (y := flapperTendBidWord σ I)
      (dest := UInt256.ofNat 2298)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      hfit (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) h4894
  have h2298 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2298)
      (flapperTendBegBidWord σ I :: flapperTendBidArgWord I ::
        flapperTendLotArgWord I :: flapperTendIdWord I :: UInt256.ofNat 360 ::
        [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw2298 ByteArray.empty
      (cA, σ) k2298 C2298 := by
    simpa [flapperTendBegBidWord] using rd2298raw
  obtain ⟨aw4894b, k, C, rd4894b⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2298_packed
      (x0 := flapperTendBegBidWord σ I)
      (x1 := flapperTendBidArgWord I)
      (R := [flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) h2298
  exact ⟨aw4894b, k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2298_stack,
      flapperTendOneWord] using rd4894b⟩

theorem flapperX_tend_bidOne_overflow_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hbegFit :
      (flapperTendBegWord σ I).toNat * (flapperTendBidWord σ I).toNat <
        UInt256.size)
    (hover :
      UInt256.size ≤
        (flapperTendBidArgWord I).toNat * flapperTendOneWord.toNat)
    (h2270 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h4894 := flapperX_tend_begBid_ok_to_bidOne_check
    (σ := σ) (g := g) (sel := sel) (mem := mem) hbegFit h2270
  exact flapperX_tend_checkedMul_overflow_revert
    (x := flapperTendBidArgWord I) (y := flapperTendOneWord)
    (dest := UInt256.ofNat 2316)
    (R := [flapperTendBegBidWord σ I, flapperTendBidArgWord I,
      flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
    hover (by simp only [List.length_cons, List.length_nil]; omega) h4894

theorem flapperX_tend_checkedMul_floor_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hbegFit :
      (flapperTendBegWord σ I).toNat * (flapperTendBidWord σ I).toNat <
        UInt256.size)
    (hbidOneFit :
      (flapperTendBidArgWord I).toNat * flapperTendOneWord.toNat < UInt256.size)
    (hfloor :
      (flapperTendBidOneWord I).toNat < (flapperTendBegBidWord σ I).toNat)
    (h2270 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw4894, k4894, C4894, rd4894⟩ := flapperX_tend_begBid_ok_to_bidOne_check
    (σ := σ) (g := g) (sel := sel) (mem := mem) hbegFit h2270
  obtain ⟨aw2316, k2316, C2316, rd2316raw⟩ :=
    flapperX_tend_checkedMul_ok
      (x := flapperTendBidArgWord I) (y := flapperTendOneWord)
      (dest := UInt256.ofNat 2316)
      (R := [flapperTendBegBidWord σ I, flapperTendBidArgWord I,
        flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
      hbidOneFit (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) ⟨aw4894, k4894, C4894, rd4894⟩
  have h2316 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2316)
      (flapperTendBidOneWord I :: flapperTendBegBidWord σ I ::
        flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw2316 ByteArray.empty
      (cA, σ) k2316 C2316 := by
    simpa [flapperTendBidOneWord] using rd2316raw
  have hlt : UInt256.lt (flapperTendBidOneWord I) (flapperTendBegBidWord σ I) =
      UInt256.ofNat 1 := by
    exact ult_one hfloor
  have hcond :
      UInt256.isZero
          (UInt256.lt (flapperTendBidOneWord I) (flapperTendBegBidWord σ I)) =
        UInt256.ofNat 0 := by
    rw [hlt]
    decide
  obtain ⟨aw2323, _, _, rd2323⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2316_fallthrough_packed
      (x0 := flapperTendBidOneWord I) (x1 := flapperTendBegBidWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond h2316
  exact flapperRuntimeBlocks.flapperRuntime_block_2323
    (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
      flapperTendIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd2323

theorem flapperX_tend_checkedMul_floor_ok {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hbegFit :
      (flapperTendBegWord σ I).toNat * (flapperTendBidWord σ I).toNat <
        UInt256.size)
    (hbidOneFit :
      (flapperTendBidArgWord I).toNat * flapperTendOneWord.toNat < UInt256.size)
    (hfloor :
      ¬ (flapperTendBidOneWord I).toNat < (flapperTendBegBidWord σ I).toNat)
    (h2270 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2270)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2399)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨aw4894, k4894, C4894, rd4894⟩ := flapperX_tend_begBid_ok_to_bidOne_check
    (σ := σ) (g := g) (sel := sel) (mem := mem) hbegFit h2270
  obtain ⟨aw2316, k2316, C2316, rd2316raw⟩ :=
    flapperX_tend_checkedMul_ok
      (x := flapperTendBidArgWord I) (y := flapperTendOneWord)
      (dest := UInt256.ofNat 2316)
      (R := [flapperTendBegBidWord σ I, flapperTendBidArgWord I,
        flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
      hbidOneFit (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest) ⟨aw4894, k4894, C4894, rd4894⟩
  have h2316 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2316)
      (flapperTendBidOneWord I :: flapperTendBegBidWord σ I ::
        flapperTendBidArgWord I :: flapperTendLotArgWord I ::
        flapperTendIdWord I :: UInt256.ofNat 360 :: [sel])
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw2316 ByteArray.empty
      (cA, σ) k2316 C2316 := by
    simpa [flapperTendBidOneWord] using rd2316raw
  have hlt : UInt256.lt (flapperTendBidOneWord I) (flapperTendBegBidWord σ I) =
      UInt256.ofNat 0 := by
    exact ult_zero (Nat.le_of_not_lt hfloor)
  have hcond :
      UInt256.isZero
          (UInt256.lt (flapperTendBidOneWord I) (flapperTendBegBidWord σ I)) ≠
        UInt256.ofNat 0 := by
    rw [hlt]
    decide
  obtain ⟨aw2399, k, C, rd2399⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2316_taken_packed
      (x0 := flapperTendBidOneWord I) (x1 := flapperTendBegBidWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond (by jump_dest) h2316
  exact ⟨aw2399, k, C, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2316_taken_stack] using
      rd2399⟩

theorem flapperX_tend_refund_skipped {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hsame : UInt256.ofNat I.source.val = flapperTendGuyWord σ I)
    (h2399 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2399)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2598)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨aw2399, _, _, rd2399⟩ := h2399
  have hcond :
      UInt256.eq (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1))
            (storageRead I.codeOwner σ
              ((UInt256.ofNat 2) +
                (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                  ((UInt256.ofNat 1).toByteArray.write 0
                    ((flapperTendIdWord I).toByteArray.write 0 mem
                      (UInt256.ofNat 0).toNat 32)
                    (UInt256.ofNat 32).toNat 32))))) ≠
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeGuyRaw_eq σ I mem, ← hsame]
    rw [u256_eq_refl]
    decide
  obtain ⟨aw2598, k2598, C2598, rd2598raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2399_taken_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond (by jump_dest) rd2399
  exact ⟨aw2598, k2598, C2598, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2399_taken_memory,
      flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd2598raw⟩

theorem flapperX_tend_refund_setup {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hdiff : UInt256.ofNat I.source.val ≠ flapperTendGuyWord σ I)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h2399 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2399)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2519)
      (UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel)
      (flapperTendRefundCallMemFrom σ I
        (flapperTendScratchMem (flapperTendIdWord I)
          (flapperTendScratchMem (flapperTendIdWord I) mem)))
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw2399, _, _, rd2399⟩ := h2399
  have hcond :
      UInt256.eq (UInt256.ofNat I.source.val)
          (UInt256.land
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1))
            (storageRead I.codeOwner σ
              ((UInt256.ofNat 2) +
                (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                  ((UInt256.ofNat 1).toByteArray.write 0
                    ((flapperTendIdWord I).toByteArray.write 0 mem
                      (UInt256.ofNat 0).toNat 32)
                    (UInt256.ofNat 32).toNat 32))))) =
        UInt256.ofNat 0 := by
    rw [flapperTendRuntimeGuyRaw_eq σ I mem]
    exact u256_eq_of_ne hdiff
  obtain ⟨aw2433, k2433, C2433, rd2433raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2399_fallthrough_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcond rd2399
  have rd2433 : RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2433)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      (flapperTendScratchMem (flapperTendIdWord I) mem) aw2433 ByteArray.empty
      (cA, σ) k2433 C2433 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2399_fallthrough_memory,
      flapperTendScratchMem, flapperDealScratchMem,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd2433raw
  let mem2433 := flapperTendScratchMem (flapperTendIdWord I) mem
  have hmem2433 : 96 ≤ mem2433.size := by
    simpa [mem2433] using
      flapperTendScratchMem_size_ge_96 (flapperTendIdWord I) mem hmem
  have hread2433 : mem2433.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
    simpa [mem2433] using
      flapperTendScratchMem_read64 (flapperTendIdWord I) mem hmem hread
  obtain ⟨aw2519, k2519, C2519, rd2519raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2433_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by simpa [mem2433] using rd2433)
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem2433) =
        UInt256.ofNat 128 :=
    flapperTendScratchMem_mload64 (flapperTendIdWord I) mem2433
      hmem2433 hread2433
  have hmemEq :=
    flapperTendRuntimeRefundCallMem_eq_from σ I mem2433 hbase
  have hstackEq :=
    flapperTendRuntimeRefundCallStack_eq_from σ I sel mem2433
      (flapperTendScratchMem_size_ge_96 (flapperTendIdWord I) mem2433
        hmem2433)
      (flapperTendScratchMem_read64 (flapperTendIdWord I) mem2433
        hmem2433 hread2433)
  exact ⟨aw2519, k2519, C2519, by
    simpa [mem2433, hmemEq, hstackEq] using rd2519raw⟩

theorem flapperX_tend_refund_no_code_revert {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperTendGemWord σ I) = UInt256.ofNat 0)
    (h2519 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2519)
      (UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel)
      mem aw ByteArray.empty (cAcur, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, _, rd2519⟩ := h2519
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I))) =
        UInt256.ofNat 0 := by
    rw [hcodeSize]
    decide
  obtain ⟨_, _, _, rd2536⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2519_fallthrough_packed
      (x0 := UInt256.ofNat 128) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 0)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt rd2519
  exact flapperRuntimeBlocks.flapperRuntime_block_2536
    (R := flapperRuntimeBlocks.flapperRuntime_block_2519_fallthrough_stack
      (σ := σ) (x0 := UInt256.ofNat 128) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 0)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_2519_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd2536

theorem flapperX_tend_refund_call_boundary {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperTendGemWord σ I) ≠ UInt256.ofNat 0)
    (h2519 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2519)
      (UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel)
      mem aw ByteArray.empty (cAcur, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2543)
      (gasArg :: flapperTendGemWord σ I :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel)
      mem aw ByteArray.empty (cAcur, σ) k C := by
  obtain ⟨_, _, _, rd2519⟩ := h2519
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I))) ≠
        UInt256.ofNat 0 := by
    rw [isZero_eq_zero_of_ne hcodeSize]
    decide
  obtain ⟨aw2540, k2540, C2540, rd2540raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2519_taken_packed
      (x0 := UInt256.ofNat 128) (x1 := UInt256.ofNat 100)
      (x2 := UInt256.ofNat 128) (x3 := UInt256.ofNat 0)
      (x4 := UInt256.ofNat 228) (x5 := UInt256.ofNat 3140843579)
      (x6 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest) rd2519
  have rd2540 : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2540)
      (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I)) ::
        flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw2540 ByteArray.empty (cAcur, σ) k2540 C2540 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2519_taken_stack,
      flapperTendMoveCallRest,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) =
        UInt256.ofNat 0 by decide,
      show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide]
      using rd2540raw
  have rd2542 := flapperRuntimeBlocks.flapperRuntime_block_2540
    (x0 := UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I)))
    (R := flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperTendMoveCallRest σ I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    rd2540
  have rd2542' : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2542)
      (flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw2540 ByteArray.empty (cAcur, σ) (k2540 + 2) (C2540 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2540_stack] using rd2542
  obtain ⟨gasArg, rd2543raw⟩ := RD.rawGas rd2542' (by native_decide)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw2540, k2540 + 2 + 1, C2540 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_2540_stack,
    show UInt256.ofNat 2542 + ⟨1⟩ = UInt256.ofNat 2543 by native_decide]
    using rd2543raw

theorem flapperX_tend_refund_call_failure {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σcall : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 2544)
      (UInt256.ofNat 0 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2551 := flapperRuntimeBlocks.flapperRuntime_block_2544_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperTendMoveCallRest σcall I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_2551
    (R := flapperRuntimeBlocks.flapperRuntime_block_2544_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperTendMoveCallRest σcall I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_2544_fallthrough_stack,
        flapperTendMoveCallRest, List.length_cons, List.length_nil]
      omega)
    rd2551

theorem flapperX_tend_refund_call_success_to_pay_start
    {cA cAcur gh bl σinit σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {σcall : AccountMap}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I)
      (UInt256.ofNat 2544)
      (UInt256.ofNat 1 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata (cAcur, σ) k C) :
    ∃ aw' k' C', RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2598)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      (flapperTendScratchMem (flapperTendIdWord I) mem)
      aw' rdata (cAcur, flapperTendAfterRefundWorld σ I) k' C' := by
  have rd2560raw := flapperRuntimeBlocks.flapperRuntime_block_2544_taken
    (x0 := UInt256.ofNat 1) (R := flapperTendMoveCallRest σcall I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) h
  have rd2560 : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2560)
      (UInt256.ofNat 0 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata (cAcur, σ) (k + 5) (C + 22) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2544_taken_stack,
      flapperTendMoveCallRest] using rd2560raw
  obtain ⟨aw2598, k2598, C2598, rd2598raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2560_packed
      (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
      (x2 := UInt256.ofNat 3140843579)
      (x3 := flapperTendGemWord σcall I)
      (x4 := flapperTendBidArgWord I) (x5 := flapperTendLotArgWord I)
      (x6 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm rd2560
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32)
            32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  exact ⟨aw2598, k2598, C2598, by
    simpa [flapperTendAfterRefundWorld,
      flapperRuntimeBlocks.flapperRuntime_block_2560_stack,
      flapperRuntimeBlocks.flapperRuntime_block_2560_memory,
      flapperTendScratchMem, flapperDealScratchMem, flapperTendPackedSlot,
      flapperDealPackedSlot, flapperYankPackedSlot, hhash, u256_add_comm,
      show (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = solcAddrMask by decide,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd2598raw⟩

theorem flapperX_tend_pay_setup {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h2598 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2598)
      [flapperTendBidArgWord I, flapperTendLotArgWord I, flapperTendIdWord I,
        UInt256.ofNat 360, sel]
      mem aw rdata (cAcur, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2683)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      (flapperTendPayCallMemFrom σ I
        (flapperTendScratchMem (flapperTendIdWord I) mem))
      aw rdata (cAcur, σ) k C := by
  obtain ⟨_, _, _, rd2598⟩ := h2598
  obtain ⟨aw2683, k2683, C2683, rd2683raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2598_packed
      (x0 := flapperTendBidArgWord I) (x1 := flapperTendLotArgWord I)
      (x2 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      rd2598
  have hbase : memLoad (UInt256.ofNat 64)
      (flapperTendScratchMem (flapperTendIdWord I) mem) =
        UInt256.ofNat 128 :=
    flapperTendScratchMem_mload64 (flapperTendIdWord I) mem hmem hread
  have hmemEq :=
    flapperTendRuntimePayCallMem_eq_from σ I mem hbase
  have hstackEq :=
    flapperTendRuntimePayCallStack_eq_from σ I sel mem
      (flapperTendScratchMem_size_ge_96 (flapperTendIdWord I) mem hmem)
      (flapperTendScratchMem_read64 (flapperTendIdWord I) mem hmem hread)
  exact ⟨aw2683, k2683, C2683, by
    simpa [hmemEq, hstackEq] using rd2683raw⟩

theorem flapperX_tend_pay_no_code_revert {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperTendGemWord σ I) = UInt256.ofNat 0)
    (h2683 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2683)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw rdata (cAcur, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, _, rd2683⟩ := h2683
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I))) =
        UInt256.ofNat 0 := by
    rw [hcodeSize]
    decide
  obtain ⟨_, _, _, rd2695⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2683_fallthrough_packed
      (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 228)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt rd2683
  exact flapperRuntimeBlocks.flapperRuntime_block_2695
    (R := flapperRuntimeBlocks.flapperRuntime_block_2683_fallthrough_stack
      (σ := σ) (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 228)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_2683_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd2695

theorem flapperX_tend_pay_call_boundary {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hcodeSize : extCodeSizeWord σ (flapperTendGemWord σ I) ≠ UInt256.ofNat 0)
    (h2683 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2683)
      (UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw rdata (cAcur, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2702)
      (gasArg :: flapperTendGemWord σ I :: UInt256.ofNat 0 ::
        UInt256.ofNat 128 :: UInt256.ofNat 100 :: UInt256.ofNat 128 ::
        UInt256.ofNat 0 :: flapperTendMoveCallRest σ I sel)
      mem aw rdata (cAcur, σ) k C := by
  obtain ⟨_, _, _, rd2683⟩ := h2683
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I))) ≠
        UInt256.ofNat 0 := by
    rw [isZero_eq_zero_of_ne hcodeSize]
    decide
  obtain ⟨aw2699, k2699, C2699, rd2699raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2683_taken_packed
      (x0 := UInt256.ofNat 100) (x1 := UInt256.ofNat 128)
      (x2 := UInt256.ofNat 0) (x3 := UInt256.ofNat 228)
      (x4 := UInt256.ofNat 3140843579) (x5 := flapperTendGemWord σ I)
      (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hcondExt (by jump_dest) rd2683
  have rd2699 : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2699)
      (UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I)) ::
        flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw2699 rdata (cAcur, σ) k2699 C2699 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2683_taken_stack,
      flapperTendMoveCallRest] using rd2699raw
  have rd2701 := flapperRuntimeBlocks.flapperRuntime_block_2699
    (x0 := UInt256.isZero (extCodeSizeWord σ (flapperTendGemWord σ I)))
    (R := flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperTendMoveCallRest σ I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    rd2699
  have rd2701' : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2701)
      (flapperTendGemWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperTendMoveCallRest σ I sel)
      mem aw2699 rdata (cAcur, σ) (k2699 + 2) (C2699 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2699_stack] using rd2701
  obtain ⟨gasArg, rd2702raw⟩ := RD.rawGas rd2701' (by native_decide)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw2699, k2699 + 2 + 1, C2699 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_2699_stack,
    show UInt256.ofNat 2701 + ⟨1⟩ = UInt256.ofNat 2702 by native_decide]
    using rd2702raw

theorem flapperX_tend_pay_call_failure {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σcall : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 2703)
      (UInt256.ofNat 0 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2710 := flapperRuntimeBlocks.flapperRuntime_block_2703_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperTendMoveCallRest σcall I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_2710
    (R := flapperRuntimeBlocks.flapperRuntime_block_2703_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperTendMoveCallRest σcall I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_2703_fallthrough_stack,
        flapperTendMoveCallRest, List.length_cons, List.length_nil]
      omega)
    rd2710

theorem flapperX_tend_pay_call_success_to_add48
    {cA cAcur gh bl σinit σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {σcall : AccountMap}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g (initState cA gh bl σinit σ₀ g A I)
      (UInt256.ofNat 2703)
      (UInt256.ofNat 1 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata (cAcur, σ) k C) :
    ∃ aw' k' C', RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4936)
      [flapperTendTtlWord (flapperTendAfterPayWorld σ I) I,
        flapperTendTimestampWord I, UInt256.ofNat 2762,
        flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel]
      (flapperTendScratchMem (flapperTendIdWord I) mem)
      aw' rdata (cAcur, flapperTendAfterPayWorld σ I) k' C' := by
  have rd2719raw := flapperRuntimeBlocks.flapperRuntime_block_2703_taken
    (x0 := UInt256.ofNat 1) (R := flapperTendMoveCallRest σcall I sel)
    (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) h
  have rd2719 : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 2719)
      (UInt256.ofNat 0 :: flapperTendMoveCallRest σcall I sel)
      mem aw rdata (cAcur, σ) (k + 5) (C + 22) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_2703_taken_stack,
      flapperTendMoveCallRest] using rd2719raw
  obtain ⟨aw4936, k4936, C4936, rd4936raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2719_packed
      (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
      (x2 := UInt256.ofNat 3140843579)
      (x3 := flapperTendGemWord σcall I)
      (x4 := flapperTendBidArgWord I) (x5 := flapperTendLotArgWord I)
      (x6 := flapperTendIdWord I) (R := UInt256.ofNat 360 :: [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm (by jump_dest) rd2719
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32)
            32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  exact ⟨aw4936, k4936, C4936, by
    simpa [flapperTendAfterPayWorld, flapperTendTtlWord,
      flapperTendTimestampWord, flapperDealTimestampWord,
      flapperRuntimeBlocks.flapperRuntime_block_2719_stack,
      flapperRuntimeBlocks.flapperRuntime_block_2719_memory,
      flapperTendScratchMem, flapperDealScratchMem, hhash, u256_land_comm,
      show flapperUint48Mask = UInt256.ofNat 281474976710655 by native_decide,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd4936raw⟩

theorem flapperX_tend_tic_overflow_revert {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hwrap : (flapperTendNewTicWord σ I).toNat < (flapperTendNowWord I).toNat)
    (h4936 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4936)
      [flapperTendTtlWord σ I, flapperTendTimestampWord I,
        UInt256.ofNat 2762, flapperTendBidArgWord I,
        flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel]
      mem aw rdata (cAcur, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, _, rd4936⟩ := h4936
  have hltWrap :
      UInt256.lt (flapperTendNewTicWord σ I) (flapperTendNowWord I) =
        UInt256.ofNat 1 := by
    exact ult_one hwrap
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              (flapperTendTimestampWord I + flapperTendTtlWord σ I)
              (UInt256.ofNat 281474976710655))
            (UInt256.land (flapperTendTimestampWord I)
              (UInt256.ofNat 281474976710655))) =
        UInt256.ofNat 0 := by
    simpa [flapperTendNewTicWord, flapperTendNowWord,
      show flapperUint48Mask = UInt256.ofNat 281474976710655 by native_decide]
      using
        (by
          rw [hltWrap]
          decide :
          UInt256.isZero
              (UInt256.lt (flapperTendNewTicWord σ I)
                (flapperTendNowWord I)) =
            UInt256.ofNat 0)
  have rd4959 := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough
    (x0 := flapperTendTtlWord σ I) (x1 := flapperTendTimestampWord I)
    (R := [UInt256.ofNat 2762, flapperTendBidArgWord I,
      flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondWrap rd4936
  exact flapperRuntimeBlocks.flapperRuntime_block_4959
    (R := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack
      (x0 := flapperTendTtlWord σ I) (x1 := flapperTendTimestampWord I)
      (R := [UInt256.ofNat 2762, flapperTendBidArgWord I,
        flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd4959

theorem flapperX_tend_tic_ok_return {cA cAcur gh bl σinit σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hwrap :
      ¬ (flapperTendNewTicWord σ I).toNat < (flapperTendNowWord I).toNat)
    (h4936 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 4936)
      [flapperTendTtlWord σ I, flapperTendTimestampWord I,
        UInt256.ofNat 2762, flapperTendBidArgWord I,
        flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel]
      mem aw rdata (cAcur, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σinit σ₀ g A I)
      (cAcur, flapperTendAfterTicWorld σ I) ByteArray.empty := by
  obtain ⟨aw4936, k4936, C4936, rd4936⟩ := h4936
  have hltWrap :
      UInt256.lt (flapperTendNewTicWord σ I) (flapperTendNowWord I) =
        UInt256.ofNat 0 := by
    exact ult_zero (Nat.le_of_not_lt hwrap)
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              (flapperTendTimestampWord I + flapperTendTtlWord σ I)
              (UInt256.ofNat 281474976710655))
            (UInt256.land (flapperTendTimestampWord I)
              (UInt256.ofNat 281474976710655))) ≠
        UInt256.ofNat 0 := by
    simpa [flapperTendNewTicWord, flapperTendNowWord,
      show flapperUint48Mask = UInt256.ofNat 281474976710655 by native_decide]
      using
        (by
          rw [hltWrap]
          decide :
          UInt256.isZero
              (UInt256.lt (flapperTendNewTicWord σ I)
                (flapperTendNowWord I)) ≠
            UInt256.ofNat 0)
  have rd4930raw := flapperRuntimeBlocks.flapperRuntime_block_4936_taken
    (x0 := flapperTendTtlWord σ I) (x1 := flapperTendTimestampWord I)
    (R := [UInt256.ofNat 2762, flapperTendBidArgWord I,
      flapperTendLotArgWord I, flapperTendIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondWrap (by jump_dest) rd4936
  have rd2762 := flapperRuntimeBlocks.flapperRuntime_block_4930
    (x0 := flapperTendTimestampWord I + flapperTendTtlWord σ I)
    (x1 := flapperTendTtlWord σ I) (x2 := flapperTendTimestampWord I)
    (x3 := UInt256.ofNat 2762)
    (R := [flapperTendBidArgWord I, flapperTendLotArgWord I,
      flapperTendIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    (by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_4936_taken_stack]
        using rd4930raw)
  obtain ⟨aw360, k360, C360, rd360raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_2762_packed
      (x0 := flapperTendTimestampWord I + flapperTendTtlWord σ I)
      (x1 := flapperTendBidArgWord I) (x2 := flapperTendLotArgWord I)
      (x3 := flapperTendIdWord I) (x4 := UInt256.ofNat 360)
      (R := [sel])
      (by simp only [List.length_cons, List.length_nil]; omega)
      hperm (by jump_dest) rd2762
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTendIdWord I).toByteArray.write 0 mem 0 32)
            32 32) =
        flapperTendBaseSlot (flapperTendIdWord I) := by
    simpa [flapperTendBaseSlot, flapperDealBaseSlot,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using
      flapperYankMappingHashSlot (flapperTendIdWord I) mem
  have hnewClean :
      UInt256.land flapperUint48Mask (flapperTendNewTicWord σ I) =
        flapperTendNewTicWord σ I := by
    simpa [flapperTendNewTicWord, u256_land_comm] using
      flapperUint48Mask_clean_right_file
        (flapperTendTimestampWord I + flapperTendTtlWord σ I)
  have hnewCleanRaw :
      UInt256.land (UInt256.ofNat 281474976710655)
          (UInt256.land (UInt256.ofNat 281474976710655)
            (flapperTendTimestampWord I + flapperTendTtlWord σ I)) =
        UInt256.land (UInt256.ofNat 281474976710655)
          (flapperTendTimestampWord I + flapperTendTtlWord σ I) := by
    rw [← show flapperUint48Mask = UInt256.ofNat 281474976710655 by native_decide]
    rw [u256_land_comm flapperUint48Mask
      (UInt256.land flapperUint48Mask
        (flapperTendTimestampWord I + flapperTendTtlWord σ I))]
    rw [u256_land_comm flapperUint48Mask
      (flapperTendTimestampWord I + flapperTendTtlWord σ I)]
    exact flapperUint48Mask_clean_right_file
      (flapperTendTimestampWord I + flapperTendTtlWord σ I)
  have rd360 : RD flapperBytecode I g
      (initState cA gh bl σinit σ₀ g A I) (UInt256.ofNat 360)
      [sel] (flapperTendScratchMem (flapperTendIdWord I) mem)
      aw360 rdata (cAcur, flapperTendAfterTicWorld σ I) k360 C360 := by
    simpa [flapperTendAfterTicWorld, flapperTendPackedTicWord,
      flapperTendNewTicWord, flapperTendPackedSlot, flapperDealPackedSlot,
      flapperYankPackedSlot, flapperTendBaseSlot, flapperDealBaseSlot,
      flapperRuntimeBlocks.flapperRuntime_block_2762_stack,
      flapperRuntimeBlocks.flapperRuntime_block_2762_memory,
      flapperTendScratchMem, flapperDealScratchMem, hhash, hnewClean,
      hnewCleanRaw,
      u256_add_comm, u256_land_comm,
      show flapperUint48Mask = UInt256.ofNat 281474976710655 by native_decide,
      show flapperUint48Shift160 =
        UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) by rfl,
      show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide] using rd360raw
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd360

set_option maxHeartbeats 1000000 in
theorem flapperTendPayTailProgress
    {cA cAcur : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σinit σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {sel : UInt256} {mem2598 rdata : ByteArray}
    {evm : EVM.State} {locals : Store}
    (hState : CallStateRel
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      I (cAcur, σworld) evm)
    (hperm : I.perm = true)
    (hbaseGem : locals.get? "gem" = none)
    (hbaseBids : locals.get? "bids" = none)
    (hbaseTtl : locals.get? "ttl" = none)
    (hgetId : locals.get? "id" =
      some (.int (Int.ofNat (flapperTendIdWord I).toNat)))
    (hgetBid : locals.get? "bid" =
      some (.int (Int.ofNat (flapperTendBidArgWord I).toNat)))
    (hmem : 96 ≤ mem2598.size)
    (hread : mem2598.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h2598 : ∃ aw k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 2598)
      [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel]
      mem2598 aw rdata (cAcur, σworld) k C) :
    BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
      config { contract := contract, locals := locals } evm
      (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
        [sender, thisAddr,
          wrap256 (.binary .sub (.var "bid")
            (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
       [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
       checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
       [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      (runtimeExit (.abi tendTransition.returnType)) := by
  let id := flapperTendIdWord I
  let bid := flapperTendBidArgWord I
  let frame : Frame := { contract := contract, locals := locals }
  let payBase := flapperTendScratchMem id mem2598
  let payMem := flapperTendPayCallMemFrom σworld I payBase
  have hGemWordSolm :
      flapperTendGemWordOfState evm = flapperTendGemWord σworld I :=
    flapperTendGemWordOfState_eq_of_stateRel (g := g) hState
  have hPayAmtSolm :
      flapperTendPayAmtWordOfState evm id bid =
        flapperTendPayAmtWord σworld I := by
    simpa [id, bid] using
      flapperTendPayAmtWordOfState_eq_of_stateRel (g := g) hState
  have h2683 := flapperX_tend_pay_setup
    (cA := cA) (cAcur := cAcur) (gh := gh) (bl := bl)
    (σinit := σinit) (σ := σworld) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := sel) hmem hread h2598
  by_cases hGemCodeSize :
      extCodeSizeWord σworld (flapperTendGemWord σworld I) = UInt256.ofNat 0
  · have hGemCodeSizeSolm :
        extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) =
          UInt256.ofNat 0 := by
      have hmapCode := extCodeSizeWord_accountMapEquiv hState.accounts
        (flapperTendGemWord σworld I)
      exact (by simpa [hGemWordSolm] using hmapCode.symm.trans hGemCodeSize)
    have hguardFalse :
        evalExpr? config frame evm
          (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
            .ok (.bool false) := by
      simpa [frame, hGemWordSolm] using
        flapperTendGemExtGuard_false_of_locals evm locals hbaseGem
          hGemCodeSizeSolm
    exact BlockProgress.ofRDrev
      (hsource := by
        simpa [checkedExternalCallStmts, checkedAdd48Into, frame] using
          (ExecBlock.consRevert (ExecStmt.requireFalse hguardFalse) :
            ExecBlock config frame evm
              ((.require
                (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0))) ::
                (.externalCall (.storage gemRef) "move" (.intLit 0)
                  [sender, thisAddr,
                    wrap256 (.binary .sub (.var "bid")
                      (.storage (bidsF (.var "id") "bid")))]
                  "_payRet") ::
                [ .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
                  .letDecl "tic_" (some uint48)
                    (wrap48 (.binary .add now48 (.storage ttlRef))),
                  .require (.binary .ge (.var "tic_") now48),
                  .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
              .reverted))
      (flapperX_tend_pay_no_code_revert
        (cA := cA) (cAcur := cAcur) (gh := gh) (bl := bl)
        (σinit := σinit) (σ := σworld) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (sel := sel) hGemCodeSize h2683)
  · have hGemCodeSizeSolmNe :
        extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) ≠
          UInt256.ofNat 0 := by
      intro hzero
      apply hGemCodeSize
      have hmapCode := extCodeSizeWord_accountMapEquiv hState.accounts
        (flapperTendGemWord σworld I)
      have hzeroGem :
          extCodeSizeWord evm.accountMap (flapperTendGemWord σworld I) =
            UInt256.ofNat 0 := by
        simpa [hGemWordSolm] using hzero
      exact hmapCode.trans hzeroGem
    have hguardTrue :
        evalExpr? config frame evm
          (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
            .ok (.bool true) := by
      simpa [frame, hGemWordSolm] using
        flapperTendGemExtGuard_true_of_locals evm locals hbaseGem
          hGemCodeSizeSolmNe
    have htailExternal :
        BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
          config frame evm
          [ .externalCall (.storage gemRef) "move" (.intLit 0)
              [sender, thisAddr,
                wrap256 (.binary .sub (.var "bid")
                  (.storage (bidsF (.var "id") "bid")))] "_payRet",
            .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
            .letDecl "tic_" (some uint48)
              (wrap48 (.binary .add now48 (.storage ttlRef))),
            .require (.binary .ge (.var "tic_") now48),
            .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]
          (runtimeExit (.abi tendTransition.returnType)) := by
      obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
        flapperX_tend_pay_call_boundary
          (cA := cA) (cAcur := cAcur) (gh := gh) (bl := bl)
          (σinit := σinit) (σ := σworld) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (sel := sel) hGemCodeSize h2683
      refine BlockProgress.externalCall
        (h := rdCall) (hState := hState)
        (receiver := .storage gemRef) (eth := .intLit 0)
        (args := [sender, thisAddr,
          wrap256 (.binary .sub (.var "bid")
            (.storage (bidsF (.var "id") "bid")))])
        (argVals := [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (flapperTendPayAmtWord σworld I).toNat)])
        (tgt := AccountAddress.ofNat (flapperTendGemWord σworld I).toNat)
        (name := "move") (retVar := "_payRet") (value := 0)
        (stmts :=
          [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
        (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
        (show runtimeExit (.abi tendTransition.returnType)
            ExecResult.reverted Endpoint.reverted by
          simp [runtimeExit, functionResult]) ?_ ?_
      · have hrecv := flapperTendGemStorage_eval_of_locals evm locals hbaseGem
        simpa [frame, hGemWordSolm] using hrecv
      · simp [evalExpr?, pure]
      · have hargs := flapperTendPayArgs_eval_of_locals evm locals id bid
          hbaseBids (by simpa [id] using hgetId) (by simpa [bid] using hgetBid)
        simpa [frame, id, bid, hState.env, hPayAmtSolm] using hargs
      · exact wordOfInt_zero.symm
      · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
        apply Fin.ext
        simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
          AccountAddress.size]
      · change config.externalABI.encode? "move"
            [.address I.source, .address I.codeOwner,
              .int (Int.ofNat (flapperTendPayAmtWord σworld I).toNat)] =
          some ((flapperTendPayCallMemFrom σworld I payBase).readWithPadding
            128 100)
        exact flapperTendPayMoveEncodeFrom_eq σworld I payBase
      · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
        have hdecodeOut : config.externalABI.decode? "move" out = some [] := by
          simp [config, externalABI, decodeVoid?]
        rw [hdecodeOut]
        cases world' with
        | mk cApay σpay =>
            let localsAfterPay := flapperTendLocalsAfterPay locals
            let frameAfterPay : Frame :=
              { contract := contract, locals := localsAfterPay }
            let evmBid := Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner
              (flapperTendBaseSlot id) bid
            let newTic := flapperTendNewTicWordOfState evmBid
            let localsTic := flapperTendLocalsTic localsAfterPay newTic
            let frameTic : Frame := { contract := contract, locals := localsTic }
            let evmTic := Solm.EVM.storageStore evmBid evmBid.executionEnv.codeOwner
              (flapperTendPackedSlot id)
              (flapperTendPackedTicWord
                (flapperTendPackedWordOfState evmBid id) newTic)
            have hmin0 :
                (min (UInt256.ofNat 0) (UInt256.ofNat out.size)).toNat = 0 := by
              simpa [show (UInt256.ofNat 0).toNat = 0 by decide] using
                callCopyLength_toNat out (UInt256.ofNat 0) hsizeOut
            have h2703 :
                RD flapperBytecode I (Sat256.ofUInt256 g)
                  (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
                  (UInt256.ofNat 2703)
                  (UInt256.ofNat 1 :: flapperTendMoveCallRest σworld I sel)
                  payMem cur.aw out (cApay, σpay) k' C' := by
              simpa [callCursor, hmin0, byteArray_write_len_zero, payMem,
                show UInt256.ofNat 2702 + ⟨1⟩ = UInt256.ofNat 2703 by native_decide]
                using rdSucc
            have h4936 := flapperX_tend_pay_call_success_to_add48
              (cA := cA) (cAcur := cApay) (gh := gh) (bl := bl)
              (σinit := σinit) (σ := σpay) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) (sel := sel) (σcall := σworld)
              hperm h2703
            have hgetBidAfterPay : localsAfterPay.get? "bid" =
                some (.int (Int.ofNat bid.toNat)) := by
              unfold localsAfterPay flapperTendLocalsAfterPay
              rw [store_get_ne locals (k := "_payRet") (a := "bid")
                (collapseReturns []) (by decide)]
              exact hgetBid
            have hgetIdAfterPay : localsAfterPay.get? "id" =
                some (.int (Int.ofNat id.toNat)) := by
              unfold localsAfterPay flapperTendLocalsAfterPay
              rw [store_get_ne locals (k := "_payRet") (a := "id")
                (collapseReturns []) (by decide)]
              exact hgetId
            have hbaseBidsAfterPay : localsAfterPay.get? "bids" = none := by
              unfold localsAfterPay flapperTendLocalsAfterPay
              rw [store_get_ne locals (k := "_payRet") (a := "bids")
                (collapseReturns []) (by decide)]
              exact hbaseBids
            have hbaseTtlAfterPay : localsAfterPay.get? "ttl" = none := by
              unfold localsAfterPay flapperTendLocalsAfterPay
              rw [store_get_ne locals (k := "_payRet") (a := "ttl")
                (collapseReturns []) (by decide)]
              exact hbaseTtl
            have hBidRhs :
                evalExpr? config frameAfterPay evm' (.var "bid") =
                  .ok (.int (Int.ofNat bid.toNat)) := by
              exact flapperTendVarInt_eval_of_get (evm := evm')
                (by simpa [frameAfterPay] using hgetBidAfterPay)
            have hAssignBid :
                assignStorageRef? config frameAfterPay evm'
                    .storage (bidsF (.var "id") "bid")
                    (.int (Int.ofNat bid.toNat)) =
                  .ok (frameAfterPay, evmBid) := by
              change assignStorageRef? config
                    { contract := contract, locals := localsAfterPay } evm'
                    .storage (bidsF (.var "id") "bid")
                    (.int (Int.ofNat bid.toNat)) =
                  .ok ({ contract := contract, locals := localsAfterPay },
                    Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner
                      (flapperTendBaseSlot id) bid)
              exact flapperTendAssignBid_of_locals evm' localsAfterPay id bid
                hbaseBidsAfterPay hgetIdAfterPay
            have hStateBid :
                CallStateRel
                  (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
                  I (cApay, flapperTendAfterPayWorld σpay I) evmBid := by
              change CallStateRel
                (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
                I (cApay, flapperTendAfterPayWorld σpay I)
                (Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner
                  (flapperTendBaseSlot (flapperTendIdWord I))
                  (flapperTendBidArgWord I))
              exact flapperTendAfterPay_stateRel (g := g) hState'
            have hNewTicEq :
                newTic =
                  flapperTendNewTicWord (flapperTendAfterPayWorld σpay I) I := by
              simpa [newTic] using
                flapperTendNewTicWordOfState_eq_of_stateRel (g := g) hStateBid
            have hNowEq :
                flapperTendNowWordOfState evmBid = flapperTendNowWord I := by
              simpa using
                flapperTendNowWordOfState_eq_of_stateRel (g := g) hStateBid
            have hLetTic :
                evalExpr? config frameAfterPay evmBid
                    (wrap48 (.binary .add now48 (.storage ttlRef))) =
                  .ok (.int (Int.ofNat newTic.toNat)) := by
              simpa [frameAfterPay, newTic] using
                flapperTendNewTic_eval evmBid localsAfterPay hbaseTtlAfterPay
            by_cases hwrap :
                (flapperTendNewTicWord (flapperTendAfterPayWorld σpay I) I).toNat <
                  (flapperTendNowWord I).toNat
            · have hwrapSolm : newTic.toNat < (flapperTendNowWordOfState evmBid).toNat := by
                simpa [hNewTicEq, hNowEq] using hwrap
              have hguardWrapFalse :
                  evalExpr? config frameTic evmBid
                      (.binary .ge (.var "tic_") now48) =
                    .ok (.bool false) := by
                simpa [frameTic, localsTic, newTic] using
                  flapperTendTicCheckedGuard_eval_false evmBid localsAfterPay
                    newTic hwrapSolm
              have hsource :
                  ExecBlock config frameAfterPay evm'
                    ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
                     checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                     [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
                    .reverted := by
                simpa [checkedAdd48Into, frameAfterPay, frameTic, localsAfterPay,
                  localsTic, evmBid, newTic] using
                  (ExecBlock.consNormal (ExecStmt.assign hBidRhs hAssignBid) <|
                    ExecBlock.consNormal (ExecStmt.letDecl hLetTic) <|
                      ExecBlock.consRevert
                        (ExecStmt.requireFalse hguardWrapFalse) :
                    ExecBlock config frameAfterPay evm'
                      [ .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
                        .letDecl "tic_" (some uint48)
                          (wrap48 (.binary .add now48 (.storage ttlRef))),
                        .require (.binary .ge (.var "tic_") now48),
                        .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]
                      .reverted)
              exact BlockProgress.ofRDrev
                (hsource := hsource)
                (flapperX_tend_tic_overflow_revert
                  (cA := cA) (cAcur := cApay) (gh := gh) (bl := bl)
                  (σinit := σinit) (σ := flapperTendAfterPayWorld σpay I)
                  (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (sel := sel) hwrap h4936)
            · have hwrapSolm :
                  ¬ newTic.toNat < (flapperTendNowWordOfState evmBid).toNat := by
                intro hbad
                exact hwrap (by simpa [hNewTicEq, hNowEq] using hbad)
              have hguardWrapTrue :
                  evalExpr? config frameTic evmBid
                      (.binary .ge (.var "tic_") now48) =
                    .ok (.bool true) := by
                simpa [frameTic, localsTic, newTic] using
                  flapperTendTicCheckedGuard_eval_true evmBid localsAfterPay
                    newTic hwrapSolm
              have hTicRhs :
                  evalExpr? config frameTic evmBid (.var "tic_") =
                    .ok (.int (Int.ofNat newTic.toNat)) := by
                simpa [frameTic, localsTic, newTic] using
                  flapperTendTicLocal_eval evmBid localsAfterPay newTic
              have hbaseBidsTic : localsTic.get? "bids" = none := by
                unfold localsTic flapperTendLocalsTic
                rw [store_get_ne localsAfterPay (k := "tic_") (a := "bids")
                  (.int (Int.ofNat newTic.toNat)) (by decide)]
                exact hbaseBidsAfterPay
              have hgetIdTic : localsTic.get? "id" =
                  some (.int (Int.ofNat id.toNat)) := by
                unfold localsTic flapperTendLocalsTic
                rw [store_get_ne localsAfterPay (k := "tic_") (a := "id")
                  (.int (Int.ofNat newTic.toNat)) (by decide)]
                exact hgetIdAfterPay
              have hnewClean : UInt256.land newTic flapperUint48Mask = newTic := by
                simpa [newTic, flapperTendNewTicWordOfState] using
                  flapperUint48Mask_clean_right_file
                    (flapperTendTimestampWordOfState evmBid +
                      flapperTendTtlWordOfState evmBid)
              have hAssignTic :
                  assignStorageRef? config frameTic evmBid
                      .storage (bidsF (.var "id") "tic")
                      (.int (Int.ofNat newTic.toNat)) =
                    .ok (frameTic, evmTic) := by
                simpa [frameTic, evmTic, id, newTic] using
                  flapperTendAssignTic_of_locals evmBid localsTic id newTic
                    hnewClean hbaseBidsTic hgetIdTic
              have hsource :
                  ExecBlock config frameAfterPay evm'
                    ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
                     checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                     [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
                    (.ok frameTic evmTic) := by
                simpa [checkedAdd48Into, frameAfterPay, frameTic, localsAfterPay,
                  localsTic, evmBid, evmTic, newTic] using
                  (ExecBlock.consNormal (ExecStmt.assign hBidRhs hAssignBid) <|
                    ExecBlock.consNormal (ExecStmt.letDecl hLetTic) <|
                      ExecBlock.consNormal (ExecStmt.requireTrue hguardWrapTrue) <|
                        ExecBlock.consNormal (ExecStmt.assign hTicRhs hAssignTic)
                          ExecBlock.nil :
                    ExecBlock config frameAfterPay evm'
                      [ .assign .storage (bidsF (.var "id") "bid") (.var "bid"),
                        .letDecl "tic_" (some uint48)
                          (wrap48 (.binary .add now48 (.storage ttlRef))),
                        .require (.binary .ge (.var "tic_") now48),
                        .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]
                      (.ok frameTic evmTic))
              have hStateTic :
                  CallStateRel
                    (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
                    I
                    (cApay,
                      flapperTendAfterTicWorld (flapperTendAfterPayWorld σpay I) I)
                    evmTic := by
                simpa [evmTic, id, newTic] using
                  flapperTendAfterTic_stateRel (g := g) hStateBid
              exact BlockProgress.ofRDret
                (frame' := frameTic) (evm' := evmTic) (value := none)
                (hsource := hsource)
                (flapperX_tend_tic_ok_return
                  (cA := cA) (cAcur := cApay) (gh := gh) (bl := bl)
                  (σinit := σinit) (σ := flapperTendAfterPayWorld σpay I)
                  (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (sel := sel) hperm hwrap h4936)
                hStateTic.created.symm hStateTic.accounts
                (by simpa [tendTransition] using abiVoidFallthrough)
      · intro out world' k' C' cur rdFail
        exact flapperX_tend_pay_call_failure
          (cA := cA) (gh := gh) (bl := bl) (σ := σinit)
          (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (sel := sel) (σcall := σworld)
          (h := by
            simpa [callCursor,
              show UInt256.ofNat 2702 + ⟨1⟩ = UInt256.ofNat 2703 by native_decide]
              using rdFail)
    have htail :
        BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σinit σ₀ (Sat256.ofUInt256 g) A I)
          config frame evm
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
            [sender, thisAddr,
              wrap256 (.binary .sub (.var "bid")
                (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
           [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
           checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
           [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
          (runtimeExit (.abi tendTransition.returnType)) := by
      simpa [checkedExternalCallStmts, checkedAdd48Into] using
        BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
    simpa [frame] using htail

set_option maxHeartbeats 4000000 in
theorem flapperTendExternalTailProgress
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σworld σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} {sel : UInt256} {mem2399 : ByteArray}
    {evm : EVM.State} {locals : Store}
    (hState : CallStateRel
      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
      I (cA, σworld) evm)
    (hperm : I.perm = true)
    (hbaseGem : locals.get? "gem" = none)
    (hbaseBids : locals.get? "bids" = none)
    (hbaseTtl : locals.get? "ttl" = none)
    (hgetId : locals.get? "id" =
      some (.int (Int.ofNat (flapperTendIdWord I).toNat)))
    (hgetBid : locals.get? "bid" =
      some (.int (Int.ofNat (flapperTendBidArgWord I).toNat)))
    (hmem : 96 ≤ mem2399.size)
    (hread : mem2399.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128))
    (h2399 : ∃ aw k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
      (UInt256.ofNat 2399)
      [flapperTendBidArgWord I, flapperTendLotArgWord I,
        flapperTendIdWord I, UInt256.ofNat 360, sel]
      mem2399 aw ByteArray.empty (cA, σworld) k C) :
    BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
      config { contract := contract, locals := locals } evm
      ([ .ite
          (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          (checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
              [sender, .storage (bidsF (.var "id") "guy"),
                .storage (bidsF (.var "id") "bid")] "_refundRet" ++
            [ .assign .storage (bidsF (.var "id") "guy") sender ])
          [] ] ++
       checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
        [sender, thisAddr,
          wrap256 (.binary .sub (.var "bid")
            (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
       [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
       checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
       [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      (runtimeExit (.abi tendTransition.returnType)) := by
  let id := flapperTendIdWord I
  let bid := flapperTendBidArgWord I
  let frame : Frame := { contract := contract, locals := locals }
  let payTail : List Stmt :=
    checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
      [sender, thisAddr,
        wrap256 (.binary .sub (.var "bid")
          (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
    [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
    checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
    [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]
  let refundThen : List Stmt :=
    checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
      [sender, .storage (bidsF (.var "id") "guy"),
        .storage (bidsF (.var "id") "bid")] "_refundRet" ++
    [ .assign .storage (bidsF (.var "id") "guy") sender ]
  have hGuyWordSolm :
      flapperTendGuyWordOfState evm id = flapperTendGuyWord σworld I := by
    simpa [id] using flapperTendGuyWordOfState_eq_of_stateRel (g := g) hState
  have hBidWordSolm :
      flapperTendBidWordOfState evm id = flapperTendBidWord σworld I := by
    simpa [id] using flapperTendBidWordOfState_eq_of_stateRel (g := g) hState
  have hGemWordSolm :
      flapperTendGemWordOfState evm = flapperTendGemWord σworld I :=
    flapperTendGemWordOfState_eq_of_stateRel (g := g) hState
  change BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
      config frame evm
      ([ .ite
          (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
          refundThen [] ] ++ payTail)
      (runtimeExit (.abi tendTransition.returnType))
  by_cases hsame : UInt256.ofNat I.source.val = flapperTendGuyWord σworld I
  · have hsameSolm :
        UInt256.ofNat evm.executionEnv.source.val = flapperTendGuyWordOfState evm id := by
      rw [hState.env]
      exact hsame.trans hGuyWordSolm.symm
    have hcondFalse :
        evalExpr? config frame evm
            (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool false) := by
      simpa [frame, id] using
        flapperTendSenderNeGuy_eval_false_of_locals evm locals id
          hbaseBids (by simpa [id] using hgetId) hsameSolm
    have h2598 := flapperX_tend_refund_skipped
      (cA := cA) (gh := gh) (bl := bl) (σ := σworld) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
      hsame h2399
    have hmem2598 : 96 ≤ (flapperTendScratchMem id mem2399).size := by
      simpa [id] using flapperTendScratchMem_size_ge_96 id mem2399 hmem
    have hread2598 :
        (flapperTendScratchMem id mem2399).readWithPadding 64 32 =
          UInt256.toByteArray (UInt256.ofNat 128) := by
      simpa [id] using flapperTendScratchMem_read64 id mem2399 hmem hread
    have htail : BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
        config frame evm payTail
        (runtimeExit (.abi tendTransition.returnType)) := by
      simpa [payTail, frame, id, bid] using
        flapperTendPayTailProgress
          (cA := cA) (cAcur := cA) (gh := gh) (bl := bl)
          (σinit := σworld) (σworld := σworld) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel)
          (mem2598 := flapperTendScratchMem id mem2399)
          (evm := evm) (locals := locals)
          hState hperm hbaseGem hbaseBids hbaseTtl
          (by simpa [id] using hgetId) (by simpa [bid] using hgetBid)
          hmem2598 hread2598
          (by simpa [id] using h2598)
    simpa [payTail, refundThen] using
      (BlockProgress.iteFalse
        (cond := (.binary .ne sender (.storage (bidsF (.var "id") "guy"))))
        (thenB := refundThen) (elseB := []) (stmts := payTail)
        hcondFalse (by simpa using htail))
  · have hdiffSolm :
        UInt256.ofNat evm.executionEnv.source.val ≠ flapperTendGuyWordOfState evm id := by
      intro hbad
      apply hsame
      rw [← hGuyWordSolm]
      simpa [hState.env] using hbad
    have hcondTrue :
        evalExpr? config frame evm
            (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool true) := by
      simpa [frame, id] using
        flapperTendSenderNeGuy_eval_true_of_locals evm locals id
          hbaseBids (by simpa [id] using hgetId) hdiffSolm
    have h2519 := flapperX_tend_refund_setup
      (cA := cA) (gh := gh) (bl := bl) (σ := σworld) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
      hsame hmem hread h2399
    let refundBase := flapperTendScratchMem id (flapperTendScratchMem id mem2399)
    let refundMem := flapperTendRefundCallMemFrom σworld I refundBase
    have hbranch : BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
        config frame evm (refundThen ++ payTail)
        (runtimeExit (.abi tendTransition.returnType)) := by
      by_cases hGemCodeSize :
          extCodeSizeWord σworld (flapperTendGemWord σworld I) = UInt256.ofNat 0
      · have hGemCodeSizeSolm :
            extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) =
              UInt256.ofNat 0 := by
          have hmapCode := extCodeSizeWord_accountMapEquiv hState.accounts
            (flapperTendGemWord σworld I)
          exact (by simpa [hGemWordSolm] using hmapCode.symm.trans hGemCodeSize)
        have hguardFalse :
            evalExpr? config frame evm
              (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
                .ok (.bool false) := by
          simpa [frame, hGemWordSolm] using
            flapperTendGemExtGuard_false_of_locals evm locals hbaseGem
              hGemCodeSizeSolm
        exact BlockProgress.ofRDrev
          (hsource := by
            simpa [refundThen, payTail, checkedExternalCallStmts] using
              (ExecBlock.consRevert (ExecStmt.requireFalse hguardFalse) :
                ExecBlock config frame evm
                  ((.require
                    (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0))) ::
                    (.externalCall (.storage gemRef) "move" (.intLit 0)
                      [sender, .storage (bidsF (.var "id") "guy"),
                        .storage (bidsF (.var "id") "bid")]
                      "_refundRet") ::
                    (.assign .storage (bidsF (.var "id") "guy") sender) ::
                    payTail)
                  .reverted))
          (flapperX_tend_refund_no_code_revert
            (cA := cA) (cAcur := cA) (gh := gh) (bl := bl)
            (σinit := σworld) (σ := σworld) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
            hGemCodeSize (by simpa [refundBase, refundMem, id] using h2519))
      · have hGemCodeSizeSolmNe :
            extCodeSizeWord evm.accountMap (flapperTendGemWordOfState evm) ≠
              UInt256.ofNat 0 := by
          intro hzero
          apply hGemCodeSize
          have hmapCode := extCodeSizeWord_accountMapEquiv hState.accounts
            (flapperTendGemWord σworld I)
          have hzeroGem :
              extCodeSizeWord evm.accountMap (flapperTendGemWord σworld I) =
                UInt256.ofNat 0 := by
            simpa [hGemWordSolm] using hzero
          exact hmapCode.trans hzeroGem
        have hguardTrue :
            evalExpr? config frame evm
              (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
                .ok (.bool true) := by
          simpa [frame, hGemWordSolm] using
            flapperTendGemExtGuard_true_of_locals evm locals hbaseGem
              hGemCodeSizeSolmNe
        have htailExternal : BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
            config frame evm
            (.externalCall (.storage gemRef) "move" (.intLit 0)
                [sender, .storage (bidsF (.var "id") "guy"),
                  .storage (bidsF (.var "id") "bid")]
                "_refundRet" ::
              .assign .storage (bidsF (.var "id") "guy") sender ::
              payTail)
            (runtimeExit (.abi tendTransition.returnType)) := by
          obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
            flapperX_tend_refund_call_boundary
              (cA := cA) (cAcur := cA) (gh := gh) (bl := bl)
              (σinit := σworld) (σ := σworld) (σ₀ := σ₀) (A := A)
              (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              hGemCodeSize (by simpa [refundBase, refundMem, id] using h2519)
          refine BlockProgress.externalCall
            (h := rdCall) (hState := hState)
            (receiver := .storage gemRef) (eth := .intLit 0)
            (args := [sender, .storage (bidsF (.var "id") "guy"),
              .storage (bidsF (.var "id") "bid")])
            (argVals := [.address I.source,
              .address (AccountAddress.ofNat (flapperTendGuyWord σworld I).toNat),
              .int (Int.ofNat (flapperTendBidWord σworld I).toNat)])
            (tgt := AccountAddress.ofNat (flapperTendGemWord σworld I).toNat)
            (name := "move") (retVar := "_refundRet") (value := 0)
            (stmts :=
              .assign .storage (bidsF (.var "id") "guy") sender :: payTail)
            ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
            (by simp only [flapperTendMoveCallRest, List.length_cons, List.length_nil]; omega)
            (show runtimeExit (.abi tendTransition.returnType)
                ExecResult.reverted Endpoint.reverted by
              simp [runtimeExit, functionResult]) ?_ ?_
          · have hrecv := flapperTendGemStorage_eval_of_locals evm locals hbaseGem
            simpa [frame, hGemWordSolm] using hrecv
          · simp [evalExpr?, pure]
          · have hargs := flapperTendRefundArgs_eval_of_locals evm locals id
              hbaseBids (by simpa [id] using hgetId)
            simpa [frame, id, hState.env, hGuyWordSolm, hBidWordSolm] using hargs
          · exact wordOfInt_zero.symm
          · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
            apply Fin.ext
            simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
              AccountAddress.size]
          · change config.externalABI.encode? "move"
                [.address I.source,
                  .address (AccountAddress.ofNat (flapperTendGuyWord σworld I).toNat),
                  .int (Int.ofNat (flapperTendBidWord σworld I).toNat)] =
              some ((flapperTendRefundCallMemFrom σworld I refundBase).readWithPadding
                128 100)
            exact flapperTendRefundMoveEncodeFrom_eq σworld I refundBase
          · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
            have hdecodeOut : config.externalABI.decode? "move" out = some [] := by
              simp [config, externalABI, decodeVoid?]
            rw [hdecodeOut]
            cases world' with
            | mk cArefund σrefund =>
                let localsAfterRefund := locals.insert "_refundRet" (collapseReturns [])
                let frameAfterRefund : Frame :=
                  { contract := contract, locals := localsAfterRefund }
                let evmGuy := Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner
                  (flapperTendPackedSlot id)
                  (setAddressOffset0Word
                    (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
                      (flapperTendPackedSlot id))
                    (UInt256.ofNat evm'.executionEnv.source.val))
                have hmin0 :
                    (min (UInt256.ofNat 0) (UInt256.ofNat out.size)).toNat = 0 := by
                  simpa [show (UInt256.ofNat 0).toNat = 0 by decide] using
                    callCopyLength_toNat out (UInt256.ofNat 0) hsizeOut
                have h2544 :
                    RD flapperBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
                      (UInt256.ofNat 2544)
                      (UInt256.ofNat 1 :: flapperTendMoveCallRest σworld I sel)
                      refundMem cur.aw out (cArefund, σrefund) k' C' := by
                  simpa [callCursor, hmin0, byteArray_write_len_zero, refundMem,
                    show UInt256.ofNat 2543 + ⟨1⟩ = UInt256.ofNat 2544 by native_decide]
                    using rdSucc
                have h2598AfterRefund :=
                  flapperX_tend_refund_call_success_to_pay_start
                    (cA := cA) (cAcur := cArefund) (gh := gh) (bl := bl)
                    (σinit := σworld) (σ := σrefund) (σ₀ := σ₀) (A := A)
                    (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                    (σcall := σworld) hperm h2544
                have hgetIdAfterRefund : localsAfterRefund.get? "id" =
                    some (.int (Int.ofNat id.toNat)) := by
                  unfold localsAfterRefund
                  rw [store_get_ne locals (k := "_refundRet") (a := "id")
                    (collapseReturns []) (by decide)]
                  simpa [id] using hgetId
                have hgetBidAfterRefund : localsAfterRefund.get? "bid" =
                    some (.int (Int.ofNat bid.toNat)) := by
                  unfold localsAfterRefund
                  rw [store_get_ne locals (k := "_refundRet") (a := "bid")
                    (collapseReturns []) (by decide)]
                  simpa [bid] using hgetBid
                have hbaseGemAfterRefund : localsAfterRefund.get? "gem" = none := by
                  unfold localsAfterRefund
                  rw [store_get_ne locals (k := "_refundRet") (a := "gem")
                    (collapseReturns []) (by decide)]
                  exact hbaseGem
                have hbaseBidsAfterRefund : localsAfterRefund.get? "bids" = none := by
                  unfold localsAfterRefund
                  rw [store_get_ne locals (k := "_refundRet") (a := "bids")
                    (collapseReturns []) (by decide)]
                  exact hbaseBids
                have hbaseTtlAfterRefund : localsAfterRefund.get? "ttl" = none := by
                  unfold localsAfterRefund
                  rw [store_get_ne locals (k := "_refundRet") (a := "ttl")
                    (collapseReturns []) (by decide)]
                  exact hbaseTtl
                have hGuyRhs :
                    evalExpr? config frameAfterRefund evm' sender =
                      .ok (.address evm'.executionEnv.source) := by
                  simp [frameAfterRefund, sender, evalExpr?, envValue, pure]
                have hAssignGuy :
                    assignStorageRef? config frameAfterRefund evm'
                        .storage (bidsF (.var "id") "guy")
                        (.address evm'.executionEnv.source) =
                      .ok (frameAfterRefund, evmGuy) := by
                  change assignStorageRef? config
                        { contract := contract, locals := localsAfterRefund } evm'
                        .storage (bidsF (.var "id") "guy")
                        (.address evm'.executionEnv.source) =
                    .ok ({ contract := contract, locals := localsAfterRefund },
                      Solm.EVM.storageStore evm' evm'.executionEnv.codeOwner
                        (flapperTendPackedSlot id)
                        (setAddressOffset0Word
                          (Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
                            (flapperTendPackedSlot id))
                          (UInt256.ofNat evm'.executionEnv.source.val)))
                  exact flapperTendAssignGuy_of_locals evm' localsAfterRefund id
                    hbaseBidsAfterRefund hgetIdAfterRefund
                have hStateRefund :
                    CallStateRel
                      (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
                      I (cArefund, flapperTendAfterRefundWorld σrefund I) evmGuy := by
                  simpa [evmGuy, id] using
                    flapperTendAfterRefund_stateRel (g := g) hState'
                have hrefundMemSize : 96 ≤ refundMem.size := by
                  simpa [refundMem] using
                    flapperTendRefundCallMemFrom_size_ge_96 σworld I refundBase
                have hrefundBaseSize : 96 ≤ refundBase.size := by
                  have hmem1 : 96 ≤ (flapperTendScratchMem id mem2399).size :=
                    flapperTendScratchMem_size_ge_96 id mem2399 hmem
                  simpa [refundBase] using
                    flapperTendScratchMem_size_ge_96 id
                      (flapperTendScratchMem id mem2399) hmem1
                have hrefundBaseRead :
                    refundBase.readWithPadding 64 32 =
                      UInt256.toByteArray (UInt256.ofNat 128) := by
                  have hmem1 : 96 ≤ (flapperTendScratchMem id mem2399).size :=
                    flapperTendScratchMem_size_ge_96 id mem2399 hmem
                  have hread1 :
                      (flapperTendScratchMem id mem2399).readWithPadding 64 32 =
                        UInt256.toByteArray (UInt256.ofNat 128) :=
                    flapperTendScratchMem_read64 id mem2399 hmem hread
                  simpa [refundBase] using
                    flapperTendScratchMem_read64 id
                      (flapperTendScratchMem id mem2399) hmem1 hread1
                have hrefundMemRead :
                    refundMem.readWithPadding 64 32 =
                      UInt256.toByteArray (UInt256.ofNat 128) := by
                  simpa [refundMem] using
                    flapperTendRefundCallMemFrom_read64 σworld I refundBase
                      hrefundBaseSize hrefundBaseRead
                have hmem2598 :
                    96 ≤ (flapperTendScratchMem id refundMem).size := by
                  exact flapperTendScratchMem_size_ge_96 id refundMem hrefundMemSize
                have hread2598 :
                    (flapperTendScratchMem id refundMem).readWithPadding 64 32 =
                      UInt256.toByteArray (UInt256.ofNat 128) := by
                  exact flapperTendScratchMem_read64 id refundMem
                    hrefundMemSize hrefundMemRead
                have hpay : BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σworld σ₀ (Sat256.ofUInt256 g) A I)
                    config frameAfterRefund evmGuy payTail
                    (runtimeExit (.abi tendTransition.returnType)) := by
                  simpa [payTail, frameAfterRefund, id, bid] using
                    flapperTendPayTailProgress
                      (cA := cA) (cAcur := cArefund) (gh := gh) (bl := bl)
                      (σinit := σworld)
                      (σworld := flapperTendAfterRefundWorld σrefund I)
                      (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
                      (mem2598 := flapperTendScratchMem id refundMem)
                      (rdata := out) (evm := evmGuy) (locals := localsAfterRefund)
                      hStateRefund hperm hbaseGemAfterRefund hbaseBidsAfterRefund
                      hbaseTtlAfterRefund
                      (by simpa [id] using hgetIdAfterRefund)
                      (by simpa [bid] using hgetBidAfterRefund)
                      hmem2598 hread2598
                      (by simpa [id, refundMem] using h2598AfterRefund)
                exact BlockProgress.cons (ExecStmt.assign hGuyRhs hAssignGuy) hpay
          · intro out world' k' C' cur rdFail
            exact flapperX_tend_refund_call_failure
              (cA := cA) (gh := gh) (bl := bl) (σ := σworld) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (σcall := σworld) (h := by
                simpa [callCursor,
                  show UInt256.ofNat 2543 + ⟨1⟩ = UInt256.ofNat 2544 by native_decide]
                  using rdFail)
        simpa [refundThen, checkedExternalCallStmts] using
          BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
    simpa [payTail, refundThen] using
      (BlockProgress.iteTrue
        (cond := (.binary .ne sender (.storage (bidsF (.var "id") "guy"))))
        (thenB := refundThen) (elseB := []) (stmts := payTail)
        hcondTrue (by simpa using hbranch))

def flapperTendTimingGuardExpr : Expr :=
  .binary .or
    (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
    (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))

theorem flapperTendBodyRevertsLive (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_false evm id lot bid hlive
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hLive))

theorem flapperTendBodyRevertsGuy (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id = UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_false evm id lot bid hguy
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hGuy))

theorem flapperTendBodyRevertsTiming (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (hticGt :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendTicWordOfState evm id).toNat)
    (hticZero : flapperTendTicWordOfState evm id ≠ UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hTiming := flapperTendTimingGuard_eval_false evm id lot bid hticGt hticZero
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hTiming))

theorem flapperTendBodyRevertsEnd (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      ¬ (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_false evm id lot bid hend
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hEnd))

theorem flapperTendBodyRevertsLot (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot ≠ flapperTendLotWordOfState evm id) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_false evm id lot bid hlot
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hLot))

theorem flapperTendBodyRevertsBid (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot = flapperTendLotWordOfState evm id)
    (hbid :
      ¬ (flapperTendBidWordOfState evm id).toNat < bid.toNat) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let frame : Frame := { contract := contract, locals := flapperTendLocals id lot bid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_true evm id lot bid hlot
  have hBid := flapperTendBidGt_eval_false evm id lot bid hbid
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, flapperTendLocals, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLot) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hBid))

theorem flapperTendBodyRevertsBidOneOverflow (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot = flapperTendLotWordOfState evm id)
    (hbid :
      (flapperTendBidWordOfState evm id).toNat < bid.toNat)
    (hover : UInt256.size ≤ bid.toNat * flapperTendOneWord.toNat) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let locals := flapperTendLocals id lot bid
  let frame : Frame := { contract := contract, locals := locals }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_true evm id lot bid hlot
  have hBid := flapperTendBidGt_eval_true evm id lot bid hbid
  have hBidVar :
      evalExpr? config frame evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    simpa [frame, locals] using flapperTendVarBid_eval evm id lot bid
  have hOne :
      evalExpr? config frame evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hLetBidOne :
      evalExpr? config frame evm (mul256 (.var "bid") (.intLit ONE)) = .revert := by
    exact flapperTendMul256_eval_revert
      (x := bid) (y := flapperTendOneWord) hBidVar hOne hover
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, locals, flapperTendLocals, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLot) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBid) <|
        ExecBlock.consRevert (ExecStmt.letDeclRevert hLetBidOne))

theorem flapperTendBodyRevertsBegBidOverflow (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot = flapperTendLotWordOfState evm id)
    (hbid :
      (flapperTendBidWordOfState evm id).toNat < bid.toNat)
    (hbidOneFit : bid.toNat * flapperTendOneWord.toNat < UInt256.size)
    (hover :
      UInt256.size ≤
        (flapperTendBegWordOfState evm).toNat *
          (flapperTendBidWordOfState evm id).toNat) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let bidOne := UInt256.mul bid flapperTendOneWord
  let locals := flapperTendLocals id lot bid
  let frame : Frame := { contract := contract, locals := locals }
  let localsBidOne := flapperTendLocalsBidOne id lot bid bidOne
  let frameBidOne : Frame := { contract := contract, locals := localsBidOne }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_true evm id lot bid hlot
  have hBid := flapperTendBidGt_eval_true evm id lot bid hbid
  have hBidVar :
      evalExpr? config frame evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    simpa [frame, locals] using flapperTendVarBid_eval evm id lot bid
  have hOne :
      evalExpr? config frame evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hLetBidOne :
      evalExpr? config frame evm (mul256 (.var "bid") (.intLit ONE)) =
        .ok (.int (Int.ofNat bidOne.toNat)) := by
    simpa [bidOne] using flapperTendMul256_eval_ok
      (x := bid) (y := flapperTendOneWord) hBidVar hOne hbidOneFit
  have hGetBidOne : localsBidOne.get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
    simpa [localsBidOne, bidOne] using
      flapperTendLocalsBidOne_get_bidOne id lot bid bidOne
  have hBidVarOne :
      evalExpr? config frameBidOne evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    exact flapperTendVarInt_eval_of_get (evm := evm)
      (by simpa [frameBidOne, localsBidOne, bidOne] using
        flapperTendLocalsBidOne_get_bid id lot bid bidOne)
  have hOneOne :
      evalExpr? config frameBidOne evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hBidOneCheck :
      evalExpr? config frameBidOne evm
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
        .ok (.bool true) := by
    exact flapperTendCheckedMulGuard_eval_true (name := "bidOne")
      hGetBidOne hBidVarOne hOneOne hbidOneFit
  have hbaseBeg : localsBidOne.get? "beg" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hbaseBids : localsBidOne.get? "bids" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hgetId : localsBidOne.get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
    simpa [localsBidOne, bidOne] using flapperTendLocalsBidOne_get_id id lot bid bidOne
  have hBegEval :
      evalExpr? config frameBidOne evm (.storage begRef) =
        .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
    exact flapperTendBegStorage_eval_of_locals evm localsBidOne hbaseBeg
  have hOldBidEval :
      evalExpr? config frameBidOne evm (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
    exact flapperTendBidStorage_eval_of_locals evm localsBidOne id hbaseBids hgetId
  have hLetBegBid :
      evalExpr? config frameBidOne evm
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) = .revert := by
    exact flapperTendMul256_eval_revert
      (x := flapperTendBegWordOfState evm)
      (y := flapperTendBidWordOfState evm id)
      hBegEval hOldBidEval hover
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, locals, frameBidOne, localsBidOne, bidOne,
      flapperTendLocals, flapperTendLocalsBidOne, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLot) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBid) <|
        ExecBlock.consNormal (ExecStmt.letDecl hLetBidOne) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBidOneCheck) <|
        ExecBlock.consRevert (ExecStmt.letDeclRevert hLetBegBid))

theorem flapperTendBodyRevertsFloor (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot = flapperTendLotWordOfState evm id)
    (hbid :
      (flapperTendBidWordOfState evm id).toNat < bid.toNat)
    (hbidOneFit : bid.toNat * flapperTendOneWord.toNat < UInt256.size)
    (hbegFit :
      (flapperTendBegWordOfState evm).toNat *
          (flapperTendBidWordOfState evm id).toNat < UInt256.size)
    (hfloor :
      (UInt256.mul bid flapperTendOneWord).toNat <
        (UInt256.mul (flapperTendBegWordOfState evm)
          (flapperTendBidWordOfState evm id)).toNat) :
    ExecTransitionBody config contract evm (flapperTendLocals id lot bid)
      tendTransition.body .reverted := by
  let bidOne := UInt256.mul bid flapperTendOneWord
  let begBid := UInt256.mul (flapperTendBegWordOfState evm)
    (flapperTendBidWordOfState evm id)
  let locals := flapperTendLocals id lot bid
  let frame : Frame := { contract := contract, locals := locals }
  let localsBidOne := flapperTendLocalsBidOne id lot bid bidOne
  let frameBidOne : Frame := { contract := contract, locals := localsBidOne }
  let localsBegBid := flapperTendLocalsBegBid id lot bid bidOne begBid
  let frameBegBid : Frame := { contract := contract, locals := localsBegBid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_true evm id lot bid hlot
  have hBid := flapperTendBidGt_eval_true evm id lot bid hbid
  have hBidVar :
      evalExpr? config frame evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    simpa [frame, locals] using flapperTendVarBid_eval evm id lot bid
  have hOne :
      evalExpr? config frame evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hLetBidOne :
      evalExpr? config frame evm (mul256 (.var "bid") (.intLit ONE)) =
        .ok (.int (Int.ofNat bidOne.toNat)) := by
    simpa [bidOne] using flapperTendMul256_eval_ok
      (x := bid) (y := flapperTendOneWord) hBidVar hOne hbidOneFit
  have hGetBidOne : localsBidOne.get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
    simpa [localsBidOne, bidOne] using
      flapperTendLocalsBidOne_get_bidOne id lot bid bidOne
  have hBidVarOne :
      evalExpr? config frameBidOne evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    exact flapperTendVarInt_eval_of_get (evm := evm)
      (by simpa [frameBidOne, localsBidOne, bidOne] using
        flapperTendLocalsBidOne_get_bid id lot bid bidOne)
  have hOneOne :
      evalExpr? config frameBidOne evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hBidOneCheck :
      evalExpr? config frameBidOne evm
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
        .ok (.bool true) := by
    exact flapperTendCheckedMulGuard_eval_true (name := "bidOne")
      hGetBidOne hBidVarOne hOneOne hbidOneFit
  have hbaseBegOne : localsBidOne.get? "beg" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hbaseBidsOne : localsBidOne.get? "bids" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hgetIdOne : localsBidOne.get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
    simpa [localsBidOne, bidOne] using flapperTendLocalsBidOne_get_id id lot bid bidOne
  have hBegEvalOne :
      evalExpr? config frameBidOne evm (.storage begRef) =
        .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
    exact flapperTendBegStorage_eval_of_locals evm localsBidOne hbaseBegOne
  have hOldBidEvalOne :
      evalExpr? config frameBidOne evm (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
    exact flapperTendBidStorage_eval_of_locals evm localsBidOne id hbaseBidsOne hgetIdOne
  have hLetBegBid :
      evalExpr? config frameBidOne evm
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
        .ok (.int (Int.ofNat begBid.toNat)) := by
    simpa [begBid] using flapperTendMul256_eval_ok
      (x := flapperTendBegWordOfState evm)
      (y := flapperTendBidWordOfState evm id)
      hBegEvalOne hOldBidEvalOne hbegFit
  have hGetBegBid : localsBegBid.get? "begBid" =
      some (.int (Int.ofNat begBid.toNat)) := by
    simpa [localsBegBid, bidOne, begBid] using
      flapperTendLocalsBegBid_get_begBid id lot bid bidOne begBid
  have hbaseBeg : localsBegBid.get? "beg" = none := by
    exact flapperTendLocalsBegBid_get_none id lot bid bidOne begBid
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbaseBids : localsBegBid.get? "bids" = none := by
    exact flapperTendLocalsBegBid_get_none id lot bid bidOne begBid
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgetId : localsBegBid.get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
    simpa [localsBegBid, bidOne, begBid] using
      flapperTendLocalsBegBid_get_id id lot bid bidOne begBid
  have hBegEval :
      evalExpr? config frameBegBid evm (.storage begRef) =
        .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
    exact flapperTendBegStorage_eval_of_locals evm localsBegBid hbaseBeg
  have hOldBidEval :
      evalExpr? config frameBegBid evm (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
    exact flapperTendBidStorage_eval_of_locals evm localsBegBid id hbaseBids hgetId
  have hBegBidCheck :
      evalExpr? config frameBegBid evm
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "begBid") (.storage (bidsF (.var "id") "bid")))
            (.storage begRef))) =
        .ok (.bool true) := by
    exact flapperTendCheckedMulGuard_eval_true (name := "begBid")
      hGetBegBid hBegEval hOldBidEval hbegFit
  have hFloor :
      evalExpr? config frameBegBid evm
        (.binary .ge (.var "bidOne") (.var "begBid")) =
        .ok (.bool false) := by
    simpa [frameBegBid, localsBegBid, bidOne, begBid] using
      flapperTendFloorGuard_eval_false evm id lot bid bidOne begBid hfloor
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tendTransition, nonpayable, checkedMulUintInto, checkedExternalCallStmts,
      checkedAdd48Into, frame, locals, frameBidOne, localsBidOne, frameBegBid,
      localsBegBid, bidOne, begBid, flapperTendLocals, flapperTendLocalsBidOne,
      flapperTendLocalsBegBid, flapperTendTimingGuardExpr] using
      (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
        ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hLot) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBid) <|
        ExecBlock.consNormal (ExecStmt.letDecl hLetBidOne) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBidOneCheck) <|
        ExecBlock.consNormal (ExecStmt.letDecl hLetBegBid) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hBegBidCheck) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hFloor))

theorem flapperTendPrefixOk (evm : EVM.State) (id lot bid : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : flapperTendLiveWordOfState evm = UInt256.ofNat 1)
    (hguy : flapperTendGuyWordOfState evm id ≠ UInt256.ofNat 0)
    (htiming :
      evalExpr? config { contract := contract, locals := flapperTendLocals id lot bid }
        evm flapperTendTimingGuardExpr = .ok (.bool true))
    (hend :
      (flapperTendTimestampWordOfState evm).toNat <
        (flapperTendEndWordOfState evm id).toNat)
    (hlot : lot = flapperTendLotWordOfState evm id)
    (hbid :
      (flapperTendBidWordOfState evm id).toNat < bid.toNat)
    (hbidOneFit : bid.toNat * flapperTendOneWord.toNat < UInt256.size)
    (hbegFit :
      (flapperTendBegWordOfState evm).toNat *
          (flapperTendBidWordOfState evm id).toNat < UInt256.size)
    (hfloor :
      ¬ (UInt256.mul bid flapperTendOneWord).toNat <
        (UInt256.mul (flapperTendBegWordOfState evm)
          (flapperTendBidWordOfState evm id)).toNat) :
    ExecBlock config { contract := contract, locals := flapperTendLocals id lot bid } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr),
          .require flapperTendTimingGuardExpr,
          .require (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))),
          .require (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) ] ++
        checkedMulUintInto "bidOne" (.var "bid") (.intLit ONE) ++
        checkedMulUintInto "begBid" (.storage begRef)
          (.storage (bidsF (.var "id") "bid")) ++
        [ .require (.binary .ge (.var "bidOne") (.var "begBid")) ])
      (.ok
        { contract := contract,
          locals :=
            flapperTendLocalsBegBid id lot bid
              (UInt256.mul bid flapperTendOneWord)
              (UInt256.mul (flapperTendBegWordOfState evm)
                (flapperTendBidWordOfState evm id)) }
        evm) := by
  let bidOne := UInt256.mul bid flapperTendOneWord
  let begBid := UInt256.mul (flapperTendBegWordOfState evm)
    (flapperTendBidWordOfState evm id)
  let locals := flapperTendLocals id lot bid
  let frame : Frame := { contract := contract, locals := locals }
  let localsBidOne := flapperTendLocalsBidOne id lot bid bidOne
  let frameBidOne : Frame := { contract := contract, locals := localsBidOne }
  let localsBegBid := flapperTendLocalsBegBid id lot bid bidOne begBid
  let frameBegBid : Frame := { contract := contract, locals := localsBegBid }
  have hLive := flapperTendLiveGuard_eval_true evm id lot bid hlive
  have hGuy := flapperTendGuyNeZero_eval_true evm id lot bid hguy
  have hEnd := flapperTendEndGt_eval_true evm id lot bid hend
  have hLot := flapperTendLotEq_eval_true evm id lot bid hlot
  have hBid := flapperTendBidGt_eval_true evm id lot bid hbid
  have hBidVar :
      evalExpr? config frame evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    simpa [frame, locals] using flapperTendVarBid_eval evm id lot bid
  have hOne :
      evalExpr? config frame evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hLetBidOne :
      evalExpr? config frame evm (mul256 (.var "bid") (.intLit ONE)) =
        .ok (.int (Int.ofNat bidOne.toNat)) := by
    simpa [bidOne] using flapperTendMul256_eval_ok
      (x := bid) (y := flapperTendOneWord) hBidVar hOne hbidOneFit
  have hGetBidOne : localsBidOne.get? "bidOne" =
      some (.int (Int.ofNat bidOne.toNat)) := by
    simpa [localsBidOne, bidOne] using
      flapperTendLocalsBidOne_get_bidOne id lot bid bidOne
  have hBidVarOne :
      evalExpr? config frameBidOne evm (.var "bid") =
        .ok (.int (Int.ofNat bid.toNat)) := by
    exact flapperTendVarInt_eval_of_get (evm := evm)
      (by simpa [frameBidOne, localsBidOne, bidOne] using
        flapperTendLocalsBidOne_get_bid id lot bid bidOne)
  have hOneOne :
      evalExpr? config frameBidOne evm (.intLit ONE) =
        .ok (.int (Int.ofNat flapperTendOneWord.toNat)) := by
    unfold evalExpr?
    rw [flapperTendOneWord_toNat]
    rfl
  have hBidOneCheck :
      evalExpr? config frameBidOne evm
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
        .ok (.bool true) := by
    exact flapperTendCheckedMulGuard_eval_true (name := "bidOne")
      hGetBidOne hBidVarOne hOneOne hbidOneFit
  have hbaseBegOne : localsBidOne.get? "beg" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hbaseBidsOne : localsBidOne.get? "bids" = none := by
    exact flapperTendLocalsBidOne_get_none id lot bid bidOne
      (by decide) (by decide) (by decide) (by decide)
  have hgetIdOne : localsBidOne.get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
    simpa [localsBidOne, bidOne] using flapperTendLocalsBidOne_get_id id lot bid bidOne
  have hBegEvalOne :
      evalExpr? config frameBidOne evm (.storage begRef) =
        .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
    exact flapperTendBegStorage_eval_of_locals evm localsBidOne hbaseBegOne
  have hOldBidEvalOne :
      evalExpr? config frameBidOne evm (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
    exact flapperTendBidStorage_eval_of_locals evm localsBidOne id hbaseBidsOne hgetIdOne
  have hLetBegBid :
      evalExpr? config frameBidOne evm
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
        .ok (.int (Int.ofNat begBid.toNat)) := by
    simpa [begBid] using flapperTendMul256_eval_ok
      (x := flapperTendBegWordOfState evm)
      (y := flapperTendBidWordOfState evm id)
      hBegEvalOne hOldBidEvalOne hbegFit
  have hGetBegBid : localsBegBid.get? "begBid" =
      some (.int (Int.ofNat begBid.toNat)) := by
    simpa [localsBegBid, bidOne, begBid] using
      flapperTendLocalsBegBid_get_begBid id lot bid bidOne begBid
  have hbaseBeg : localsBegBid.get? "beg" = none := by
    exact flapperTendLocalsBegBid_get_none id lot bid bidOne begBid
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hbaseBids : localsBegBid.get? "bids" = none := by
    exact flapperTendLocalsBegBid_get_none id lot bid bidOne begBid
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hgetId : localsBegBid.get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
    simpa [localsBegBid, bidOne, begBid] using
      flapperTendLocalsBegBid_get_id id lot bid bidOne begBid
  have hBegEval :
      evalExpr? config frameBegBid evm (.storage begRef) =
        .ok (.int (Int.ofNat (flapperTendBegWordOfState evm).toNat)) := by
    exact flapperTendBegStorage_eval_of_locals evm localsBegBid hbaseBeg
  have hOldBidEval :
      evalExpr? config frameBegBid evm (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (flapperTendBidWordOfState evm id).toNat)) := by
    exact flapperTendBidStorage_eval_of_locals evm localsBegBid id hbaseBids hgetId
  have hBegBidCheck :
      evalExpr? config frameBegBid evm
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq
            (.binary .div (.var "begBid") (.storage (bidsF (.var "id") "bid")))
            (.storage begRef))) =
        .ok (.bool true) := by
    exact flapperTendCheckedMulGuard_eval_true (name := "begBid")
      hGetBegBid hBegEval hOldBidEval hbegFit
  have hFloor :
      evalExpr? config frameBegBid evm
        (.binary .ge (.var "bidOne") (.var "begBid")) =
        .ok (.bool true) := by
    simpa [frameBegBid, localsBegBid, bidOne, begBid] using
      flapperTendFloorGuard_eval_true evm id lot bid bidOne begBid
        (Nat.le_of_not_gt hfloor)
  simpa [nonpayable, checkedMulUintInto, frame, locals, frameBidOne, localsBidOne,
    frameBegBid, localsBegBid, bidOne, begBid, flapperTendLocals,
    flapperTendLocalsBidOne, flapperTendLocalsBegBid, flapperTendTimingGuardExpr] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hLive) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hGuy) <|
      ExecBlock.consNormal (ExecStmt.requireTrue htiming) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hEnd) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hLot) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hBid) <|
      ExecBlock.consNormal (ExecStmt.letDecl hLetBidOne) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hBidOneCheck) <|
      ExecBlock.consNormal (ExecStmt.letDecl hLetBegBid) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hBegBidCheck) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hFloor) ExecBlock.nil)

set_option maxHeartbeats 8000000 in
theorem flapperTendBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 14))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨524⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hselLit :
      ((⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) == I.calldata.extract 0 4) =
        true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 14) (by decide) hsel
  have hd : dispatchMsg contract I.calldata = some tendTransition :=
    flapperDispatch_tend hselLit
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdec := flapperDecode_tend_ok (I := I) hsz100
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let id := flapperTendIdWord I
    let lot := flapperTendLotArgWord I
    let bid := flapperTendBidArgWord I
    have hStateInit :
        CallStateRel
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          I (cA, σ_evm) evmSolm := by
      simpa [evmSolm] using
        (CallStateRel.initState
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀)
          (g := Sat256.ofUInt256 g) (A := A) (I := I) hAccounts)
    have hdecode := flapperX_tend_decode_ok
      (g := Sat256.ofUInt256 g) hsize hsz100 hreach
    have hloadLiveEq :
        flapperTendLiveWordOfState evmSolm =
          storageRead I.codeOwner σ_evm (UInt256.ofNat 7) := by
      simpa [flapperTendLiveWordOfState, flapperDealLiveWordOfState, evmSolm,
        initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 7)
    have hPackedLoadEq :
        flapperTendPackedWordOfState evmSolm id =
          storageRead I.codeOwner σ_evm (flapperTendPackedSlot id) := by
      simpa [flapperTendPackedWordOfState, flapperDealPackedWordOfState,
        flapperYankPackedWordOfState, evmSolm, initState, id] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (flapperTendPackedSlot id)
    have hPackedLoadEqRaw :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (UInt256.ofNat 2 + flapperYankBaseSlot (flapperYankIdWord I)) =
          storageRead I.codeOwner σ_evm
            (UInt256.ofNat 2 + flapperYankBaseSlot (flapperYankIdWord I)) := by
      simpa [evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 2 + flapperYankBaseSlot (flapperYankIdWord I))
    have hGuyWordSolm :
        flapperTendGuyWordOfState evmSolm id = flapperTendGuyWord σ_evm I := by
      simp [flapperTendGuyWordOfState, flapperTendGuyWord,
        flapperDealGuyWordOfState, flapperDealGuyWord, flapperYankGuyWordOfState,
        flapperYankGuyWord, flapperTendPackedWordOfState, flapperTendPackedWord,
        flapperDealPackedWordOfState, flapperDealPackedWord,
        flapperYankPackedWordOfState, flapperYankPackedWord, flapperTendPackedSlot,
        flapperDealPackedSlot, flapperYankPackedSlot, hPackedLoadEq,
        hPackedLoadEqRaw, id,
        flapperTendIdWord, flapperDealIdWord, u256_add_comm, u256_land_comm]
    have hTicWordSolm :
        flapperTendTicWordOfState evmSolm id = flapperTendTicWord σ_evm I := by
      simp [flapperTendTicWordOfState, flapperTendTicWord,
        flapperDealTicWordOfState, flapperDealTicWord,
        flapperTendPackedWordOfState, flapperTendPackedWord,
        flapperDealPackedWordOfState, flapperDealPackedWord,
        flapperYankPackedWordOfState, flapperYankPackedWord, flapperTendPackedSlot,
        flapperDealPackedSlot, flapperYankPackedSlot, hPackedLoadEq,
        hPackedLoadEqRaw, id,
        flapperTendIdWord, flapperDealIdWord, u256_add_comm, u256_land_comm]
    have hEndWordSolm :
        flapperTendEndWordOfState evmSolm id = flapperTendEndWord σ_evm I := by
      simp [flapperTendEndWordOfState, flapperTendEndWord,
        flapperDealEndWordOfState, flapperDealEndWord,
        flapperTendPackedWordOfState, flapperTendPackedWord,
        flapperDealPackedWordOfState, flapperDealPackedWord,
        flapperYankPackedWordOfState, flapperYankPackedWord, flapperTendPackedSlot,
        flapperDealPackedSlot, flapperYankPackedSlot, hPackedLoadEq,
        hPackedLoadEqRaw, id,
        flapperTendIdWord, flapperDealIdWord, u256_add_comm, u256_land_comm]
    have hTimestampSolm :
        flapperTendTimestampWordOfState evmSolm = flapperTendTimestampWord I := by
      simp [flapperTendTimestampWordOfState, flapperTendTimestampWord,
        flapperDealTimestampWordOfState, flapperDealTimestampWord, evmSolm, initState]
    have hLotWordSolm :
        flapperTendLotWordOfState evmSolm id = flapperTendLotWord σ_evm I := by
      simpa [flapperTendLotWordOfState, flapperTendLotWord,
        flapperDealLotWordOfState, flapperDealLotWord, evmSolm, initState, id,
        flapperTendIdWord, flapperDealIdWord] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (flapperTendBaseSlot id + UInt256.ofNat 1)
    have hBegWordSolm :
        flapperTendBegWordOfState evmSolm = flapperTendBegWord σ_evm I := by
      simpa [flapperTendBegWordOfState, flapperTendBegWord, evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 4)
    have hBidWordSolm :
        flapperTendBidWordOfState evmSolm id = flapperTendBidWord σ_evm I := by
      simpa [flapperTendBidWordOfState, flapperTendBidWord,
        flapperDealBidWordOfState, flapperDealBidWord, flapperYankBidWordOfState,
        flapperYankBidWord, evmSolm, initState, id, flapperTendIdWord,
        flapperDealIdWord, flapperTendBaseSlot, flapperDealBaseSlot] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (flapperTendBaseSlot id)
    by_cases hliveEvm : storageRead I.codeOwner σ_evm (UInt256.ofNat 7) = UInt256.ofNat 1
    · have h1704 := flapperX_tend_live_ok
        (g := Sat256.ofUInt256 g) hliveEvm hdecode
      have hliveSolm :
          flapperTendLiveWordOfState evmSolm = UInt256.ofNat 1 := by
        rw [hloadLiveEq, hliveEvm]
      by_cases hguyEvm : flapperTendGuyWord σ_evm I = UInt256.ofNat 0
      · have hguySolm :
            flapperTendGuyWordOfState evmSolm id = UInt256.ofNat 0 := by
          rw [hGuyWordSolm, hguyEvm]
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperTendLocals id lot bid)
              tendTransition.body .reverted := by
          simpa [evmSolm, id, lot, bid] using
            flapperTendBodyRevertsGuy evmSolm id lot bid
              (by simp only [evmSolm, initState]; exact hwv)
              hliveSolm hguySolm
        exact (flapperX_tend_guy_revert
            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I) hguyEvm h1704)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have h1802 := flapperX_tend_guy_ok
            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I) hguyEvm h1704
        have hguySolm :
            flapperTendGuyWordOfState evmSolm id ≠ UInt256.ofNat 0 := by
          intro hzero
          exact hguyEvm (by rw [← hGuyWordSolm]; exact hzero)
        by_cases hticGtEvm :
            (flapperTendTimestampWord I).toNat < (flapperTendTicWord σ_evm I).toNat
        · have hticGtSolm :
              (flapperTendTimestampWordOfState evmSolm).toNat <
                (flapperTendTicWordOfState evmSolm id).toNat := by
            simpa [hTimestampSolm, hTicWordSolm] using hticGtEvm
          have htiming :
              evalExpr? config
                { contract := contract, locals := flapperTendLocals id lot bid }
                evmSolm flapperTendTimingGuardExpr = .ok (.bool true) := by
            simpa [flapperTendTimingGuardExpr] using
              flapperTendTimingGuard_eval_true_tic evmSolm id lot bid hticGtSolm
          have h1960 := flapperX_tend_tic_gt_ok
            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
            hticGtEvm h1802
          by_cases hendEvm :
              (flapperTendTimestampWord I).toNat < (flapperTendEndWord σ_evm I).toNat
          · have hendSolm :
                (flapperTendTimestampWordOfState evmSolm).toNat <
                  (flapperTendEndWordOfState evmSolm id).toNat := by
              simpa [hTimestampSolm, hEndWordSolm] using hendEvm
            have h2077 := flapperX_tend_end_ok
              (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
              hendEvm h1960
            by_cases hlotEvm : flapperTendLotArgWord I = flapperTendLotWord σ_evm I
            · have hlotSolm : lot = flapperTendLotWordOfState evmSolm id := by
                simpa [lot, hLotWordSolm] using hlotEvm
              have h2179 := flapperX_tend_lot_ok
                (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                hlotEvm h2077
              by_cases hbidEvm :
                  (flapperTendBidWord σ_evm I).toNat < (flapperTendBidArgWord I).toNat
              · have h2270 := flapperX_tend_bid_ok
                  (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                  hbidEvm h2179
                have hbidSolm :
                    (flapperTendBidWordOfState evmSolm id).toNat < bid.toNat := by
                  simpa [hBidWordSolm, bid] using hbidEvm
                by_cases hBegFit :
                    (flapperTendBegWord σ_evm I).toNat *
                        (flapperTendBidWord σ_evm I).toNat < UInt256.size
                · by_cases hBidOneFit :
                      (flapperTendBidArgWord I).toNat *
                          flapperTendOneWord.toNat < UInt256.size
                  · by_cases hfloor :
                        (flapperTendBidOneWord I).toNat <
                          (flapperTendBegBidWord σ_evm I).toNat
                    · have hBegFitSolm :
                          (flapperTendBegWordOfState evmSolm).toNat *
                              (flapperTendBidWordOfState evmSolm id).toNat <
                            UInt256.size := by
                        simpa [hBegWordSolm, hBidWordSolm] using hBegFit
                      have hBidOneFitSolm :
                          bid.toNat * flapperTendOneWord.toNat < UInt256.size := by
                        simpa [bid] using hBidOneFit
                      have hfloorSolm :
                          (UInt256.mul bid flapperTendOneWord).toNat <
                            (UInt256.mul (flapperTendBegWordOfState evmSolm)
                              (flapperTendBidWordOfState evmSolm id)).toNat := by
                        simpa [flapperTendBidOneWord, flapperTendBegBidWord, bid,
                          hBegWordSolm, hBidWordSolm] using hfloor
                      have hbody :
                          ExecTransitionBody config contract evmSolm
                            (flapperTendLocals id lot bid) tendTransition.body
                            .reverted := by
                        simpa [evmSolm, id, lot, bid] using
                          flapperTendBodyRevertsFloor evmSolm id lot bid
                            (by simp only [evmSolm, initState]; exact hwv)
                            hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                            hBidOneFitSolm hBegFitSolm hfloorSolm
                      exact (flapperX_tend_checkedMul_floor_revert
                          (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                          hBegFit hBidOneFit hfloor h2270)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                    · have h2399 := flapperX_tend_checkedMul_floor_ok
                        (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                        hBegFit hBidOneFit hfloor h2270
                      have hBegFitSolm :
                          (flapperTendBegWordOfState evmSolm).toNat *
                              (flapperTendBidWordOfState evmSolm id).toNat <
                            UInt256.size := by
                        simpa [hBegWordSolm, hBidWordSolm] using hBegFit
                      have hBidOneFitSolm :
                          bid.toNat * flapperTendOneWord.toNat < UInt256.size := by
                        simpa [bid] using hBidOneFit
                      have hfloorSolm :
                          ¬ (UInt256.mul bid flapperTendOneWord).toNat <
                            (UInt256.mul (flapperTendBegWordOfState evmSolm)
                              (flapperTendBidWordOfState evmSolm id)).toNat := by
                        intro hbad
                        exact hfloor (by
                          simpa [flapperTendBidOneWord, flapperTendBegBidWord, bid,
                            hBegWordSolm, hBidWordSolm] using hbad)
                      have hpref :
                          ExecBlock config
                            { contract := contract, locals := flapperTendLocals id lot bid }
                            evmSolm
                            (nonpayable ++
                              [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                                .require
                                  (.binary .ne (.storage (bidsF (.var "id") "guy"))
                                    zeroAddr),
                                .require flapperTendTimingGuardExpr,
                                .require
                                  (.binary .gt (.storage (bidsF (.var "id") "end"))
                                    (.env .timestamp)),
                                .require
                                  (.binary .eq (.var "lot")
                                    (.storage (bidsF (.var "id") "lot"))),
                                .require
                                  (.binary .gt (.var "bid")
                                    (.storage (bidsF (.var "id") "bid"))) ] ++
                              checkedMulUintInto "bidOne" (.var "bid") (.intLit ONE) ++
                              checkedMulUintInto "begBid" (.storage begRef)
                                (.storage (bidsF (.var "id") "bid")) ++
                              [ .require (.binary .ge (.var "bidOne") (.var "begBid")) ])
                            (.ok
                              { contract := contract,
                                locals :=
                                  flapperTendLocalsBegBid id lot bid
                                    (UInt256.mul bid flapperTendOneWord)
                                    (UInt256.mul (flapperTendBegWordOfState evmSolm)
                                      (flapperTendBidWordOfState evmSolm id)) }
                              evmSolm) := by
                        simpa [evmSolm, id, lot, bid] using
                          flapperTendPrefixOk evmSolm id lot bid
                            (by simp only [evmSolm, initState]; exact hwv)
                            hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                            hBidOneFitSolm hBegFitSolm hfloorSolm
                      let bidOneTail := UInt256.mul bid flapperTendOneWord
                      let begBidTail := UInt256.mul (flapperTendBegWordOfState evmSolm)
                        (flapperTendBidWordOfState evmSolm id)
                      let localsTail := flapperTendLocalsBegBid id lot bid bidOneTail
                        begBidTail
                      have hbaseGemTail : localsTail.get? "gem" = none := by
                        simpa [localsTail, bidOneTail, begBidTail] using
                          flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                            (by decide) (by decide) (by decide) (by decide) (by decide)
                      have hbaseBidsTail : localsTail.get? "bids" = none := by
                        simpa [localsTail, bidOneTail, begBidTail] using
                          flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                            (by decide) (by decide) (by decide) (by decide) (by decide)
                      have hbaseTtlTail : localsTail.get? "ttl" = none := by
                        simpa [localsTail, bidOneTail, begBidTail] using
                          flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                            (by decide) (by decide) (by decide) (by decide) (by decide)
                      have hgetIdTail : localsTail.get? "id" =
                          some (.int (Int.ofNat (flapperTendIdWord I).toNat)) := by
                        simpa [localsTail, bidOneTail, begBidTail, id] using
                          flapperTendLocalsBegBid_get_id id lot bid bidOneTail begBidTail
                      have hgetBidTail : localsTail.get? "bid" =
                          some (.int (Int.ofNat (flapperTendBidArgWord I).toNat)) := by
                        simpa [localsTail, bidOneTail, begBidTail, bid] using
                          flapperTendLocalsBegBid_get_bid id lot bid bidOneTail begBidTail
                      let mem1 := flapperTendScratchMem id solcFreePtrMem
                      let mem2 := flapperTendScratchMem id mem1
                      let mem3 := flapperTendScratchMem id mem2
                      let mem4 := flapperTendScratchMem id mem3
                      let mem5 := flapperTendScratchMem id mem4
                      let mem2399 := flapperTendScratchMem id mem5
                      have hmem0 : 96 ≤ solcFreePtrMem.size := by
                        rw [solcFreePtrMem_size]
                      have hread0 :
                          solcFreePtrMem.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa using solcFreePtrMem_read64
                      have hmem1 : 96 ≤ mem1.size := by
                        simpa [mem1] using
                          flapperTendScratchMem_size_ge_96 id solcFreePtrMem hmem0
                      have hread1 :
                          mem1.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem1] using
                          flapperTendScratchMem_read64 id solcFreePtrMem hmem0 hread0
                      have hmem2 : 96 ≤ mem2.size := by
                        simpa [mem2] using
                          flapperTendScratchMem_size_ge_96 id mem1 hmem1
                      have hread2 :
                          mem2.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem2] using
                          flapperTendScratchMem_read64 id mem1 hmem1 hread1
                      have hmem3 : 96 ≤ mem3.size := by
                        simpa [mem3] using
                          flapperTendScratchMem_size_ge_96 id mem2 hmem2
                      have hread3 :
                          mem3.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem3] using
                          flapperTendScratchMem_read64 id mem2 hmem2 hread2
                      have hmem4 : 96 ≤ mem4.size := by
                        simpa [mem4] using
                          flapperTendScratchMem_size_ge_96 id mem3 hmem3
                      have hread4 :
                          mem4.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem4] using
                          flapperTendScratchMem_read64 id mem3 hmem3 hread3
                      have hmem5 : 96 ≤ mem5.size := by
                        simpa [mem5] using
                          flapperTendScratchMem_size_ge_96 id mem4 hmem4
                      have hread5 :
                          mem5.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem5] using
                          flapperTendScratchMem_read64 id mem4 hmem4 hread4
                      have hmem2399 : 96 ≤ mem2399.size := by
                        simpa [mem2399] using
                          flapperTendScratchMem_size_ge_96 id mem5 hmem5
                      have hread2399 :
                          mem2399.readWithPadding 64 32 =
                            UInt256.toByteArray (UInt256.ofNat 128) := by
                        simpa [mem2399] using
                          flapperTendScratchMem_read64 id mem5 hmem5 hread5
                      have htail :
                          BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            config { contract := contract, locals := localsTail }
                            evmSolm
                            ([ .ite
                                (.binary .ne sender
                                  (.storage (bidsF (.var "id") "guy")))
                                (checkedExternalCallStmts (.storage gemRef) "move"
                                    (.intLit 0)
                                    [sender, .storage (bidsF (.var "id") "guy"),
                                      .storage (bidsF (.var "id") "bid")]
                                    "_refundRet" ++
                                  [ .assign .storage
                                      (bidsF (.var "id") "guy") sender ])
                                [] ] ++
                             checkedExternalCallStmts (.storage gemRef) "move" (.intLit 0)
                              [sender, thisAddr,
                                wrap256 (.binary .sub (.var "bid")
                                  (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
                             [ .assign .storage (bidsF (.var "id") "bid")
                                (.var "bid") ] ++
                             checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                             [ .assign .storage (bidsF (.var "id") "tic")
                                (.var "tic_") ])
                            (runtimeExit (.abi tendTransition.returnType)) := by
                        simpa [localsTail, bidOneTail, begBidTail, mem2399, id, bid] using
                          flapperTendExternalTailProgress
                            (cA := cA) (gh := gh) (bl := bl) (σworld := σ_evm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (sel := flapperSelWord I) (mem2399 := mem2399)
                            (evm := evmSolm) (locals := localsTail)
                            hStateInit hperm hbaseGemTail hbaseBidsTail hbaseTtlTail
                            hgetIdTail hgetBidTail hmem2399 hread2399
                            (by simpa [mem2399, mem5, mem4, mem3, mem2, mem1, id]
                              using h2399)
                      have hprogress :
                          BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            config
                            { contract := contract, locals := flapperTendLocals id lot bid }
                            evmSolm tendTransition.body
                            (runtimeExit (.abi tendTransition.returnType)) := by
                        have hp := BlockProgress.prepend hpref htail
                        simpa [tendTransition, nonpayable, checkedExternalCallStmts,
                          checkedMulUintInto, checkedAdd48Into,
                          flapperTendTimingGuardExpr, localsTail, bidOneTail, begBidTail,
                          flapperTendLocalsBegBid, evmSolm, id, lot, bid] using hp
                      exact hprogress.toRuntimeEquivalenceFor hcode
                        (fun result hfunc => by
                          exact solmExec.intro (flapperSelectorDispatch_tend hselLit)
                            rfl hdec
                            (by simp [evmSolm, initState, Sat256.ofUInt256,
                              Sat256.toUInt256])
                            hfunc)
                        (by intro result endpoint h; exact h)
                  · have hBidOneOverflow :
                        UInt256.size ≤
                          (flapperTendBidArgWord I).toNat *
                            flapperTendOneWord.toNat := by
                      exact Nat.le_of_not_gt hBidOneFit
                    have hbody :
                        ExecTransitionBody config contract evmSolm
                          (flapperTendLocals id lot bid) tendTransition.body
                          .reverted := by
                      have hBidOneOverflowSolm :
                          UInt256.size ≤ bid.toNat * flapperTendOneWord.toNat := by
                        simpa [bid] using hBidOneOverflow
                      simpa [evmSolm, id, lot, bid] using
                        flapperTendBodyRevertsBidOneOverflow evmSolm id lot bid
                          (by simp only [evmSolm, initState]; exact hwv)
                          hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                          hBidOneOverflowSolm
                    exact (flapperX_tend_bidOne_overflow_revert
                        (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                        hBegFit hBidOneOverflow h2270)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hBegOverflow :
                      UInt256.size ≤
                        (flapperTendBegWord σ_evm I).toNat *
                          (flapperTendBidWord σ_evm I).toNat := by
                    exact Nat.le_of_not_gt hBegFit
                  have hbody :
                      ExecTransitionBody config contract evmSolm
                        (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                    by_cases hBidOneFit :
                        bid.toNat * flapperTendOneWord.toNat < UInt256.size
                    · have hBegOverflowSolm :
                          UInt256.size ≤
                            (flapperTendBegWordOfState evmSolm).toNat *
                              (flapperTendBidWordOfState evmSolm id).toNat := by
                        simpa [hBegWordSolm, hBidWordSolm] using hBegOverflow
                      simpa [evmSolm, id, lot, bid] using
                        flapperTendBodyRevertsBegBidOverflow evmSolm id lot bid
                          (by simp only [evmSolm, initState]; exact hwv)
                          hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                          hBidOneFit hBegOverflowSolm
                    · have hBidOneOverflow :
                          UInt256.size ≤ bid.toNat * flapperTendOneWord.toNat := by
                        exact Nat.le_of_not_gt hBidOneFit
                      simpa [evmSolm, id, lot, bid] using
                        flapperTendBodyRevertsBidOneOverflow evmSolm id lot bid
                          (by simp only [evmSolm, initState]; exact hwv)
                          hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                          hBidOneOverflow
                  exact (flapperX_tend_begBid_overflow_revert
                      (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                      hBegOverflow h2270)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hbidSolm :
                    ¬ (flapperTendBidWordOfState evmSolm id).toNat < bid.toNat := by
                  intro hbad
                  exact hbidEvm (by simpa [hBidWordSolm, bid] using hbad)
                have hbody :
                    ExecTransitionBody config contract evmSolm
                      (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                  simpa [evmSolm, id, lot, bid] using
                    flapperTendBodyRevertsBid evmSolm id lot bid
                      (by simp only [evmSolm, initState]; exact hwv)
                      hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                exact (flapperX_tend_bid_revert
                    (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                    hbidEvm h2179)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hlotSolm : lot ≠ flapperTendLotWordOfState evmSolm id := by
                intro hbad
                exact hlotEvm (by simpa [lot, hLotWordSolm] using hbad)
              have hbody :
                  ExecTransitionBody config contract evmSolm
                    (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                simpa [evmSolm, id, lot, bid] using
                  flapperTendBodyRevertsLot evmSolm id lot bid
                    (by simp only [evmSolm, initState]; exact hwv)
                    hliveSolm hguySolm htiming hendSolm hlotSolm
              exact (flapperX_tend_lot_revert
                  (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                  hlotEvm h2077)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hendSolm :
                ¬ (flapperTendTimestampWordOfState evmSolm).toNat <
                  (flapperTendEndWordOfState evmSolm id).toNat := by
              intro hbad
              exact hendEvm (by simpa [hTimestampSolm, hEndWordSolm] using hbad)
            have hbody :
                ExecTransitionBody config contract evmSolm
                  (flapperTendLocals id lot bid) tendTransition.body .reverted := by
              simpa [evmSolm, id, lot, bid] using
                flapperTendBodyRevertsEnd evmSolm id lot bid
                  (by simp only [evmSolm, initState]; exact hwv)
                  hliveSolm hguySolm htiming hendSolm
            exact (flapperX_tend_end_revert
                (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                hendEvm h1960)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · by_cases hticZeroEvm : flapperTendTicWord σ_evm I = UInt256.ofNat 0
          · have hticGtSolm :
                ¬ (flapperTendTimestampWordOfState evmSolm).toNat <
                  (flapperTendTicWordOfState evmSolm id).toNat := by
              intro hbad
              exact hticGtEvm (by simpa [hTimestampSolm, hTicWordSolm] using hbad)
            have hticZeroSolm :
                flapperTendTicWordOfState evmSolm id = UInt256.ofNat 0 := by
              rw [hTicWordSolm, hticZeroEvm]
            have htiming :
                evalExpr? config
                  { contract := contract, locals := flapperTendLocals id lot bid }
                  evmSolm flapperTendTimingGuardExpr = .ok (.bool true) := by
              simpa [flapperTendTimingGuardExpr] using
                flapperTendTimingGuard_eval_true_zero evmSolm id lot bid
                  hticGtSolm hticZeroSolm
            have h1960 := flapperX_tend_tic_zero_ok
              (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
              hticGtEvm hticZeroEvm h1802
            by_cases hendEvm :
                (flapperTendTimestampWord I).toNat <
                  (flapperTendEndWord σ_evm I).toNat
            · have hendSolm :
                  (flapperTendTimestampWordOfState evmSolm).toNat <
                    (flapperTendEndWordOfState evmSolm id).toNat := by
                simpa [hTimestampSolm, hEndWordSolm] using hendEvm
              have h2077 := flapperX_tend_end_ok
                (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                hendEvm h1960
              by_cases hlotEvm : flapperTendLotArgWord I = flapperTendLotWord σ_evm I
              · have hlotSolm : lot = flapperTendLotWordOfState evmSolm id := by
                  simpa [lot, hLotWordSolm] using hlotEvm
                have h2179 := flapperX_tend_lot_ok
                  (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                  hlotEvm h2077
                by_cases hbidEvm :
                    (flapperTendBidWord σ_evm I).toNat <
                      (flapperTendBidArgWord I).toNat
                · have h2270 := flapperX_tend_bid_ok
                    (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                    hbidEvm h2179
                  have hbidSolm :
                      (flapperTendBidWordOfState evmSolm id).toNat < bid.toNat := by
                    simpa [hBidWordSolm, bid] using hbidEvm
                  by_cases hBegFit :
                      (flapperTendBegWord σ_evm I).toNat *
                          (flapperTendBidWord σ_evm I).toNat < UInt256.size
                  · by_cases hBidOneFit :
                        (flapperTendBidArgWord I).toNat *
                            flapperTendOneWord.toNat < UInt256.size
                    · by_cases hfloor :
                          (flapperTendBidOneWord I).toNat <
                            (flapperTendBegBidWord σ_evm I).toNat
                      · have hBegFitSolm :
                            (flapperTendBegWordOfState evmSolm).toNat *
                                (flapperTendBidWordOfState evmSolm id).toNat <
                              UInt256.size := by
                          simpa [hBegWordSolm, hBidWordSolm] using hBegFit
                        have hBidOneFitSolm :
                            bid.toNat * flapperTendOneWord.toNat < UInt256.size := by
                          simpa [bid] using hBidOneFit
                        have hfloorSolm :
                            (UInt256.mul bid flapperTendOneWord).toNat <
                              (UInt256.mul (flapperTendBegWordOfState evmSolm)
                                (flapperTendBidWordOfState evmSolm id)).toNat := by
                          simpa [flapperTendBidOneWord, flapperTendBegBidWord, bid,
                            hBegWordSolm, hBidWordSolm] using hfloor
                        have hbody :
                            ExecTransitionBody config contract evmSolm
                              (flapperTendLocals id lot bid) tendTransition.body
                              .reverted := by
                          simpa [evmSolm, id, lot, bid] using
                            flapperTendBodyRevertsFloor evmSolm id lot bid
                              (by simp only [evmSolm, initState]; exact hwv)
                              hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                              hBidOneFitSolm hBegFitSolm hfloorSolm
                        exact (flapperX_tend_checkedMul_floor_revert
                            (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                            hBegFit hBidOneFit hfloor h2270)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
                      · have h2399 := flapperX_tend_checkedMul_floor_ok
                          (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                          hBegFit hBidOneFit hfloor h2270
                        have hBegFitSolm :
                            (flapperTendBegWordOfState evmSolm).toNat *
                                (flapperTendBidWordOfState evmSolm id).toNat <
                              UInt256.size := by
                          simpa [hBegWordSolm, hBidWordSolm] using hBegFit
                        have hBidOneFitSolm :
                            bid.toNat * flapperTendOneWord.toNat < UInt256.size := by
                          simpa [bid] using hBidOneFit
                        have hfloorSolm :
                            ¬ (UInt256.mul bid flapperTendOneWord).toNat <
                              (UInt256.mul (flapperTendBegWordOfState evmSolm)
                                (flapperTendBidWordOfState evmSolm id)).toNat := by
                          intro hbad
                          exact hfloor (by
                            simpa [flapperTendBidOneWord, flapperTendBegBidWord, bid,
                              hBegWordSolm, hBidWordSolm] using hbad)
                        have hpref :
                            ExecBlock config
                              { contract := contract, locals := flapperTendLocals id lot bid }
                              evmSolm
                              (nonpayable ++
                                [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
                                  .require
                                    (.binary .ne (.storage (bidsF (.var "id") "guy"))
                                      zeroAddr),
                                  .require flapperTendTimingGuardExpr,
                                  .require
                                    (.binary .gt (.storage (bidsF (.var "id") "end"))
                                      (.env .timestamp)),
                                  .require
                                    (.binary .eq (.var "lot")
                                      (.storage (bidsF (.var "id") "lot"))),
                                  .require
                                    (.binary .gt (.var "bid")
                                      (.storage (bidsF (.var "id") "bid"))) ] ++
                                checkedMulUintInto "bidOne" (.var "bid") (.intLit ONE) ++
                                checkedMulUintInto "begBid" (.storage begRef)
                                  (.storage (bidsF (.var "id") "bid")) ++
                                [ .require
                                    (.binary .ge (.var "bidOne") (.var "begBid")) ])
                              (.ok
                                { contract := contract,
                                  locals :=
                                    flapperTendLocalsBegBid id lot bid
                                      (UInt256.mul bid flapperTendOneWord)
                                      (UInt256.mul (flapperTendBegWordOfState evmSolm)
                                        (flapperTendBidWordOfState evmSolm id)) }
                                evmSolm) := by
                          simpa [evmSolm, id, lot, bid] using
                            flapperTendPrefixOk evmSolm id lot bid
                              (by simp only [evmSolm, initState]; exact hwv)
                              hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                              hBidOneFitSolm hBegFitSolm hfloorSolm
                        let bidOneTail := UInt256.mul bid flapperTendOneWord
                        let begBidTail := UInt256.mul (flapperTendBegWordOfState evmSolm)
                          (flapperTendBidWordOfState evmSolm id)
                        let localsTail := flapperTendLocalsBegBid id lot bid bidOneTail
                          begBidTail
                        have hbaseGemTail : localsTail.get? "gem" = none := by
                          simpa [localsTail, bidOneTail, begBidTail] using
                            flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                              (by decide) (by decide) (by decide) (by decide) (by decide)
                        have hbaseBidsTail : localsTail.get? "bids" = none := by
                          simpa [localsTail, bidOneTail, begBidTail] using
                            flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                              (by decide) (by decide) (by decide) (by decide) (by decide)
                        have hbaseTtlTail : localsTail.get? "ttl" = none := by
                          simpa [localsTail, bidOneTail, begBidTail] using
                            flapperTendLocalsBegBid_get_none id lot bid bidOneTail begBidTail
                              (by decide) (by decide) (by decide) (by decide) (by decide)
                        have hgetIdTail : localsTail.get? "id" =
                            some (.int (Int.ofNat (flapperTendIdWord I).toNat)) := by
                          simpa [localsTail, bidOneTail, begBidTail, id] using
                            flapperTendLocalsBegBid_get_id id lot bid bidOneTail begBidTail
                        have hgetBidTail : localsTail.get? "bid" =
                            some (.int (Int.ofNat (flapperTendBidArgWord I).toNat)) := by
                          simpa [localsTail, bidOneTail, begBidTail, bid] using
                            flapperTendLocalsBegBid_get_bid id lot bid bidOneTail begBidTail
                        let mem1 := flapperTendScratchMem id solcFreePtrMem
                        let mem2 := flapperTendScratchMem id mem1
                        let mem3 := flapperTendScratchMem id mem2
                        let mem4 := flapperTendScratchMem id mem3
                        let mem5 := flapperTendScratchMem id mem4
                        let mem6 := flapperTendScratchMem id mem5
                        let mem2399 := flapperTendScratchMem id mem6
                        have hmem0 : 96 ≤ solcFreePtrMem.size := by
                          rw [solcFreePtrMem_size]
                        have hread0 :
                            solcFreePtrMem.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa using solcFreePtrMem_read64
                        have hmem1 : 96 ≤ mem1.size := by
                          simpa [mem1] using
                            flapperTendScratchMem_size_ge_96 id solcFreePtrMem hmem0
                        have hread1 :
                            mem1.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem1] using
                            flapperTendScratchMem_read64 id solcFreePtrMem hmem0 hread0
                        have hmem2 : 96 ≤ mem2.size := by
                          simpa [mem2] using
                            flapperTendScratchMem_size_ge_96 id mem1 hmem1
                        have hread2 :
                            mem2.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem2] using
                            flapperTendScratchMem_read64 id mem1 hmem1 hread1
                        have hmem3 : 96 ≤ mem3.size := by
                          simpa [mem3] using
                            flapperTendScratchMem_size_ge_96 id mem2 hmem2
                        have hread3 :
                            mem3.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem3] using
                            flapperTendScratchMem_read64 id mem2 hmem2 hread2
                        have hmem4 : 96 ≤ mem4.size := by
                          simpa [mem4] using
                            flapperTendScratchMem_size_ge_96 id mem3 hmem3
                        have hread4 :
                            mem4.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem4] using
                            flapperTendScratchMem_read64 id mem3 hmem3 hread3
                        have hmem5 : 96 ≤ mem5.size := by
                          simpa [mem5] using
                            flapperTendScratchMem_size_ge_96 id mem4 hmem4
                        have hread5 :
                            mem5.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem5] using
                            flapperTendScratchMem_read64 id mem4 hmem4 hread4
                        have hmem6 : 96 ≤ mem6.size := by
                          simpa [mem6] using
                            flapperTendScratchMem_size_ge_96 id mem5 hmem5
                        have hread6 :
                            mem6.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem6] using
                            flapperTendScratchMem_read64 id mem5 hmem5 hread5
                        have hmem2399 : 96 ≤ mem2399.size := by
                          simpa [mem2399] using
                            flapperTendScratchMem_size_ge_96 id mem6 hmem6
                        have hread2399 :
                            mem2399.readWithPadding 64 32 =
                              UInt256.toByteArray (UInt256.ofNat 128) := by
                          simpa [mem2399] using
                            flapperTendScratchMem_read64 id mem6 hmem6 hread6
                        have htail :
                            BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              config { contract := contract, locals := localsTail }
                              evmSolm
                              ([ .ite
                                  (.binary .ne sender
                                    (.storage (bidsF (.var "id") "guy")))
                                  (checkedExternalCallStmts (.storage gemRef) "move"
                                      (.intLit 0)
                                      [sender, .storage (bidsF (.var "id") "guy"),
                                        .storage (bidsF (.var "id") "bid")]
                                      "_refundRet" ++
                                    [ .assign .storage
                                        (bidsF (.var "id") "guy") sender ])
                                  [] ] ++
                               checkedExternalCallStmts (.storage gemRef) "move"
                                (.intLit 0)
                                [sender, thisAddr,
                                  wrap256 (.binary .sub (.var "bid")
                                    (.storage (bidsF (.var "id") "bid")))] "_payRet" ++
                               [ .assign .storage (bidsF (.var "id") "bid")
                                  (.var "bid") ] ++
                               checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
                               [ .assign .storage (bidsF (.var "id") "tic")
                                  (.var "tic_") ])
                              (runtimeExit (.abi tendTransition.returnType)) := by
                          simpa [localsTail, bidOneTail, begBidTail, mem2399, id, bid] using
                            flapperTendExternalTailProgress
                              (cA := cA) (gh := gh) (bl := bl) (σworld := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (sel := flapperSelWord I) (mem2399 := mem2399)
                              (evm := evmSolm) (locals := localsTail)
                              hStateInit hperm hbaseGemTail hbaseBidsTail hbaseTtlTail
                              hgetIdTail hgetBidTail hmem2399 hread2399
                              (by simpa [mem2399, mem6, mem5, mem4, mem3, mem2, mem1, id]
                                using h2399)
                        have hprogress :
                            BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                              config
                              { contract := contract, locals := flapperTendLocals id lot bid }
                              evmSolm tendTransition.body
                              (runtimeExit (.abi tendTransition.returnType)) := by
                          have hp := BlockProgress.prepend hpref htail
                          simpa [tendTransition, nonpayable, checkedExternalCallStmts,
                            checkedMulUintInto, checkedAdd48Into,
                            flapperTendTimingGuardExpr, localsTail, bidOneTail, begBidTail,
                            flapperTendLocalsBegBid, evmSolm, id, lot, bid] using hp
                        exact hprogress.toRuntimeEquivalenceFor hcode
                          (fun result hfunc => by
                            exact solmExec.intro (flapperSelectorDispatch_tend hselLit)
                              rfl hdec
                              (by simp [evmSolm, initState, Sat256.ofUInt256,
                                Sat256.toUInt256])
                              hfunc)
                          (by intro result endpoint h; exact h)
                    · have hBidOneOverflow :
                          UInt256.size ≤
                            (flapperTendBidArgWord I).toNat *
                              flapperTendOneWord.toNat := by
                        exact Nat.le_of_not_gt hBidOneFit
                      have hbody :
                          ExecTransitionBody config contract evmSolm
                            (flapperTendLocals id lot bid) tendTransition.body
                            .reverted := by
                        have hBidOneOverflowSolm :
                            UInt256.size ≤ bid.toNat * flapperTendOneWord.toNat := by
                          simpa [bid] using hBidOneOverflow
                        simpa [evmSolm, id, lot, bid] using
                          flapperTendBodyRevertsBidOneOverflow evmSolm id lot bid
                            (by simp only [evmSolm, initState]; exact hwv)
                            hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                            hBidOneOverflowSolm
                      exact (flapperX_tend_bidOne_overflow_revert
                          (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                          hBegFit hBidOneOverflow h2270)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                  · have hBegOverflow :
                        UInt256.size ≤
                          (flapperTendBegWord σ_evm I).toNat *
                            (flapperTendBidWord σ_evm I).toNat := by
                      exact Nat.le_of_not_gt hBegFit
                    have hbody :
                        ExecTransitionBody config contract evmSolm
                          (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                      by_cases hBidOneFit :
                          bid.toNat * flapperTendOneWord.toNat < UInt256.size
                      · have hBegOverflowSolm :
                            UInt256.size ≤
                              (flapperTendBegWordOfState evmSolm).toNat *
                                (flapperTendBidWordOfState evmSolm id).toNat := by
                          simpa [hBegWordSolm, hBidWordSolm] using hBegOverflow
                        simpa [evmSolm, id, lot, bid] using
                          flapperTendBodyRevertsBegBidOverflow evmSolm id lot bid
                            (by simp only [evmSolm, initState]; exact hwv)
                            hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                            hBidOneFit hBegOverflowSolm
                      · have hBidOneOverflow :
                            UInt256.size ≤ bid.toNat * flapperTendOneWord.toNat := by
                          exact Nat.le_of_not_gt hBidOneFit
                        simpa [evmSolm, id, lot, bid] using
                          flapperTendBodyRevertsBidOneOverflow evmSolm id lot bid
                            (by simp only [evmSolm, initState]; exact hwv)
                            hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                            hBidOneOverflow
                    exact (flapperX_tend_begBid_overflow_revert
                        (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                        hBegOverflow h2270)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hbidSolm :
                      ¬ (flapperTendBidWordOfState evmSolm id).toNat < bid.toNat := by
                    intro hbad
                    exact hbidEvm (by simpa [hBidWordSolm, bid] using hbad)
                  have hbody :
                      ExecTransitionBody config contract evmSolm
                        (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                    simpa [evmSolm, id, lot, bid] using
                      flapperTendBodyRevertsBid evmSolm id lot bid
                        (by simp only [evmSolm, initState]; exact hwv)
                        hliveSolm hguySolm htiming hendSolm hlotSolm hbidSolm
                  exact (flapperX_tend_bid_revert
                      (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                      hbidEvm h2179)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hlotSolm : lot ≠ flapperTendLotWordOfState evmSolm id := by
                  intro hbad
                  exact hlotEvm (by simpa [lot, hLotWordSolm] using hbad)
                have hbody :
                    ExecTransitionBody config contract evmSolm
                      (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                  simpa [evmSolm, id, lot, bid] using
                    flapperTendBodyRevertsLot evmSolm id lot bid
                      (by simp only [evmSolm, initState]; exact hwv)
                      hliveSolm hguySolm htiming hendSolm hlotSolm
                exact (flapperX_tend_lot_revert
                    (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                    hlotEvm h2077)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hendSolm :
                  ¬ (flapperTendTimestampWordOfState evmSolm).toNat <
                    (flapperTendEndWordOfState evmSolm id).toNat := by
                intro hbad
                exact hendEvm (by simpa [hTimestampSolm, hEndWordSolm] using hbad)
              have hbody :
                  ExecTransitionBody config contract evmSolm
                    (flapperTendLocals id lot bid) tendTransition.body .reverted := by
                simpa [evmSolm, id, lot, bid] using
                  flapperTendBodyRevertsEnd evmSolm id lot bid
                    (by simp only [evmSolm, initState]; exact hwv)
                    hliveSolm hguySolm htiming hendSolm
              exact (flapperX_tend_end_revert
                  (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                  hendEvm h1960)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hticGtSolm :
                ¬ (flapperTendTimestampWordOfState evmSolm).toNat <
                  (flapperTendTicWordOfState evmSolm id).toNat := by
              intro hbad
              exact hticGtEvm (by simpa [hTimestampSolm, hTicWordSolm] using hbad)
            have hticNeSolm :
                flapperTendTicWordOfState evmSolm id ≠ UInt256.ofNat 0 := by
              intro hzero
              exact hticZeroEvm (by rw [← hTicWordSolm]; exact hzero)
            have hbody :
                ExecTransitionBody config contract evmSolm
                  (flapperTendLocals id lot bid) tendTransition.body .reverted := by
              simpa [evmSolm, id, lot, bid] using
                flapperTendBodyRevertsTiming evmSolm id lot bid
                  (by simp only [evmSolm, initState]; exact hwv)
                  hliveSolm hguySolm hticGtSolm hticNeSolm
            exact (flapperX_tend_timing_revert
                (g := Sat256.ofUInt256 g) (sel := flapperSelWord I)
                hticGtEvm hticZeroEvm h1802)
              |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hliveSolmNe :
          flapperTendLiveWordOfState evmSolm ≠ UInt256.ofNat 1 := by
        intro hLive
        exact hliveEvm (by rw [← hloadLiveEq]; exact hLive)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperTendLocals id lot bid)
            tendTransition.body .reverted := by
        simpa [evmSolm, id, lot, bid] using
          flapperTendBodyRevertsLive evmSolm id lot bid
            (by simp only [evmSolm, initState]; exact hwv) hliveSolmNe
      exact (flapperX_tend_live_revert
          (g := Sat256.ofUInt256 g) hliveEvm hdecode)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := flapperDecode_tend_none_short (I := I) hsz4 hshort
    have hrev := flapperX_tend_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
