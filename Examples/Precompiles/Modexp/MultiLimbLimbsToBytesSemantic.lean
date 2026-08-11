import Examples.Precompiles.Modexp.MultiLimbLimbsToBytes
import Examples.Precompiles.Modexp.MultiLimbClzArithmetic
import Examples.Precompiles.Modexp.MultiLimbMemoryModel
import Examples.Precompiles.Modexp.MultiLimbSubtractionModel
import Examples.Precompiles.Modexp.MultiLimbMultiplicationOuterModel
import Examples.Precompiles.Modexp.Bridge

/-!
# `limbsToBytes` semantics

This module interprets the deployed serializer's full-word writes and partial masked merge as the
trusted fixed-width big-endian encoding of the little-endian accumulator value.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbLimbsToBytesSemantic

open Modexp
open Modexp.MultiLimbLimbsToBytes
open Modexp.MultiLimbClz

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Clearing the low `k` bits of a 256-bit natural floors it to a multiple of `2^k`. -/
private theorem nat_land_mask_pow (m k : Nat) (hm : m < 2 ^ 256) (hk : k ≤ 256) :
    m &&& (2 ^ 256 - 2 ^ k) = 2 ^ k * (m / 2 ^ k) := by
  have hmask : (2 : Nat) ^ 256 - 2 ^ k = (2 ^ (256 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
    simp only [one_mul]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hmask, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    show 2 ^ k * (m / 2 ^ k) = (m >>> k) * 2 ^ k by
      rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm],
    Nat.testBit_mul_two_pow, Nat.testBit_shiftRight]
  by_cases hi : k ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hi256 : i - k < 256 - k
    · simp only [hi256, decide_true, Bool.and_true]
      rw [show k + (i - k) = i by omega]
    · simp only [hi256, decide_false, Bool.and_false]
      have hiBound : 256 ≤ i := by omega
      have hb : m.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
        (Nat.pow_le_pow_right (by norm_num) hiBound))
      rw [show k + (i - k) = i by omega, hb]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

private theorem lnot_toNat (x : UInt256) :
    (UInt256.lnot x).toNat = UInt256.size - 1 - x.toNat := by
  unfold UInt256.lnot
  change (UInt256.sub (UInt256.ofNat (UInt256.size - 1)) x).toNat = _
  have htop : UInt256.size - 1 < UInt256.size := by unfold UInt256.size; omega
  rw [usub_toNat]
  · rw [ulit_toNat' _ htop]
  · rw [ulit_toNat' _ htop]
    exact Nat.le_pred_of_lt x.val.isLt

theorem partialShift_toNat
    {dataLen : UInt256} {rem : Nat} (hrem : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem) :
    (partialShift dataLen).toNat = 8 * (32 - rem) := by
  unfold partialShift
  rw [hland]
  have hrNat : (UInt256.ofNat rem).toNat = rem :=
    UInt256.toNat_ofNat_of_lt (lt_trans hrem (by decide))
  simpa only [hrNat] using
    (paddingShift_toNat (size := UInt256.ofNat rem) (by simpa only [hrNat] using hrem.le))

theorem partialLowMask_toNat
    {dataLen : UInt256} {rem : Nat} (hremPos : 0 < rem) (hrem : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem) :
    (partialLowMask dataLen).toNat = 2 ^ (8 * (32 - rem)) - 1 := by
  let s := 8 * (32 - rem)
  have hsPos : 0 < s := by dsimp [s]; omega
  have hs : s < 256 := by dsimp [s]; omega
  have hsWord : s < UInt256.size := lt_trans hs (by decide)
  have hshiftWord : UInt256.ofNat s = partialShift dataLen := by
    apply u256_inj
    rw [UInt256.toNat_ofNat_of_lt hsWord, partialShift_toNat hrem hland]
  have hone : ((⟨1⟩ : UInt256).shiftLeft (UInt256.ofNat s)).toNat = 2 ^ s := by
    have h := shiftLeft_toNat_exact (x := (⟨1⟩ : UInt256)) (shift := s) hs (by
      change 1 < 2 ^ (256 - s)
      exact Nat.one_lt_pow (by omega : 256 - s ≠ 0) (by decide))
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide] at h
    simpa using h
  unfold partialLowMask
  rw [← hshiftWord, uadd_toNat, hone,
    show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 by native_decide]
  rw [show 2 ^ s + (UInt256.size - 1) = UInt256.size + (2 ^ s - 1) by
    have hpow : 0 < 2 ^ s := by positivity
    omega]
  rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  apply Nat.mod_eq_of_lt
  rw [show UInt256.size = 2 ^ 256 by decide]
  have hpowLt : 2 ^ s < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hs
  omega

/-- The `j`th source load addresses the `j`th little-endian payload limb when the source array
fits in the 256-bit address space. -/
theorem sourceAddress_toNat
    {fp j : Nat} (hfit : fp + 32 + 32 * j < UInt256.size) :
    (sourceAddress (UInt256.ofNat j) (UInt256.ofNat fp)).toNat = fp + 32 + 32 * j := by
  unfold sourceAddress
  have hj : j < UInt256.size := by omega
  have hfp : fp < UInt256.size := by omega
  have hjShift : j < 2 ^ (256 - 5) := by
    rw [show 256 - 5 = 251 by omega]
    by_contra hn
    have hjLarge : 2 ^ 251 ≤ j := Nat.le_of_not_gt hn
    have hp : 32 * 2 ^ 251 = 2 ^ 256 := by
      norm_num [show 32 = 2 ^ 5 by norm_num, ← Nat.pow_add]
    have : UInt256.size ≤ 32 * j := by
      rw [show UInt256.size = 2 ^ 256 by decide, ← hp]
      exact Nat.mul_le_mul_left 32 hjLarge
    omega
  have hshift : (UInt256.shiftLeft (UInt256.ofNat j) ⟨5⟩).toNat = 32 * j := by
    change (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5)).toNat = 32 * j
    rw [shiftLeft_toNat_exact (shift := 5) (by decide) (by
      rw [UInt256.toNat_ofNat_of_lt hj]
      exact hjShift), UInt256.toNat_ofNat_of_lt hj]
    omega
  have hfirst : 32 * j + fp < UInt256.size := by
    rw [Nat.add_comm]
    omega
  rw [uadd_toNat, uadd_toNat, hshift, UInt256.toNat_ofNat_of_lt hfp,
    show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The `j`th full output store is the `j`th 32-byte window counted backwards from the end of the
requested result. -/
theorem outputAddress_toNat
    {out : UInt256} {dataLen j : Nat}
    (hlen : dataLen ≤ 1024) (hj : j < dataLen / 32)
    (hfit : out.toNat + 32 + dataLen < UInt256.size) :
    (outputAddress (UInt256.ofNat j) (UInt256.ofNat dataLen) out).toNat =
      out.toNat + 32 + dataLen - 32 * (j + 1) := by
  unfold outputAddress outputOffset
  have hjWord : j < UInt256.size := by omega
  have hj1Word : j + 1 < UInt256.size := by omega
  have hlenWord : dataLen < UInt256.size := by omega
  have hmul : 32 * (j + 1) ≤ dataLen := by
    calc
      32 * (j + 1) ≤ 32 * (dataLen / 32) := Nat.mul_le_mul_left 32 (by omega)
      _ = (dataLen / 32) * 32 := by omega
      _ ≤ dataLen := Nat.div_mul_le_self dataLen 32
  have hadd : (UInt256.ofNat j + ⟨1⟩).toNat = j + 1 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hjWord,
      show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt hj1Word]
  have hshift : ((UInt256.ofNat j + ⟨1⟩).shiftLeft ⟨5⟩).toNat =
      32 * (j + 1) := by
    change (UInt256.shiftLeft (UInt256.ofNat j + ⟨1⟩) (UInt256.ofNat 5)).toNat =
      32 * (j + 1)
    rw [shiftLeft_toNat_exact (shift := 5) (by decide) (by rw [hadd]; omega), hadd]
    omega
  have hsub : ((UInt256.ofNat dataLen).sub
      ((UInt256.ofNat j + ⟨1⟩).shiftLeft ⟨5⟩)).toNat =
      dataLen - 32 * (j + 1) := by
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hlenWord, hshift]
    · rw [UInt256.toNat_ofNat_of_lt hlenWord, hshift]
      exact hmul
  have hfirst : out.toNat + (dataLen - 32 * (j + 1)) < UInt256.size := by omega
  have hsecond : out.toNat + (dataLen - 32 * (j + 1)) + 32 < UInt256.size := by omega
  rw [uadd_toNat, uadd_toNat, hsub,
    show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hsecond]
  omega

/-- A concrete full-limb store reads back as the source limb. -/
theorem fullMemory_word
    (mem : ByteArray) (word : UInt256) (dest : Nat)
    (haddr64 : dest < 2 ^ 64) (hgap : dest - mem.size < USize.size) :
    Model.bytesToNatPadded (word.toByteArray.write 0 mem dest 32) dest 32 = word.toNat := by
  rw [← MultiLimbMemoryModel.memoryWordNat_eq_model
    (word.toByteArray.write 0 mem dest 32) dest haddr64]
  unfold MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- Source words observed by the concrete full-limb iteration sequence. -/
def fullSourceWords (aw limbs dataLen out : UInt256) : Nat → FullState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      sourceValue state.memory aw state.index limbs ::
        fullSourceWords aw limbs dataLen out n (advance aw limbs dataLen out state)

@[simp] theorem fullSourceWords_length
    (aw limbs dataLen out : UInt256) (count : Nat) (state : FullState) :
    (fullSourceWords aw limbs dataLen out count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp only [fullSourceWords, List.length_cons, ih]

/-- A sequence of in-bounds output writes below a read window preserves that window. -/
theorem iterate_read_above
    (aw limbs dataLen out : UInt256) (count : Nat) (state : FullState) (read : Nat)
    (hin : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size)
    (hbelow : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat + 32 ≤ read) :
    (iterate aw limbs dataLen out count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance aw limbs dataLen out state
      let dest := (outputAddress state.index dataLen out).toNat
      have hfirstIn : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hin 0 (by omega)
      have hfirstBelow : dest + 32 ≤ read := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hfirst : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, advance, dest]
        exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
          hfirstIn hfirstBelow
      have hin' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hin (q + 1) (by omega)
      have hbelow' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ read := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have hrest := ih next hin' hbelow'
      simpa only [next, iterate] using hrest.trans hfirst

/-- A sequence of in-bounds output writes above a read window preserves that window. -/
theorem iterate_read_below
    (aw limbs dataLen out : UInt256) (count : Nat) (state : FullState) (read : Nat)
    (hin : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size)
    (habove : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      read + 32 ≤ (outputAddress current.index dataLen out).toNat) :
    (iterate aw limbs dataLen out count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance aw limbs dataLen out state
      let dest := (outputAddress state.index dataLen out).toNat
      have hfirstIn : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hin 0 (by omega)
      have hfirstAbove : read + 32 ≤ dest := by
        simpa only [dest, iterate] using habove 0 (by omega)
      have hfirst : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, advance, dest]
        exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
          (by omega) hfirstAbove
      have hin' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hin (q + 1) (by omega)
      have habove' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          read + 32 ≤ (outputAddress current.index dataLen out).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using habove (q + 1) (by omega)
      have hrest := ih next hin' habove'
      simpa only [next, iterate] using hrest.trans hfirst

/-- The partial branch's exact Solidity merge has the source limb in its leading `rem` bytes.
The lower mask can contain arbitrary preexisting output data. -/
theorem partialMerged_shiftRight
    {source existing dataLen : UInt256} {rem : Nat}
    (hremPos : 0 < rem) (hremLt : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem)
    (hfit : source.toNat < 2 ^ (8 * rem)) :
    (partialMergedValue source existing dataLen).shiftRight (partialShift dataLen) = source := by
  let s := 8 * (32 - rem)
  have hsPos : 0 < s := by dsimp [s]; omega
  have hs : s < 256 := by dsimp [s]; omega
  have hsum : 8 * rem + s = 256 := by dsimp [s]; omega
  have hshiftNat : (partialShift dataLen).toNat = s := partialShift_toNat hremLt hland
  have hlowMask : (partialLowMask dataLen).toNat = 2 ^ s - 1 := by
    simpa only [s] using partialLowMask_toNat hremPos hremLt hland
  have hhighMask : (partialLowMask dataLen).lnot.toNat = 2 ^ 256 - 2 ^ s := by
    rw [lnot_toNat, hlowMask]
    rw [show UInt256.size = 2 ^ 256 by decide]
    have hpow : 2 ^ s ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpowPos : 0 < 2 ^ s := by positivity
    omega
  have hsourceBound : source.toNat < 2 ^ (256 - s) := by
    rw [show 256 - s = 8 * rem by omega]
    exact hfit
  have hsourceShift :
      (source.shiftLeft (partialShift dataLen)).toNat = source.toNat * 2 ^ s := by
    have h := shiftLeft_toNat_exact (x := source) (shift := s) hs hsourceBound
    have hword : UInt256.ofNat s = partialShift dataLen := by
      apply u256_inj
      rw [UInt256.toNat_ofNat_of_lt (lt_trans hs (by decide)), hshiftNat]
    simpa only [hword] using h
  have hsourceShiftBound : source.toNat * 2 ^ s < 2 ^ 256 := by
    calc
      source.toNat * 2 ^ s < 2 ^ (256 - s) * 2 ^ s :=
        Nat.mul_lt_mul_of_pos_right hsourceBound (by positivity)
      _ = 2 ^ 256 := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hhigh :
      ((source.shiftLeft (partialShift dataLen)).land
        (partialLowMask dataLen).lnot).toNat = source.toNat * 2 ^ s := by
    rw [uland_toNat, hsourceShift, hhighMask,
      nat_land_mask_pow _ _ hsourceShiftBound (by omega)]
    rw [Nat.mul_div_left _ (by positivity), Nat.mul_comm]
  have hlow :
      (existing.land (partialLowMask dataLen)).toNat = existing.toNat % 2 ^ s := by
    rw [uland_toNat, hlowMask]
    exact nat_land_mask_eq_mod existing.toNat s
  have hlowBound : existing.toNat % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  have hor :
      Nat.lor (source.toNat * 2 ^ s) (existing.toNat % 2 ^ s) =
        existing.toNat % 2 ^ s + source.toNat * 2 ^ s := by
    calc
      Nat.lor (source.toNat * 2 ^ s) (existing.toNat % 2 ^ s) =
          Nat.lor (existing.toNat % 2 ^ s) (source.toNat * 2 ^ s) := Nat.lor_comm _ _
      _ = existing.toNat % 2 ^ s + source.toNat * 2 ^ s :=
        nat_lor_shift_add _ _ _ hlowBound
  have hmerged : (partialMergedValue source existing dataLen).toNat =
      existing.toNat % 2 ^ s + source.toNat * 2 ^ s := by
    unfold partialMergedValue
    rw [u256_lor_toNat, hhigh, hlow, hor]
    apply Nat.mod_eq_of_lt
    calc
      existing.toNat % 2 ^ s + source.toNat * 2 ^ s <
          2 ^ s + source.toNat * 2 ^ s := Nat.add_lt_add_right hlowBound _
      _ = (source.toNat + 1) * 2 ^ s := by ring
      _ ≤ 2 ^ (256 - s) * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
      _ = UInt256.size := by
        rw [show UInt256.size = 2 ^ 256 by decide, ← Nat.pow_add,
          Nat.sub_add_cancel (by omega)]
  apply u256_inj
  rw [shiftRight_toNat_of_lt256 _ _ (by simpa [hshiftNat] using hs), hshiftNat, hmerged]
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlowBound]
  simp

/-- The partial merge preserves the low `32 - rem` bytes of the preexisting output word. -/
theorem partialMerged_mod
    {source existing dataLen : UInt256} {rem : Nat}
    (hremPos : 0 < rem) (hremLt : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem)
    (hfit : source.toNat < 2 ^ (8 * rem)) :
    (partialMergedValue source existing dataLen).toNat % 2 ^ (8 * (32 - rem)) =
      existing.toNat % 2 ^ (8 * (32 - rem)) := by
  let s := 8 * (32 - rem)
  have hsPos : 0 < s := by dsimp [s]; omega
  have hs : s < 256 := by dsimp [s]; omega
  have hshiftNat : (partialShift dataLen).toNat = s := partialShift_toNat hremLt hland
  have hlowMask : (partialLowMask dataLen).toNat = 2 ^ s - 1 := by
    simpa only [s] using partialLowMask_toNat hremPos hremLt hland
  have hhighMask : (partialLowMask dataLen).lnot.toNat = 2 ^ 256 - 2 ^ s := by
    rw [lnot_toNat, hlowMask]
    rw [show UInt256.size = 2 ^ 256 by decide]
    have hpow : 2 ^ s ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpowPos : 0 < 2 ^ s := by positivity
    omega
  have hsourceBound : source.toNat < 2 ^ (256 - s) := by
    rw [show 256 - s = 8 * rem by dsimp [s]; omega]
    exact hfit
  have hsourceShift :
      (source.shiftLeft (partialShift dataLen)).toNat = source.toNat * 2 ^ s := by
    have h := shiftLeft_toNat_exact (x := source) (shift := s) hs hsourceBound
    have hword : UInt256.ofNat s = partialShift dataLen := by
      apply u256_inj
      rw [UInt256.toNat_ofNat_of_lt (lt_trans hs (by decide)), hshiftNat]
    simpa only [hword] using h
  have hsourceShiftBound : source.toNat * 2 ^ s < 2 ^ 256 := by
    calc
      source.toNat * 2 ^ s < 2 ^ (256 - s) * 2 ^ s :=
        Nat.mul_lt_mul_of_pos_right hsourceBound (by positivity)
      _ = 2 ^ 256 := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hhigh :
      ((source.shiftLeft (partialShift dataLen)).land
        (partialLowMask dataLen).lnot).toNat = source.toNat * 2 ^ s := by
    rw [uland_toNat, hsourceShift, hhighMask,
      nat_land_mask_pow _ _ hsourceShiftBound (by omega)]
    rw [Nat.mul_div_left _ (by positivity), Nat.mul_comm]
  have hlow :
      (existing.land (partialLowMask dataLen)).toNat = existing.toNat % 2 ^ s := by
    rw [uland_toNat, hlowMask]
    exact nat_land_mask_eq_mod existing.toNat s
  have hlowBound : existing.toNat % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  have hor : Nat.lor (source.toNat * 2 ^ s) (existing.toNat % 2 ^ s) =
      existing.toNat % 2 ^ s + source.toNat * 2 ^ s := by
    calc
      Nat.lor (source.toNat * 2 ^ s) (existing.toNat % 2 ^ s) =
          Nat.lor (existing.toNat % 2 ^ s) (source.toNat * 2 ^ s) := Nat.lor_comm _ _
      _ = existing.toNat % 2 ^ s + source.toNat * 2 ^ s :=
        nat_lor_shift_add _ _ _ hlowBound
  have hmerged : (partialMergedValue source existing dataLen).toNat =
      existing.toNat % 2 ^ s + source.toNat * 2 ^ s := by
    unfold partialMergedValue
    rw [u256_lor_toNat, hhigh, hlow, hor]
    apply Nat.mod_eq_of_lt
    calc
      existing.toNat % 2 ^ s + source.toNat * 2 ^ s <
          2 ^ s + source.toNat * 2 ^ s := Nat.add_lt_add_right hlowBound _
      _ = (source.toNat + 1) * 2 ^ s := by ring
      _ ≤ 2 ^ (256 - s) * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
      _ = UInt256.size := by
        rw [show UInt256.size = 2 ^ 256 by decide, ← Nat.pow_add,
          Nat.sub_add_cancel (by omega)]
  change (partialMergedValue source existing dataLen).toNat % 2 ^ s =
    existing.toNat % 2 ^ s
  rw [hmerged, Nat.add_mod, Nat.mul_mod_left, Nat.mod_mod, Nat.add_zero, Nat.mod_mod]

/-- The concrete partial store reads back as the exact merged 256-bit word. -/
theorem partialMemory_fullWord
    (mem : ByteArray) (source existing dataLen out : UInt256)
    (haddr64 : (partialOutputAddress out).toNat < 2 ^ 64)
    (hgap : (partialOutputAddress out).toNat - mem.size < USize.size) :
    Model.bytesToNatPadded (partialMemory mem source existing dataLen out)
      (partialOutputAddress out).toNat 32 =
        (partialMergedValue source existing dataLen).toNat := by
  rw [← MultiLimbMemoryModel.memoryWordNat_eq_model
    (partialMemory mem source existing dataLen out)
    (partialOutputAddress out).toNat haddr64]
  unfold MultiLimbMemoryModel.memoryWordNat partialMemory
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- Reading the leading `rem` bytes written by the partial branch yields the fitted source limb.
This theorem observes the concrete `ByteArray.write`, not just the mask expression. -/
theorem partialMemory_prefixValue
    {mem : ByteArray} {source existing dataLen out : UInt256} {rem : Nat}
    (hremPos : 0 < rem) (hremLt : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem)
    (hfit : source.toNat < 2 ^ (8 * rem))
    (haddr64 : (partialOutputAddress out).toNat < 2 ^ 64)
    (hgap : (partialOutputAddress out).toNat - mem.size < USize.size) :
    Model.bytesToNatPadded (partialMemory mem source existing dataLen out)
      (partialOutputAddress out).toNat rem = source.toNat := by
  let merged := partialMergedValue source existing dataLen
  let final := partialMemory mem source existing dataLen out
  have hfull : Model.bytesToNatPadded final (partialOutputAddress out).toNat 32 =
      merged.toNat := by
    exact partialMemory_fullWord mem source existing dataLen out haddr64 hgap
  let prefixValue := Model.bytesToNatPadded final (partialOutputAddress out).toNat rem
  let suffixValue := Model.bytesToNatPadded final
    ((partialOutputAddress out).toNat + rem) (32 - rem)
  let radixValue := 256 ^ (32 - rem)
  have hsplit := model_bytesToNatPadded_split final
    (partialOutputAddress out).toNat rem (32 - rem)
  have hwidth : rem + (32 - rem) = 32 := by omega
  have hdecompose : merged.toNat = prefixValue * radixValue + suffixValue := by
    rw [← hfull]
    simpa only [hwidth, prefixValue, suffixValue, radixValue] using hsplit
  have hsuffix : suffixValue < radixValue := by
    exact model_bytesToNatPadded_lt_pow final
      ((partialOutputAddress out).toNat + rem) (32 - rem)
  have hquotient : merged.toNat / radixValue = prefixValue := by
    rw [hdecompose, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hsuffix, zero_add]
  have hshifted := congrArg UInt256.toNat
    (partialMerged_shiftRight (existing := existing) hremPos hremLt hland hfit)
  change (merged.shiftRight (partialShift dataLen)).toNat = source.toNat at hshifted
  have hshiftNat : (partialShift dataLen).toNat = 8 * (32 - rem) :=
    partialShift_toNat hremLt hland
  rw [shiftRight_toNat_of_lt256 _ _ (by rw [hshiftNat]; omega), hshiftNat] at hshifted
  have hradix : radixValue = 2 ^ (8 * (32 - rem)) := by
    dsimp only [radixValue]
    rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  rw [hradix] at hquotient
  rw [hshifted] at hquotient
  exact hquotient.symm

/-- The numeric value of a suffix of a big-endian window is the full value modulo that suffix's
radix. -/
theorem bytesToNatPadded_suffix_mod (mem : ByteArray) (dest pre suffix : Nat) :
    Model.bytesToNatPadded mem (dest + pre) suffix =
      Model.bytesToNatPadded mem dest (pre + suffix) % 256 ^ suffix := by
  have hsplit := model_bytesToNatPadded_split mem dest pre suffix
  have hbound := model_bytesToNatPadded_lt_pow mem (dest + pre) suffix
  rw [hsplit, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hbound,
    Nat.zero_add, Nat.mod_eq_of_lt hbound]

/-- The masked partial store preserves the complete already-serialized suffix beginning after its
new `rem`-byte prefix, including the first window that overlaps the 32-byte store. -/
theorem partialMemory_suffixValue
    {mem : ByteArray} {source existing dataLen out : UInt256} {rem suffixLen : Nat}
    (hremPos : 0 < rem) (hremLt : rem < 32)
    (hland : dataLen.land ⟨31⟩ = UInt256.ofNat rem)
    (hfit : source.toNat < 2 ^ (8 * rem))
    (hexisting : Model.bytesToNatPadded mem (partialOutputAddress out).toNat 32 =
      existing.toNat)
    (hin : (partialOutputAddress out).toNat + 32 ≤ mem.size)
    (haddr64 : (partialOutputAddress out).toNat + rem + suffixLen < 2 ^ 64)
    (hsuffix : 32 - rem ≤ suffixLen) :
    Model.bytesToNatPadded (partialMemory mem source existing dataLen out)
        ((partialOutputAddress out).toNat + rem) suffixLen =
      Model.bytesToNatPadded mem ((partialOutputAddress out).toNat + rem) suffixLen := by
  let dest := (partialOutputAddress out).toNat
  let width := 32 - rem
  let tail := suffixLen - width
  let final := partialMemory mem source existing dataLen out
  have hsum : width + tail = suffixLen := by dsimp [width, tail]; omega
  have hstart : dest + rem + width = dest + 32 := by dsimp [width]; omega
  have hdest64 : dest < 2 ^ 64 := by dsimp [dest] at *; omega
  have hgap : dest - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by dsimp [dest] at *; omega)]
    exact lt_usize 0 (by norm_num)
  have hfull : Model.bytesToNatPadded final dest 32 =
      (partialMergedValue source existing dataLen).toNat := by
    exact partialMemory_fullWord mem source existing dataLen out hdest64 hgap
  have hprefixFinal : Model.bytesToNatPadded final (dest + rem) width =
      (partialMergedValue source existing dataLen).toNat % 256 ^ width := by
    rw [bytesToNatPadded_suffix_mod]
    simpa only [show rem + width = 32 by dsimp [width]; omega] using
      congrArg (fun x => x % 256 ^ width) hfull
  have hprefixOld : Model.bytesToNatPadded mem (dest + rem) width =
      existing.toNat % 256 ^ width := by
    rw [bytesToNatPadded_suffix_mod]
    have h := congrArg (fun x => x % 256 ^ width) hexisting
    simpa only [dest, show rem + width = 32 by dsimp [width]; omega] using h
  have hradix : 256 ^ width = 2 ^ (8 * (32 - rem)) := by
    dsimp only [width]
    rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  have hprefix : Model.bytesToNatPadded final (dest + rem) width =
      Model.bytesToNatPadded mem (dest + rem) width := by
    rw [hprefixFinal, hprefixOld, hradix]
    exact partialMerged_mod hremPos hremLt hland hfit
  have htail : Model.bytesToNatPadded final (dest + 32) tail =
      Model.bytesToNatPadded mem (dest + 32) tail := by
    by_cases hz : tail = 0
    · rw [hz, model_bytesToNatPadded_zero_width, model_bytesToNatPadded_zero_width]
    · apply model_bytesToNatPadded_eq_of_readWithPadding
          (by dsimp [dest, tail, width] at *; omega)
          (by dsimp [dest, tail, width] at *; omega)
          (by dsimp [tail, width] at *; omega)
      dsimp only [final, partialMemory]
      exact write32_read_above_len_padded _ _ dest (dest + 32) tail
        (by rw [toByteArray_size]) (by simpa only [dest] using hin) (by omega)
        (Nat.pos_of_ne_zero hz) (by dsimp [tail, width] at *; omega)
  have hsplitFinal := model_bytesToNatPadded_split final (dest + rem) width tail
  have hsplitOld := model_bytesToNatPadded_split mem (dest + rem) width tail
  rw [hsum] at hsplitFinal hsplitOld
  rw [hstart] at hsplitFinal hsplitOld
  rw [hsplitFinal, hsplitOld, hprefix, htail]

/-- Recursive output representation: low limbs occupy later 32-byte windows and the final short
top limb, if any, occupies the leading bytes. -/
def Encodes (mem : ByteArray) (start : Nat) : (len : Nat) → List UInt256 → Prop
  | 0, words => words = []
  | _ + 1, [] => False
  | len + 1, word :: words =>
      if len + 1 ≤ 32 then
        words = [] ∧ Model.bytesToNatPadded mem start (len + 1) = word.toNat
      else
        Model.bytesToNatPadded mem (start + (len + 1 - 32)) 32 = word.toNat ∧
          Encodes mem start (len + 1 - 32) words
termination_by len _ => len
decreasing_by omega

/-- The actual descending full-limb writes encode exactly the words loaded by those iterations.
The hypotheses state only the concrete destination layout and that each write is in bounds. -/
theorem iterate_encodes_full
    (aw limbs dataLen out : UInt256) (count start : Nat) (state : FullState)
    (haddr64 : start + 32 * count < 2 ^ 64)
    (hdest : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat = start + 32 * (count - q - 1))
    (hin : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size) :
    Encodes (iterate aw limbs dataLen out count state).memory start (32 * count)
      (fullSourceWords aw limbs dataLen out count state) := by
  induction count generalizing state with
  | zero => simp [fullSourceWords, Encodes]
  | succ count ih =>
      let next := advance aw limbs dataLen out state
      let word := sourceValue state.memory aw state.index limbs
      let dest := (outputAddress state.index dataLen out).toNat
      have hdest0 : dest = start + 32 * count := by
        simpa only [dest, iterate] using hdest 0 (by omega)
      have hfirstIn : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hin 0 (by omega)
      have hdest' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat =
            start + 32 * (count - q - 1) := by
        intro q hq
        have hraw := hdest (q + 1) (by omega)
        dsimp only
        rw [show iterate aw limbs dataLen out q next =
          iterate aw limbs dataLen out (q + 1) state by
            simpa only [next] using iterate_advance aw limbs dataLen out q state]
        rw [hraw]
        congr 1
        omega
      have hin' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hin (q + 1) (by omega)
      have htail := ih next (by omega) hdest' hin'
      have hbelow : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ dest := by
        intro q hq
        dsimp only
        rw [hdest' q hq, hdest0]
        omega
      have hframe := iterate_read_above aw limbs dataLen out count next dest hin' hbelow
      have hstored : Model.bytesToNatPadded next.memory dest 32 = word.toNat := by
        dsimp only [next, advance, word]
        exact fullMemory_word state.memory (sourceValue state.memory aw state.index limbs) dest
          (by rw [hdest0]; omega) (by
            rw [Nat.sub_eq_zero_of_le (by omega)]
            exact lt_usize 0 (by norm_num))
      have hfinal : Model.bytesToNatPadded
          (iterate aw limbs dataLen out count next).memory dest 32 = word.toNat := by
        rw [model_bytesToNatPadded_eq_of_readWithPadding (a :=
          (iterate aw limbs dataLen out count next).memory) (b := next.memory)
          (offA := dest) (offB := dest) (width := 32) (by omega) (by omega) (by decide) hframe]
        exact hstored
      rw [show iterate aw limbs dataLen out (count + 1) state =
        iterate aw limbs dataLen out count next by rfl]
      change Encodes (iterate aw limbs dataLen out count next).memory start (32 * (count + 1))
        (word :: fullSourceWords aw limbs dataLen out count next)
      rw [show 32 * (count + 1) = (32 * (count + 1) - 1) + 1 by omega]
      simp only [Encodes]
      by_cases hzero : count = 0
      · subst count
        simp only [fullSourceWords, true_and]
        simpa only [next, word, hdest0] using hfinal
      · rw [if_neg (by omega : ¬ 32 * (count + 1) - 1 + 1 ≤ 32)]
        constructor
        · simpa only [next, hdest0] using hfinal
        · simpa only using htail

/-- The recursive byte-window representation has exactly the pure little-endian limb value. -/
theorem Encodes.value
    {mem : ByteArray} {start len : Nat} {words : List UInt256}
    (encoded : Encodes mem start len words) :
    Model.bytesToNatPadded mem start len = Modexp.wordLimbsToNat words := by
  induction len using Nat.strong_induction_on generalizing words with
  | h len ih =>
      cases len with
      | zero =>
          simp only [Encodes] at encoded
          subst words
          simp [Modexp.wordLimbsToNat, model_bytesToNatPadded_zero_width]
      | succ len =>
          cases words with
          | nil => simp [Encodes] at encoded
          | cons word words =>
              simp only [Encodes] at encoded
              by_cases hsmall : len + 1 ≤ 32
              · simp only [hsmall, if_true] at encoded
                rcases encoded with ⟨rfl, hvalue⟩
                simpa [Modexp.wordLimbsToNat] using hvalue
              · simp only [hsmall, if_false] at encoded
                rcases encoded with ⟨hlow, hrest⟩
                have hlarge : 32 < len + 1 := by omega
                have hprefix := ih (len + 1 - 32) (by omega) hrest
                have hsplit := model_bytesToNatPadded_split mem start (len + 1 - 32) 32
                rw [show len + 1 - 32 + 32 = len + 1 by omega] at hsplit
                rw [hsplit, hprefix, hlow]
                simp only [Modexp.wordLimbsToNat]
                rw [show UInt256.size = 256 ^ 32 by native_decide]
                omega

/-- Complete source-word sequence loaded by the deployed serializer. The optional final element is
the fitted most-significant partial limb. -/
def serializedSourceWords
    (mem : ByteArray) (aw limbs out : UInt256) (dataLen : Nat) : List UInt256 :=
  let state := limbsToBytesFullState mem aw limbs out dataLen
  fullSourceWords aw limbs (UInt256.ofNat dataLen) out (dataLen / 32) (initialState mem) ++
    if dataLen % 32 = 0 then []
    else [partialSourceValue state.memory aw limbs (UInt256.ofNat dataLen)]

/-- The complete concrete serializer output equals the little-endian value of exactly the source
words loaded by its full and partial branches. This theorem accounts for the masked overlap in the
partial branch and does not assume an abstract encoding relation. -/
theorem limbsToBytesMemory_value
    {mem : ByteArray} {aw limbs out : UInt256} {dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr64 : out.toNat + 32 + dataLen < 2 ^ 64)
    (hfullIn : ∀ q, q < dataLen / 32 →
      let current := iterate aw limbs (UInt256.ofNat dataLen) out q (initialState mem)
      (outputAddress current.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        current.memory.size)
    (hpartialIn : dataLen % 32 ≠ 0 → (partialOutputAddress out).toNat + 32 ≤
      (limbsToBytesFullState mem aw limbs out dataLen).memory.size)
    (hexisting : dataLen % 32 ≠ 0 → Model.bytesToNatPadded
        (limbsToBytesFullState mem aw limbs out dataLen).memory
        (partialOutputAddress out).toNat 32 =
      (partialExistingValue (limbsToBytesFullState mem aw limbs out dataLen).memory
        aw limbs (UInt256.ofNat dataLen) out).toNat)
    (hpartialFit : dataLen % 32 ≠ 0 → (partialSourceValue
        (limbsToBytesFullState mem aw limbs out dataLen).memory aw limbs
        (UInt256.ofNat dataLen)).toNat < 2 ^ (8 * (dataLen % 32))) :
    Model.bytesToNatPadded (limbsToBytesMemory mem aw limbs out dataLen)
        (out.toNat + 32) dataLen =
      Modexp.wordLimbsToNat (serializedSourceWords mem aw limbs out dataLen) := by
  let count := dataLen / 32
  let rem := dataLen % 32
  let state := limbsToBytesFullState mem aw limbs out dataLen
  let source := partialSourceValue state.memory aw limbs (UInt256.ofNat dataLen)
  let existing := partialExistingValue state.memory aw limbs (UInt256.ofNat dataLen) out
  let words := fullSourceWords aw limbs (UInt256.ofNat dataLen) out count (initialState mem)
  have hdecomp := Nat.mod_add_div dataLen 32
  have houtNat : (partialOutputAddress out).toNat = out.toNat + 32 := by
    unfold partialOutputAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by
        have : out.toNat + 32 < 2 ^ 64 := by omega
        exact this.trans (by decide))]
  have hwordRem := MultiLimbGenerated.wordRemainder_eq hlen
  have hdest : ∀ q, q < count →
      let current := iterate aw limbs (UInt256.ofNat dataLen) out q (initialState mem)
      (outputAddress current.index (UInt256.ofNat dataLen) out).toNat =
        out.toNat + 32 + rem + 32 * (count - q - 1) := by
    intro q hq
    dsimp only
    rw [initial_index]
    rw [outputAddress_toNat hlen (by simpa only [count] using hq) (by
      apply lt_trans haddr64
      decide)]
    dsimp only [count, rem]
    omega
  have hencoded : Encodes state.memory (out.toNat + 32 + rem) (32 * count) words := by
    exact iterate_encodes_full aw limbs (UInt256.ofNat dataLen) out count
      (out.toNat + 32 + rem) (initialState mem) (by
        dsimp only [count, rem]
        omega) hdest (by simpa only [count] using hfullIn)
  have hfullValue : Model.bytesToNatPadded state.memory
      (out.toNat + 32 + rem) (32 * count) = Modexp.wordLimbsToNat words :=
    Encodes.value hencoded
  by_cases hrem : rem = 0
  · have hlenEq : dataLen = 32 * count := by dsimp [rem, count] at *; omega
    have hremRaw : dataLen % 32 = 0 := by simpa only [rem] using hrem
    have hmemory : limbsToBytesMemory mem aw limbs out dataLen = state.memory := by
      simp [limbsToBytesMemory, state, limbsToBytesFullState,
        limbsToBytesSuffixMemory, rem, hrem]
    have hfullValue' : Model.bytesToNatPadded state.memory
        (out.toNat + 32) dataLen = Modexp.wordLimbsToNat words := by
      simpa only [hrem, Nat.add_zero, hlenEq] using hfullValue
    rw [hmemory]
    unfold serializedSourceWords
    dsimp only
    rw [if_pos hremRaw, List.append_nil]
    simpa only [state, words, count] using hfullValue'
  · have hremPos : 0 < rem := Nat.pos_of_ne_zero hrem
    have hremLt : rem < 32 := by dsimp [rem]; exact Nat.mod_lt _ (by decide)
    have hland : (UInt256.ofNat dataLen).land ⟨31⟩ = UInt256.ofNat rem := by
      simpa only [rem] using hwordRem
    have hfinal : limbsToBytesMemory mem aw limbs out dataLen =
        partialMemory state.memory source existing (UInt256.ofNat dataLen) out := by
      simp [limbsToBytesMemory, limbsToBytesSuffixMemory, state, source, existing,
        rem, hrem]
    have hgap : (partialOutputAddress out).toNat - state.memory.size < USize.size := by
      rw [Nat.sub_eq_zero_of_le (by simpa only [state] using (show
          (partialOutputAddress out).toNat ≤
          (limbsToBytesFullState mem aw limbs out dataLen).memory.size by
            have := hpartialIn (by simpa only [rem] using hrem)
            omega))]
      exact lt_usize 0 (by norm_num)
    have hprefix : Model.bytesToNatPadded
        (partialMemory state.memory source existing (UInt256.ofNat dataLen) out)
        (out.toNat + 32) rem = source.toNat := by
      rw [← houtNat]
      exact partialMemory_prefixValue hremPos hremLt hland (by
        simpa only [source, state, rem] using hpartialFit (by
          simpa only [rem] using hrem)) (by rw [houtNat]; omega) hgap
    by_cases hcount : count = 0
    · have hlenEq : dataLen = rem := by dsimp [rem, count] at *; omega
      have hcountRaw : dataLen / 32 = 0 := by simpa only [count] using hcount
      have hremRaw : dataLen % 32 ≠ 0 := by simpa only [rem] using hrem
      rw [hfinal]
      calc
        Model.bytesToNatPadded
            (partialMemory state.memory source existing (UInt256.ofNat dataLen) out)
            (out.toNat + 32) dataLen = source.toNat := by simpa only [hlenEq] using hprefix
        _ = Modexp.wordLimbsToNat (serializedSourceWords mem aw limbs out dataLen) := by
          unfold serializedSourceWords
          dsimp only
          rw [hcountRaw, fullSourceWords, if_neg hremRaw, List.nil_append]
          simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero, source, state]
    · have hcountPos : 0 < count := Nat.pos_of_ne_zero hcount
      have hsuffix : Model.bytesToNatPadded
          (partialMemory state.memory source existing (UInt256.ofNat dataLen) out)
          (out.toNat + 32 + rem) (32 * count) =
          Model.bytesToNatPadded state.memory (out.toNat + 32 + rem) (32 * count) := by
        rw [← houtNat]
        exact partialMemory_suffixValue hremPos hremLt hland (by
          simpa only [source, state, rem] using hpartialFit (by
            simpa only [rem] using hrem)) (by
            simpa only [state, existing] using hexisting (by
              simpa only [rem] using hrem)) (by
              simpa only [state] using hpartialIn (by
                simpa only [rem] using hrem)) (by rw [houtNat]; omega) (by omega)
      have hsplit := model_bytesToNatPadded_split
        (partialMemory state.memory source existing (UInt256.ofNat dataLen) out)
        (out.toNat + 32) rem (32 * count)
      have hlenEq : rem + 32 * count = dataLen := by dsimp [rem, count] at *; omega
      rw [hlenEq, hprefix, hsuffix, hfullValue] at hsplit
      rw [hfinal, hsplit]
      unfold serializedSourceWords
      simp only [state, count, rem, hrem, if_false, words, source]
      rw [Modexp.wordLimbsToNat_append, fullSourceWords_length]
      simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
      rw [show UInt256.size ^ count = 256 ^ (32 * count) by
        rw [show UInt256.size = 256 ^ 32 by native_decide, ← Nat.pow_mul]]
      ring

end Modexp.MultiLimbLimbsToBytesSemantic
