import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortContract
import Examples.Precompiles.Modexp.WideWordBridge

/-!
# Exact `div512by256` helper contracts

The generated helper has a short `hi = 0` path using EVM `DIV`/`MOD` and a longer `hi > 0`
path implementing exact 512-by-256 division with a modular inverse.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbDiv512

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def nonzeroRemainder (hi lo d : UInt256) : UInt256 :=
  let r256 := UInt256.addMod (UInt256.mod (UInt256.lnot ⟨0⟩) d) ⟨1⟩ d
  UInt256.addMod (UInt256.mulMod hi r256 d) lo d

def lowbitWord (d : UInt256) : UInt256 :=
  UInt256.land d (UInt256.sub ⟨0⟩ d)

def oddPartWord (d : UInt256) : UInt256 :=
  UInt256.div d (lowbitWord d)

def quotientLowExact (hi lo d : UInt256) : UInt256 :=
  UInt256.sub lo (nonzeroRemainder hi lo d)

def quotientHighExact (hi lo d : UInt256) : UInt256 :=
  UInt256.sub hi (UInt256.lt lo (nonzeroRemainder hi lo d))

def quotientFlip (d : UInt256) : UInt256 :=
  let twos := lowbitWord d
  UInt256.add (UInt256.div (UInt256.sub ⟨0⟩ twos) twos) ⟨1⟩

def quotientExactDiv (hi lo d : UInt256) : UInt256 :=
  let twos := lowbitWord d
  UInt256.lor (UInt256.div (quotientLowExact hi lo d) twos)
    (UInt256.mul (quotientHighExact hi lo d) (quotientFlip d))

def inverseSeed (oddD : UInt256) : UInt256 :=
  UInt256.xor (UInt256.mul ⟨3⟩ oddD) ⟨2⟩

def inverseStep (oddD inv : UInt256) : UInt256 :=
  UInt256.mul (UInt256.sub ⟨2⟩ (UInt256.mul oddD inv)) inv

def inverse6 (oddD : UInt256) : UInt256 :=
  let inv0 := inverseSeed oddD
  let inv1 := inverseStep oddD inv0
  let inv2 := inverseStep oddD inv1
  let inv3 := inverseStep oddD inv2
  let inv4 := inverseStep oddD inv3
  let inv5 := inverseStep oddD inv4
  inverseStep oddD inv5

def nonzeroQuotient (hi lo d : UInt256) : UInt256 :=
  let oddD := oddPartWord d
  UInt256.mul (quotientExactDiv hi lo d) (inverse6 oddD)

def numerator (hi lo : UInt256) : Nat :=
  hi.toNat * UInt256.size + lo.toNat

theorem nat_land_pow_mask_sub (w n : Nat) (hn : n < 2 ^ w) :
    n &&& (2 ^ w - 1 - n) = 0 := by
  induction w generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      subst n
      simp
  | succ w ih =>
      cases n using Nat.bitCasesOn with
      | bit b n =>
          cases b
          · have hn' : n < 2 ^ w := by
              simp only [Nat.bit_false, Nat.pow_succ] at hn
              omega
            rw [show 2 ^ (w + 1) - 1 - Nat.bit false n =
                  Nat.bit true (2 ^ w - 1 - n) by
                simp [Nat.pow_succ]
                omega]
            change Nat.bit false n &&& Nat.bit true (2 ^ w - 1 - n) = 0
            rw [Nat.land_bit, ih n hn']
            rfl
          · have hn' : n < 2 ^ w := by
              simp only [Nat.bit_true, Nat.pow_succ] at hn
              omega
            rw [show 2 ^ (w + 1) - 1 - Nat.bit true n =
                  Nat.bit false (2 ^ w - 1 - n) by
                simp [Nat.pow_succ]
                omega]
            change Nat.bit true n &&& Nat.bit false (2 ^ w - 1 - n) = 0
            rw [Nat.land_bit, ih n hn']
            rfl

theorem nat_land_sub_self_eq_two_pow_padicVal (w n : Nat)
    (hn0 : n ≠ 0) (hn : n < 2 ^ w) :
    n &&& (2 ^ w - n) = 2 ^ padicValNat 2 n := by
  induction w generalizing n with
  | zero => simp at hn; contradiction
  | succ w ih =>
      cases n using Nat.bitCasesOn with
      | bit b n =>
          cases b
          · have hn0' : n ≠ 0 := by simpa using hn0
            have hn' : n < 2 ^ w := by
              simp only [Nat.bit_false, Nat.pow_succ] at hn
              omega
            rw [show 2 ^ (w + 1) - Nat.bit false n =
                  Nat.bit false (2 ^ w - n) by
                  simp [Nat.pow_succ]
                  omega]
            change Nat.bit false n &&& Nat.bit false (2 ^ w - n) =
              2 ^ padicValNat 2 (Nat.bit false n)
            rw [Nat.land_bit, ih n hn0' hn']
            change Nat.bit false (2 ^ padicValNat 2 n) =
              2 ^ padicValNat 2 (2 * n)
            rw [padicValNat_base_mul (p := 2) (n := n) (by omega) hn0']
            simp [Nat.pow_succ, Nat.mul_comm]
          · have hn' : n < 2 ^ w := by
              simp only [Nat.bit_true, Nat.pow_succ] at hn
              omega
            rw [show 2 ^ (w + 1) - Nat.bit true n =
                  Nat.bit true (2 ^ w - 1 - n) by
                  simp [Nat.pow_succ]
                  omega]
            have hodd : padicValNat 2 (2 * n + 1) = 0 := by
              apply (padicValNat.eq_zero_iff (p := 2)).mpr
              right; right
              omega
            change Nat.bit true n &&& Nat.bit true (2 ^ w - 1 - n) =
              2 ^ padicValNat 2 (2 * n + 1)
            rw [Nat.land_bit, nat_land_pow_mask_sub w n hn', hodd]
            rfl

theorem nat_lor_split_div (w k high low : Nat) (hk : k < w)
    (hlow : low < 2 ^ w) (htlow : 2 ^ k ∣ low) :
    (low / 2 ^ k |||
        (high * (2 ^ (w - k) % 2 ^ w)) % 2 ^ w) % 2 ^ w =
      ((high * 2 ^ w + low) / 2 ^ k) % 2 ^ w := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hs : w - k < w := by omega
    have hfactor : 2 ^ w = 2 ^ k * 2 ^ (w - k) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hk.le]
    have hflip : 2 ^ (w - k) % 2 ^ w = 2 ^ (w - k) :=
      Nat.mod_eq_of_lt ((Nat.pow_lt_pow_iff_right (by omega)).mpr hs)
    have hproduct : (high * 2 ^ (w - k)) % 2 ^ w =
        (high % 2 ^ k) * 2 ^ (w - k) := by
      rw [hfactor, Nat.mul_mod_mul_right]
    have hlowDiv : low / 2 ^ k < 2 ^ (w - k) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc
        low < 2 ^ w := hlow
        _ = 2 ^ (w - k) * 2 ^ k := by rw [hfactor, Nat.mul_comm]
    rw [hflip, hproduct]
    have hlor :
        (low / 2 ^ k ||| (high % 2 ^ k) * 2 ^ (w - k)) =
          low / 2 ^ k + (high % 2 ^ k) * 2 ^ (w - k) := by
      exact nat_lor_shift_add
        (low / 2 ^ k) (high % 2 ^ k) (w - k) hlowDiv
    rw [hlor]
    have hfirst : 2 ^ k ∣ high * 2 ^ w :=
      dvd_mul_of_dvd_right (by rw [hfactor]; exact dvd_mul_right _ _) high
    rw [Nat.add_div_of_dvd_right hfirst,
      Nat.mul_div_assoc high (by rw [hfactor]; exact dvd_mul_right _ _)]
    have hsizeDiv : 2 ^ w / 2 ^ k = 2 ^ (w - k) := by
      rw [hfactor, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ k)]
    rw [hsizeDiv]
    have hsmallLt : (high % 2 ^ k) * 2 ^ (w - k) < 2 ^ w := by
      rw [hfactor]
      gcongr
      exact Nat.mod_lt _ (by positivity)
    have hm : high * 2 ^ (w - k) ≡
        (high % 2 ^ k) * 2 ^ (w - k) [MOD 2 ^ w] := by
      unfold Nat.ModEq
      rw [hproduct, Nat.mod_eq_of_lt hsmallLt]
    simpa [Nat.add_comm] using
      (hm.add_left (low / 2 ^ k)).symm

theorem lowbit_toNat (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (lowbitWord d).toNat = 2 ^ padicValNat 2 d.toNat := by
  have hdNat0 : d.toNat ≠ 0 := by
    intro h
    apply hd0
    apply u256_inj
    simpa using h
  unfold lowbitWord
  rw [uland_toNat,
    usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := d)
      (by simpa using Nat.pos_of_ne_zero hdNat0)]
  simpa [UInt256.size] using
    nat_land_sub_self_eq_two_pow_padicVal 256 d.toNat hdNat0 d.val.isLt

theorem lowbit_ne_zero (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    lowbitWord d ≠ ⟨0⟩ := by
  intro h
  have := congrArg UInt256.toNat h
  rw [lowbit_toNat d hd0] at this
  norm_num at this

theorem lowbit_dvd (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (lowbitWord d).toNat ∣ d.toNat := by
  rw [lowbit_toNat d hd0]
  exact pow_padicValNat_dvd

theorem lowbit_mul_oddPart (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (lowbitWord d).toNat * (oddPartWord d).toNat = d.toNat := by
  rw [oddPartWord, udiv_toNat]
  exact Nat.mul_div_cancel' (lowbit_dvd d hd0)

theorem oddPart_is_odd (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (oddPartWord d).toNat % 2 = 1 := by
  have hdNat0 : d.toNat ≠ 0 := by
    intro h
    apply hd0
    apply u256_inj
    simpa using h
  have hfactor := lowbit_mul_oddPart d hd0
  rw [lowbit_toNat d hd0] at hfactor
  have hcanonical : (oddPartWord d).toNat = Nat.divMaxPow d.toNat 2 := by
    have hcanonicalFactor := Nat.pow_padicValNat_mul_divMaxPow 2 d.toNat
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ padicValNat 2 d.toNat)
      (hfactor.trans hcanonicalFactor.symm)
  rw [hcanonical]
  have hnot := Nat.not_dvd_divMaxPow (p := 2) (n := d.toNat) (by omega) hdNat0
  have hmodne : Nat.divMaxPow d.toNat 2 % 2 ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnot
  have hmodlt := Nat.mod_lt (Nat.divMaxPow d.toNat 2) (by omega : 0 < 2)
  omega

theorem padicValNat_two_le_width (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    padicValNat 2 d.toNat < 256 := by
  have hdNat0 : d.toNat ≠ 0 := by
    intro h
    apply hd0
    apply u256_inj
    simpa using h
  have hpowLe : 2 ^ padicValNat 2 d.toNat ≤ d.toNat :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hdNat0) pow_padicValNat_dvd
  have hpowLt : 2 ^ padicValNat 2 d.toNat < 2 ^ 256 :=
    hpowLe.trans_lt d.val.isLt
  exact (Nat.pow_lt_pow_iff_right (by omega)).mp hpowLt

theorem lowbit_dvd_size (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (lowbitWord d).toNat ∣ UInt256.size := by
  rw [lowbit_toNat d hd0]
  change 2 ^ padicValNat 2 d.toNat ∣ 2 ^ 256
  exact Nat.pow_dvd_pow 2 (padicValNat_two_le_width d hd0).le

theorem size_div_lowbit (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    UInt256.size / (lowbitWord d).toNat =
      2 ^ (256 - padicValNat 2 d.toNat) := by
  let k := padicValNat 2 d.toNat
  have hk : k ≤ 256 := (padicValNat_two_le_width d hd0).le
  have hfactor : UInt256.size = 2 ^ k * 2 ^ (256 - k) := by
    change 2 ^ 256 = 2 ^ k * 2 ^ (256 - k)
    rw [← Nat.pow_add]
    rw [Nat.add_sub_of_le hk]
  rw [lowbit_toNat d hd0, hfactor]
  change 2 ^ k * 2 ^ (256 - k) / 2 ^ k = 2 ^ (256 - k)
  rw [Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ k)]

theorem quotientFlip_toNat (d : UInt256) (hd0 : d ≠ ⟨0⟩) :
    (quotientFlip d).toNat =
      (UInt256.size / (lowbitWord d).toNat) % UInt256.size := by
  let twos := lowbitWord d
  have ht0 : 0 < twos.toNat := by
    exact Nat.pos_of_ne_zero (fun h ↦ lowbit_ne_zero d hd0 (u256_inj h))
  have htLt : twos.toNat < UInt256.size := twos.val.isLt
  have htDvd : twos.toNat ∣ UInt256.size := lowbit_dvd_size d hd0
  have hsub : (UInt256.sub ⟨0⟩ twos).toNat = UInt256.size - twos.toNat := by
    simpa using usub_toNat_underflow
      (a := (⟨0⟩ : UInt256)) (b := twos) ht0
  change
    (UInt256.div (UInt256.sub ⟨0⟩ twos) twos + ⟨1⟩).toNat =
      (UInt256.size / twos.toNat) % UInt256.size
  rw [uadd_toNat, udiv_toNat, hsub]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
  have hdivSub : (UInt256.size - twos.toNat) / twos.toNat + 1 =
      UInt256.size / twos.toNat := by
    obtain ⟨q, hq⟩ := htDvd
    rw [hq]
    have hq0 : 0 < q := by
      by_contra h
      have : q = 0 := by omega
      subst q
      norm_num [UInt256.size] at hq
    rw [show twos.toNat * q - twos.toNat = twos.toNat * (q - 1) by
      calc
        twos.toNat * q - twos.toNat =
            twos.toNat * q - twos.toNat * 1 := by simp
        _ = twos.toNat * (q - 1) :=
          (Nat.mul_sub_left_distrib twos.toNat q 1).symm,
      Nat.mul_div_cancel_left _ ht0, Nat.mul_div_cancel_left _ ht0]
    omega
  rw [hdivSub]

theorem exactWords_numerator (hi lo d : UInt256) (hhi : hi ≠ ⟨0⟩) :
    (quotientHighExact hi lo d).toNat * UInt256.size +
        (quotientLowExact hi lo d).toNat =
      numerator hi lo - (nonzeroRemainder hi lo d).toNat := by
  let rem := nonzeroRemainder hi lo d
  change
    (UInt256.sub hi (UInt256.lt lo rem)).toNat * UInt256.size +
        (UInt256.sub lo rem).toNat =
      hi.toNat * UInt256.size + lo.toNat - rem.toNat
  have hhiNat : 0 < hi.toNat := by
    by_contra h
    apply hhi
    apply u256_inj
    simp at h
    simpa using h
  have hremLt : rem.toNat < UInt256.size := rem.val.isLt
  have hhiSplit :
      (hi.toNat - 1) * UInt256.size + UInt256.size =
        hi.toNat * UInt256.size := by
    calc
      (hi.toNat - 1) * UInt256.size + UInt256.size =
          ((hi.toNat - 1) + 1) * UInt256.size := by ring
      _ = hi.toNat * UInt256.size := by rw [Nat.sub_add_cancel (by omega)]
  by_cases hborrow : lo.toNat < rem.toNat
  · have hlt : UInt256.lt lo rem = ⟨1⟩ := ult_one hborrow
    have hlo : (UInt256.sub lo rem).toNat =
        UInt256.size + lo.toNat - rem.toNat :=
      usub_toNat_underflow hborrow
    have hhigh : (UInt256.sub hi (⟨1⟩ : UInt256)).toNat = hi.toNat - 1 := by
      apply usub_toNat
      simpa using hhiNat
    rw [hlt, hlo, hhigh]
    omega
  · have hle : rem.toNat ≤ lo.toNat := by omega
    have hlt : UInt256.lt lo rem = ⟨0⟩ := ult_zero hle
    have hlo : (UInt256.sub lo rem).toNat = lo.toNat - rem.toNat :=
      usub_toNat hle
    rw [hlt, hlo]
    have hhigh : UInt256.sub hi ⟨0⟩ = hi := by
      apply u256_inj
      simp [usub_toNat]
    rw [hhigh]
    rw [Nat.add_sub_assoc hle]

theorem nonzeroRemainder_toNat
    (hi lo d : UInt256) (hd : 1 < d.toNat) :
    (nonzeroRemainder hi lo d).toNat = numerator hi lo % d.toNat := by
  have hd0 : d.toNat ≠ 0 := by omega
  have hr256 :
      (UInt256.addMod (UInt256.mod (UInt256.lnot ⟨0⟩) d) ⟨1⟩ d).toNat =
        UInt256.size % d.toNat := by
    simpa only [Modexp.wideR256] using Modexp.wideR256_toNat d hd
  unfold nonzeroRemainder numerator
  rw [addMod_toNat hd0, mulMod_toNat hd0, hr256]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem quotientExactDiv_toNat (hi lo d : UInt256)
    (hhi : hi ≠ ⟨0⟩) (hd : 1 < d.toNat) :
    (quotientExactDiv hi lo d).toNat =
      ((numerator hi lo - (nonzeroRemainder hi lo d).toNat) /
        (lowbitWord d).toNat) % UInt256.size := by
  let rem := nonzeroRemainder hi lo d
  let high := quotientHighExact hi lo d
  let low := quotientLowExact hi lo d
  let twos := lowbitWord d
  let k := padicValNat 2 d.toNat
  have hd0 : d ≠ ⟨0⟩ := by
    intro h
    have := congrArg UInt256.toNat h
    norm_num at this
    omega
  have hk : k < 256 := padicValNat_two_le_width d hd0
  have hrem : rem.toNat = numerator hi lo % d.toNat :=
    nonzeroRemainder_toNat hi lo d hd
  have hwords : high.toNat * UInt256.size + low.toNat =
      numerator hi lo - rem.toNat :=
    exactWords_numerator hi lo d hhi
  have hdivisor : d.toNat ∣ numerator hi lo - rem.toNat := by
    refine ⟨numerator hi lo / d.toNat, ?_⟩
    have hsplit := Nat.mod_add_div (numerator hi lo) d.toNat
    rw [hrem]
    omega
  have htwosX : twos.toNat ∣ numerator hi lo - rem.toNat :=
    (lowbit_dvd d hd0).trans hdivisor
  have htwosHigh : twos.toNat ∣ high.toNat * UInt256.size :=
    dvd_mul_of_dvd_right (lowbit_dvd_size d hd0) high.toNat
  have htwosLow : twos.toNat ∣ low.toNat := by
    apply (Nat.dvd_add_iff_left htwosHigh).mpr
    rw [Nat.add_comm, hwords]
    exact htwosX
  have hreconstruct := nat_lor_split_div 256 k high.toNat low.toNat hk
    low.val.isLt (by simpa [k, twos, lowbit_toNat d hd0] using htwosLow)
  change
    (UInt256.lor (UInt256.div low twos)
      (UInt256.mul high (quotientFlip d))).toNat =
      ((numerator hi lo - rem.toNat) / twos.toNat) % UInt256.size
  rw [u256_lor_toNat, udiv_toNat, u256_mul_toNat,
    quotientFlip_toNat d hd0, size_div_lowbit d hd0]
  change
    (low.toNat / twos.toNat |||
      high.toNat * (2 ^ (256 - k) % UInt256.size) % UInt256.size) %
        UInt256.size =
      ((numerator hi lo - rem.toNat) / twos.toNat) % UInt256.size
  rw [lowbit_toNat d hd0]
  change
    (low.toNat / 2 ^ k |||
      high.toNat * (2 ^ (256 - k) % 2 ^ 256) % 2 ^ 256) % 2 ^ 256 =
      ((numerator hi lo - rem.toNat) / 2 ^ k) % 2 ^ 256
  rw [← hwords]
  exact hreconstruct

def bvInverseSeed (oddD : BitVec 256) : BitVec 256 :=
  (3 * oddD) ^^^ 2

def bvInverseStep (oddD inv : BitVec 256) : BitVec 256 :=
  (2 - oddD * inv) * inv

def bvInverse6 (oddD : BitVec 256) : BitVec 256 :=
  let inv0 := bvInverseSeed oddD
  let inv1 := bvInverseStep oddD inv0
  let inv2 := bvInverseStep oddD inv1
  let inv3 := bvInverseStep oddD inv2
  let inv4 := bvInverseStep oddD inv3
  let inv5 := bvInverseStep oddD inv4
  bvInverseStep oddD inv5

theorem newton_modEq {m d inv : Int} (hcorrect : d * inv ≡ 1 [ZMOD m]) :
    d * ((2 - d * inv) * inv) ≡ 1 [ZMOD m * m] := by
  rw [Int.modEq_iff_dvd]
  have hsquare := mul_dvd_mul hcorrect.dvd hcorrect.dvd
  convert hsquare using 1 <;> ring

theorem uintMul_modEq (a b : UInt256) :
    (UInt256.mul a b).toNat ≡ a.toNat * b.toNat [ZMOD UInt256.size] := by
  change ((UInt256.mul a b).toNat : Int) ≡ (↑(a.toNat * b.toNat) : Int)
    [ZMOD (↑UInt256.size : Int)]
  rw [Int.natCast_modEq_iff]
  unfold Nat.ModEq
  rw [u256_mul_toNat, Nat.mod_mod]

theorem uintSub_modEq (a b : UInt256) :
    ((UInt256.sub a b).toNat : Int) ≡ (a.toNat : Int) - b.toNat
      [ZMOD UInt256.size] := by
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat hle, Int.ofNat_sub hle]
  · have hlt : a.toNat < b.toNat := by omega
    have hb : b.toNat < UInt256.size := b.val.isLt
    rw [usub_toNat_underflow hlt,
      Int.ofNat_sub (by omega : b.toNat ≤ UInt256.size + a.toNat), Nat.cast_add]
    rw [Int.modEq_iff_dvd]
    use -1
    ring

theorem inverseStep_modEq {m : Int} (oddD inv : UInt256)
    (hm : m * m ∣ (UInt256.size : Int))
    (hcorrect : (oddD.toNat : Int) * inv.toNat ≡ 1 [ZMOD m]) :
    (oddD.toNat : Int) * (inverseStep oddD inv).toNat ≡ 1 [ZMOD m * m] := by
  let product := UInt256.mul oddD inv
  let correction := UInt256.sub ⟨2⟩ product
  have hp : (product.toNat : Int) ≡ (oddD.toNat : Int) * inv.toNat
      [ZMOD m * m] :=
    (uintMul_modEq oddD inv).of_dvd hm
  have hc : (correction.toNat : Int) ≡
      2 - (oddD.toNat : Int) * inv.toNat [ZMOD m * m] := by
    have hsub := (uintSub_modEq (⟨2⟩ : UInt256) product).of_dvd hm
    have htwo : ((⟨2⟩ : UInt256).toNat : Int) = 2 := by native_decide
    rw [htwo] at hsub
    exact hsub.trans (Int.ModEq.rfl.sub hp)
  have hs : ((inverseStep oddD inv).toNat : Int) ≡
      (2 - (oddD.toNat : Int) * inv.toNat) * inv.toNat [ZMOD m * m] := by
    have hmul := (uintMul_modEq correction inv).of_dvd hm
    exact hmul.trans (hc.mul Int.ModEq.rfl)
  exact (Int.ModEq.rfl.mul hs).trans (newton_modEq hcorrect)

theorem uintXor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  unfold UInt256.xor UInt256.toNat Fin.xor
  change (a.val.val ^^^ b.val.val) % UInt256.size = a.val.val ^^^ b.val.val
  rw [Nat.mod_eq_of_lt]
  change a.val.val ^^^ b.val.val < 2 ^ 256
  exact Nat.xor_lt_two_pow a.val.isLt b.val.isLt

theorem natXor_mod_two_pow (a b k : Nat) :
    (a ^^^ b) % 2 ^ k = (a % 2 ^ k) ^^^ (b % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < k <;> simp [hi]

theorem inverseSeed_modEq (oddD : UInt256) (hodd : oddD.toNat % 2 = 1) :
    (oddD.toNat : Int) * (inverseSeed oddD).toNat ≡ 1 [ZMOD 16] := by
  have hseed : (inverseSeed oddD).toNat % 16 =
      ((3 * (oddD.toNat % 16)) ^^^ 2) % 16 := by
    unfold inverseSeed
    rw [uintXor_toNat, u256_mul_toNat]
    norm_num
    calc
      (3 * oddD.toNat % UInt256.size ^^^ 2) % 16 =
          ((3 * oddD.toNat % UInt256.size) % 16) ^^^ (2 % 16) := by
            simpa using natXor_mod_two_pow (3 * oddD.toNat % UInt256.size) 2 4
      _ = ((3 * (oddD.toNat % 16)) ^^^ 2) % 16 := by
        rw [Nat.mod_mod_of_dvd (3 * oddD.toNat)
          (by norm_num [UInt256.size] : 16 ∣ UInt256.size), Nat.mul_mod]
        norm_num
        rw [Nat.mul_mod]
        symm
        simpa [Nat.mul_mod] using
          natXor_mod_two_pow (3 * (oddD.toNat % 16)) 2 4
  change (↑(oddD.toNat * (inverseSeed oddD).toNat) : Int) ≡ (↑1 : Int) [ZMOD (↑16 : Int)]
  apply Int.natCast_modEq_iff.mpr
  unfold Nat.ModEq
  rw [Nat.mul_mod, hseed]
  mod_cases hd : oddD.toNat % 16
  all_goals
    unfold Nat.ModEq at hd
    norm_num at hd
    have hparity : oddD.toNat % 2 = (oddD.toNat % 16) % 2 :=
      (Nat.mod_mod_of_dvd oddD.toNat (by norm_num : 2 ∣ 16)).symm
    rw [hd, hodd] at hparity
    first
    | omega
    | rw [Nat.mul_mod, hd]
      native_decide

theorem inverse6_mul_of_odd (oddD : UInt256) (hodd : oddD.toNat % 2 = 1) :
    UInt256.mul oddD (inverse6 oddD) = ⟨1⟩ := by
  let inv0 := inverseSeed oddD
  let inv1 := inverseStep oddD inv0
  let inv2 := inverseStep oddD inv1
  let inv3 := inverseStep oddD inv2
  let inv4 := inverseStep oddD inv3
  let inv5 := inverseStep oddD inv4
  let inv6 := inverseStep oddD inv5
  have h0 : (oddD.toNat : Int) * inv0.toNat ≡ 1 [ZMOD 16] :=
    inverseSeed_modEq oddD hodd
  have h1 := inverseStep_modEq (m := 16) oddD inv0
    (by norm_num [UInt256.size]) h0
  norm_num at h1
  have h2 := inverseStep_modEq (m := 256) oddD inv1
    (by norm_num [UInt256.size]) h1
  norm_num at h2
  have h3 := inverseStep_modEq (m := 65536) oddD inv2
    (by norm_num [UInt256.size]) h2
  norm_num at h3
  have h4 := inverseStep_modEq (m := 4294967296) oddD inv3
    (by norm_num [UInt256.size]) h3
  norm_num at h4
  have h5 := inverseStep_modEq (m := 18446744073709551616) oddD inv4
    (by norm_num [UInt256.size]) h4
  norm_num at h5
  have h6 := inverseStep_modEq
    (m := 340282366920938463463374607431768211456) oddD inv5
    (by norm_num [UInt256.size]) h5
  norm_num [UInt256.size] at h6
  have hword : ((UInt256.mul oddD inv6).toNat : Int) ≡ 1
      [ZMOD UInt256.size] :=
    (uintMul_modEq oddD inv6).trans h6
  have hnat := Int.natCast_modEq_iff.mp hword
  unfold Nat.ModEq at hnat
  have hlt : (UInt256.mul oddD inv6).toNat < UInt256.size :=
    (UInt256.mul oddD inv6).val.isLt
  rw [Nat.mod_eq_of_lt hlt] at hnat
  norm_num [UInt256.size] at hnat
  apply u256_inj
  simpa [inverse6, inv0, inv1, inv2, inv3, inv4, inv5, inv6] using hnat

theorem nonzeroQuotient_toNat (hi lo d : UInt256)
    (hhi : hi ≠ ⟨0⟩) (hd : 1 < d.toNat) (hhiLt : hi.toNat < d.toNat) :
    (nonzeroQuotient hi lo d).toNat = numerator hi lo / d.toNat := by
  let rem := nonzeroRemainder hi lo d
  let twos := lowbitWord d
  let oddD := oddPartWord d
  let exactDiv := quotientExactDiv hi lo d
  let inv := inverse6 oddD
  let q := numerator hi lo / d.toNat
  have hd0 : d ≠ ⟨0⟩ := by
    intro h
    have := congrArg UInt256.toNat h
    norm_num at this
    omega
  have ht0 : 0 < twos.toNat :=
    Nat.pos_of_ne_zero (fun h ↦ lowbit_ne_zero d hd0 (u256_inj h))
  have hrem : rem.toNat = numerator hi lo % d.toNat :=
    nonzeroRemainder_toNat hi lo d hd
  have hquotientSplit : numerator hi lo - rem.toNat = d.toNat * q := by
    have hsplit := Nat.mod_add_div (numerator hi lo) d.toNat
    rw [hrem]
    change numerator hi lo - numerator hi lo % d.toNat =
      d.toNat * (numerator hi lo / d.toNat)
    omega
  have hdivided :
      (numerator hi lo - rem.toNat) / twos.toNat = oddD.toNat * q := by
    have hfactor : twos.toNat * oddD.toNat = d.toNat :=
      lowbit_mul_oddPart d hd0
    rw [hquotientSplit, ← hfactor, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ ht0]
  have hexact : exactDiv.toNat = (oddD.toNat * q) % UInt256.size := by
    rw [quotientExactDiv_toNat hi lo d hhi hd, hdivided]
  have hinvWord : UInt256.mul oddD inv = ⟨1⟩ :=
    inverse6_mul_of_odd oddD (oddPart_is_odd d hd0)
  have hinvNat : (oddD.toNat * inv.toNat) % UInt256.size = 1 := by
    have := congrArg UInt256.toNat hinvWord
    rw [u256_mul_toNat] at this
    simpa using this
  have hexactMod : exactDiv.toNat ≡ oddD.toNat * q [MOD UInt256.size] := by
    unfold Nat.ModEq
    rw [hexact, Nat.mod_mod]
  have hinvMod : oddD.toNat * inv.toNat ≡ 1 [MOD UInt256.size] := by
    unfold Nat.ModEq
    rw [hinvNat]
    norm_num [UInt256.size]
  have hcancel : exactDiv.toNat * inv.toNat ≡ q [MOD UInt256.size] := by
    apply (hexactMod.mul_right inv.toNat).trans
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hinvMod.mul_left q
  have hnumeratorLt : numerator hi lo < d.toNat * UInt256.size := by
    unfold numerator
    have hloLt := lo.val.isLt
    calc
      hi.toNat * UInt256.size + lo.toNat <
          hi.toNat * UInt256.size + UInt256.size :=
        Nat.add_lt_add_left hloLt _
      _ = (hi.toNat + 1) * UInt256.size := by ring
      _ ≤ d.toNat * UInt256.size :=
        Nat.mul_le_mul_right UInt256.size (by omega)
  have hqLt : q < UInt256.size := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d.toNat)]
    simpa [Nat.mul_comm] using hnumeratorLt
  change (UInt256.mul exactDiv inv).toNat = q
  rw [u256_mul_toNat]
  unfold Nat.ModEq at hcancel
  rw [Nat.mod_eq_of_lt hqLt] at hcancel
  exact hcancel

/-- With a zero high word, the helper returns the ordinary EVM remainder and quotient. -/
theorem zeroHighExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {lo d ret : UInt256}
    (hdepth : tail.length + 4 ≤ 1017)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨7898⟩
      (⟨0⟩ :: lo :: d :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret
      (UInt256.mod lo d :: UInt256.div lo d :: tail)
      mem aw rdata acc (k + 34) (C + 117) := by
  have rd8034 := GeneratedTraces.trace_7898_taken (by omega) h
    (by native_decide) (by native_decide) (by native_decide)
  have rd7926 := GeneratedTraces.trace_8027_notTaken
    (by omega) rd8034
    (by native_decide) (by native_decide)
  have rdret := GeneratedTraces.trace_7919_jump
    (tail := UInt256.mod lo d :: UInt256.div lo d :: tail)
    (by simp only [List.length_cons]; omega) rd7926
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 34) (C' := C + 117) (by omega) (by omega)
  simpa using normalized

/-- With a nonzero high word, the helper follows the modular-inverse implementation exactly. -/
theorem nonzeroHighExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {hi lo d ret : UInt256}
    (hdepth : tail.length + 4 ≤ 1017)
    (hhi : hi ≠ ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨7898⟩
      (hi :: lo :: d :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret
      (nonzeroRemainder hi lo d :: nonzeroQuotient hi lo d :: tail)
      mem aw rdata acc (k + 111) (C + 392) := by
  have hizero : UInt256.isZero hi = ⟨0⟩ := isZero_eq_zero_of_ne hhi
  have rd7920 := GeneratedTraces.trace_7898_notTaken (by omega) h
    (by native_decide) hizero
  have rd7930 := GeneratedTraces.trace_7913_taken
    (tail := lo :: hi :: d :: ret :: ⟨0⟩ :: ⟨0⟩ :: tail)
    (by simp only [List.length_cons]; omega) rd7920 (by native_decide)
    (by rw [hizero]; native_decide) (by native_decide)
  have rdret := GeneratedTraces.trace_7923_jump
    (tail := tail) (by omega) rd7930 (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 111) (C' := C + 392) (by omega) (by omega)
  simpa only [nonzeroRemainder, nonzeroQuotient] using normalized

end Modexp.MultiLimbDiv512
