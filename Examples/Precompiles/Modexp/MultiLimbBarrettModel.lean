import Examples.Precompiles.Modexp.MultiLimbBackendModel
import Examples.Precompiles.Modexp.MultiLimbSubtractionModel

/-!
# Pure Barrett backend bridge

Barrett values are ordinary reduced limb values, unlike Montgomery-domain values.  Consequently
the concrete multiply/reduce contract plugs directly into the shared MSB-first exponent proof.
-/

open Ethereum

namespace Modexp

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-! ## Pure Barrett quotient bound -/

def barrettApproxQuotient (b R n x : Nat) : Nat :=
  let q1 := x / b
  let mu := (b * R) / n
  (q1 * mu) / R

/-- The classical Barrett quotient estimate never exceeds the true quotient and is less than
three modulus units below the input.  This is the arithmetic reason the deployed correction loop
needs at most two selected subtractions. -/
theorem barrettApproxQuotient_bounds
    (b R n x : Nat) (hb : 0 < b) (hR : 0 < R) (hn : 0 < n)
    (hbn : b ≤ n) (hx : x < b * R) :
    let q3 := barrettApproxQuotient b R n x
    q3 * n ≤ x ∧ x < q3 * n + 3 * n := by
  let q1 := x / b
  let mu := (b * R) / n
  let q3 := (q1 * mu) / R
  have hxDecomp := Nat.mod_add_div x b
  have hxRem := Nat.mod_lt x hb
  have hmuDecomp := Nat.mod_add_div (b * R) n
  have hmuRem := Nat.mod_lt (b * R) hn
  have hq3Decomp := Nat.mod_add_div (q1 * mu) R
  have hq3Rem := Nat.mod_lt (q1 * mu) hR
  have hq1Lower : b * q1 ≤ x := by
    simpa [q1, Nat.mul_comm] using Nat.div_mul_le_self x b
  have hq1Upper : x < b * (q1 + 1) := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hb]
    simp [q1]
  have hmuLower : n * mu ≤ b * R := by
    simpa [mu, Nat.mul_comm] using Nat.div_mul_le_self (b * R) n
  have hmuUpper : b * R ≤ n * (mu + 1) := by
    have hstrict : b * R < (mu + 1) * n := by
      rw [← Nat.div_lt_iff_lt_mul hn]
      simp [mu]
    simpa [Nat.mul_comm] using hstrict.le
  have hq3Lower : R * q3 ≤ q1 * mu := by
    simpa [q3, Nat.mul_comm] using Nat.div_mul_le_self (q1 * mu) R
  have hq3Upper : q1 * mu < R * (q3 + 1) := by
    have hstrict : q1 * mu < (q3 + 1) * R := by
      rw [← Nat.div_lt_iff_lt_mul hR]
      simp [q3]
    simpa [Nat.mul_comm] using hstrict
  have hq1LtR : q1 < R := by
    apply (Nat.mul_lt_mul_left hb).mp
    exact lt_of_le_of_lt hq1Lower hx
  have hestimateLower : q3 * n ≤ x := by
    have h1 : R * (q3 * n) ≤ R * x := by
      calc
        R * (q3 * n) = (R * q3) * n := by ring
        _ ≤ (q1 * mu) * n := Nat.mul_le_mul_right n hq3Lower
        _ ≤ q1 * (b * R) := by
          calc
            (q1 * mu) * n = q1 * (n * mu) := by ring
            _ ≤ q1 * (b * R) := Nat.mul_le_mul_left q1 hmuLower
        _ = R * (b * q1) := by ring
        _ ≤ R * x := Nat.mul_le_mul_left R hq1Lower
    exact Nat.le_of_mul_le_mul_left h1 hR
  have hq1Scaled : q1 * n < R * n := (Nat.mul_lt_mul_right hn).mpr hq1LtR
  have hqbLt : q1 * b < (q3 + 2) * n := by
    have hscaled : R * (q1 * b) < R * ((q3 + 2) * n) := by
      calc
        R * (q1 * b) = q1 * (b * R) := by ring
        _ ≤ q1 * (n * (mu + 1)) := Nat.mul_le_mul_left q1 hmuUpper
        _ = (q1 * mu) * n + q1 * n := by ring
        _ < (R * (q3 + 1)) * n + R * n := by
          exact Nat.add_lt_add_of_le_of_lt
            (Nat.mul_le_mul_right n hq3Upper.le) hq1Scaled
        _ = R * ((q3 + 2) * n) := by ring
    exact Nat.lt_of_mul_lt_mul_left hscaled
  have hestimateUpper : x < q3 * n + 3 * n := by
    nlinarith
  simpa [barrettApproxQuotient, q1, mu, q3] using
    And.intro hestimateLower hestimateUpper

/-- The source's two conditional correction passes as a pure natural-number function. -/
def barrettCorrectTwice (n candidate : Nat) : Nat :=
  let once := if n ≤ candidate then candidate - n else candidate
  if n ≤ once then once - n else once

/-- Any nonnegative Barrett candidate below `3*n` is reduced exactly by the two deployed
conditional subtractions. -/
theorem barrettCorrectTwice_eq_mod
    (n candidate : Nat) (_hn : 0 < n) (hcandidate : candidate < 3 * n) :
    barrettCorrectTwice n candidate = candidate % n := by
  unfold barrettCorrectTwice
  by_cases hfirst : n ≤ candidate
  · rw [if_pos hfirst]
    have hmodFirst : (candidate - n) % n = candidate % n := by
      have hcongr : candidate - n ≡ candidate [MOD n] :=
        (Nat.sub_modulus_modEq_iff hfirst).2 Nat.ModEq.rfl
      exact hcongr
    by_cases hsecond : n ≤ candidate - n
    · rw [if_pos hsecond]
      have hmodSecond : (candidate - n - n) % n = (candidate - n) % n := by
        have hcongr : candidate - n - n ≡ candidate - n [MOD n] :=
          (Nat.sub_modulus_modEq_iff hsecond).2 Nat.ModEq.rfl
        exact hcongr
      have hfinalLt : candidate - n - n < n := by omega
      calc
        candidate - n - n = (candidate - n - n) % n :=
          (Nat.mod_eq_of_lt hfinalLt).symm
        _ = (candidate - n) % n := hmodSecond
        _ = candidate % n := hmodFirst
    · rw [if_neg hsecond]
      have hfinalLt : candidate - n < n := by omega
      calc
        candidate - n = (candidate - n) % n :=
          (Nat.mod_eq_of_lt hfinalLt).symm
        _ = candidate % n := hmodFirst
  · rw [if_neg hfirst, if_neg (by omega : ¬n ≤ candidate)]
    exact (Nat.mod_eq_of_lt (by omega : candidate < n)).symm

def barrettCandidate (b R n x : Nat) : Nat :=
  x - barrettApproxQuotient b R n x * n

/-- The approximate quotient's ordinary nonnegative candidate is below `3*n` and congruent to
the input modulo the modulus. -/
theorem barrettCandidate_spec
    (b R n x : Nat) (hb : 0 < b) (hR : 0 < R) (hn : 0 < n)
    (hbn : b ≤ n) (hx : x < b * R) :
    barrettCandidate b R n x < 3 * n ∧
      barrettCandidate b R n x % n = x % n := by
  let q3 := barrettApproxQuotient b R n x
  have hbounds := barrettApproxQuotient_bounds b R n x hb hR hn hbn hx
  dsimp only at hbounds
  have hle : q3 * n ≤ x := by simpa [q3] using hbounds.1
  have hlt : x < q3 * n + 3 * n := by simpa [q3] using hbounds.2
  have hcLt : x - q3 * n < 3 * n := by omega
  have hcongr : x - q3 * n ≡ x [MOD n] := by
    have hmultiple : q3 * n ≡ 0 [MOD n] := by
      simp [Nat.ModEq]
    simpa using Nat.ModEq.sub hle (Nat.zero_le x) Nat.ModEq.rfl hmultiple
  simpa [barrettCandidate, q3] using And.intro hcLt hcongr

/-- The complete pure Barrett estimate followed by the source's two correction passes is the
ordinary remainder. -/
theorem barrettCorrectApprox_eq_mod
    (b R n x : Nat) (hb : 0 < b) (hR : 0 < R) (hn : 0 < n)
    (hbn : b ≤ n) (hx : x < b * R) :
    barrettCorrectTwice n (barrettCandidate b R n x) = x % n := by
  have hc := barrettCandidate_spec b R n x hb hR hn hbn hx
  rw [barrettCorrectTwice_eq_mod n _ hn hc.1, hc.2]

def barrettQ3 (k n x : Nat) : Nat :=
  let q1 := x / UInt256.size ^ (k - 1)
  let mu := UInt256.size ^ (2 * k) / n
  q1 * mu / UInt256.size ^ (k + 1)

def deployedBarrettCandidate (k n x : Nat) : Nat := x - barrettQ3 k n x * n

theorem barrettRadix_split (k : Nat) (hk : 0 < k) :
    UInt256.size ^ (k - 1) * UInt256.size ^ (k + 1) =
      UInt256.size ^ (2 * k) := by
  rw [← pow_add]
  congr 1
  omega

/-- The quotient estimate used by the deployed `k`-limb Barrett routine has the abstract bound. -/
theorem barrettQ3_bounds
    (k n x : Nat) (hk : 0 < k) (hn : 0 < n)
    (hnNormalized : UInt256.size ^ (k - 1) ≤ n)
    (hx : x < UInt256.size ^ (2 * k)) :
    barrettQ3 k n x * n ≤ x ∧
      x < barrettQ3 k n x * n + 3 * n := by
  let b := UInt256.size ^ (k - 1)
  let R := UInt256.size ^ (k + 1)
  have hb : 0 < b := Nat.pow_pos (by norm_num [UInt256.size])
  have hR : 0 < R := Nat.pow_pos (by norm_num [UInt256.size])
  have hsplit : b * R = UInt256.size ^ (2 * k) := by
    simpa [b, R] using barrettRadix_split k hk
  have h := barrettApproxQuotient_bounds b R n x hb hR hn
    (by simpa [b] using hnNormalized) (by rw [hsplit]; exact hx)
  simpa [barrettQ3, barrettApproxQuotient, b, R, hsplit] using h

/-- The deployed estimate fits in the `k+1` low limbs consumed by the truncated product. -/
theorem barrettQ3_lt_radix
    (k n x : Nat) (hk : 0 < k)
    (hnNormalized : UInt256.size ^ (k - 1) ≤ n)
    (hx : x < UInt256.size ^ (2 * k)) :
    barrettQ3 k n x < UInt256.size ^ (k + 1) := by
  let b := UInt256.size ^ (k - 1)
  let R := UInt256.size ^ (k + 1)
  have hb : 0 < b := Nat.pow_pos (by norm_num [UInt256.size])
  have hn : 0 < n := lt_of_lt_of_le hb hnNormalized
  have hq := (barrettQ3_bounds k n x hk hn hnNormalized hx).1
  have hsplit : b * R = UInt256.size ^ (2 * k) := by
    simpa [b, R] using barrettRadix_split k hk
  have hscaled : b * barrettQ3 k n x < b * R := by
    calc
      b * barrettQ3 k n x = barrettQ3 k n x * b := Nat.mul_comm _ _
      _ ≤ barrettQ3 k n x * n := Nat.mul_le_mul_left _ hnNormalized
      _ ≤ x := hq
      _ < UInt256.size ^ (2 * k) := hx
      _ = b * R := hsplit.symm
  have := Nat.lt_of_mul_lt_mul_left hscaled
  simpa only [R] using this

/-- Subtracting equal-width radix residues with one added radix recovers the ordinary
nonnegative difference whenever that difference fits in the radix window. -/
theorem wrappedResidueSub_eq_sub
    (R x y : Nat) (hR : 0 < R) (hyx : y ≤ x) (hdiff : x - y < R) :
    (x % R + R - y % R) % R = x - y := by
  have hyMod : y % R ≤ x % R + R := by
    have hyLt : y % R < R := Nat.mod_lt y hR
    omega
  have hleft : x % R + R ≡ x [MOD R] := by
    simp [Nat.ModEq]
  have hright : y % R ≡ y [MOD R] := by
    simp [Nat.ModEq]
  have hsub : x % R + R - y % R ≡ x - y [MOD R] :=
    Nat.ModEq.sub hyMod hyx hleft hright
  unfold Nat.ModEq at hsub
  rw [Nat.mod_eq_of_lt hdiff] at hsub
  exact hsub

/-- The deployed `k+1`-limb wrapped subtraction is exactly the pure Barrett candidate.  The
upper `k`-limb modulus bound is needed here: it is what makes the `< 3*n` estimate fit in the
extra temporary limb. -/
theorem deployedBarrettCandidate_eq_wrappedResidueSub
    (k n x : Nat) (hk : 0 < k) (hn : 0 < n)
    (hnNormalized : UInt256.size ^ (k - 1) ≤ n)
    (hnFits : n < UInt256.size ^ k)
    (hx : x < UInt256.size ^ (2 * k)) :
    (x % UInt256.size ^ (k + 1) + UInt256.size ^ (k + 1) -
        (barrettQ3 k n x * n) % UInt256.size ^ (k + 1)) %
        UInt256.size ^ (k + 1) =
      deployedBarrettCandidate k n x := by
  have hbounds := barrettQ3_bounds k n x hk hn hnNormalized hx
  have hcandidate : deployedBarrettCandidate k n x < 3 * n := by
    unfold deployedBarrettCandidate
    omega
  have hthreeLt : 3 * n < UInt256.size ^ (k + 1) := by
    have hsize : 3 < UInt256.size := by norm_num [UInt256.size]
    calc
      3 * n < 3 * UInt256.size ^ k :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).2 hnFits
      _ < UInt256.size * UInt256.size ^ k :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by norm_num [UInt256.size]))).2 hsize
      _ = UInt256.size ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  exact wrappedResidueSub_eq_sub
    (UInt256.size ^ (k + 1)) x (barrettQ3 k n x * n)
    (Nat.pow_pos (by norm_num [UInt256.size])) hbounds.1
    (lt_trans hcandidate hthreeLt)

/-- After the source's at-most-two corrections, the deployed radix-power estimate is exactly the
ordinary remainder. -/
theorem deployedBarrettCorrect_eq_mod
    (k n x : Nat) (hk : 0 < k) (hn : 0 < n)
    (hnNormalized : UInt256.size ^ (k - 1) ≤ n)
    (hx : x < UInt256.size ^ (2 * k)) :
    barrettCorrectTwice n (deployedBarrettCandidate k n x) = x % n := by
  let b := UInt256.size ^ (k - 1)
  let R := UInt256.size ^ (k + 1)
  have hb : 0 < b := Nat.pow_pos (by norm_num [UInt256.size])
  have hR : 0 < R := Nat.pow_pos (by norm_num [UInt256.size])
  have hsplit : b * R = UInt256.size ^ (2 * k) := by
    simpa [b, R] using barrettRadix_split k hk
  have h := barrettCorrectApprox_eq_mod b R n x hb hR hn
    (by simpa [b] using hnNormalized) (by rw [hsplit]; exact hx)
  simpa [deployedBarrettCandidate, barrettQ3, barrettCandidate,
    barrettApproxQuotient, b, R, hsplit] using h

/-- End-to-end pure Barrett result from its concrete modular-multiplication contract. -/
theorem barrettScan_eq_model
    {A : Type} (repr : A → Nat) (mul : A → A → A) (base one : A)
    (baseNat modulus : Nat) (hmod : 1 < modulus)
    (hrawMul : ∀ x y, repr (mul x y) = (repr x * repr y) % modulus)
    (hrawBase : repr base = baseNat % modulus)
    (hrawOne : repr one = 1)
    (bits : List Bool) :
    repr (msbPowScan mul base { value := one, exponent := 0 } bits).value =
      Model.modPow baseNat
        (msbPowScan mul base { value := one, exponent := 0 } bits).exponent modulus := by
  have hscan := msbPowScan_eq_model repr mul base one modulus hmod hrawMul hrawOne bits
  rw [hrawBase, model_modPow_mod_base hmod] at hscan
  exact hscan

end Modexp
