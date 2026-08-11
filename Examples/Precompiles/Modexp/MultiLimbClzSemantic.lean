import Examples.Precompiles.Modexp.MultiLimbClzSemantic2
import Examples.Precompiles.Modexp.MultiLimbClzExecutable

/-!
# Leading-zero helper semantics

This module keeps the pure arithmetic proof separate from the exact execution contract.  The
separation prevents normalization of the staged leading-zero model from inflating the kernel term
for every module that only needs `_clz` execution and exact gas.
-/

open Ethereum
namespace Modexp.MultiLimbClz

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def clzFinalStage (x : UInt256) : StageResult :=
  let pre := clzPreFinal x
  stage1 pre.x pre.n

def normalizedTop (x : UInt256) : UInt256 :=
  let pre := clzPreFinal x
  if pre.x.toNat < 2 ^ 255 then pre.x.shiftLeft ⟨1⟩ else pre.x

theorem clzResult_n_eq_stage1 (x : UInt256) :
    (clzResult x).n = (clzFinalStage x).n := by
  unfold clzResult clzFinalStage clzPreFinal through1
  dsimp only

theorem clzResult_n_le (x : UInt256) : (clzResult x).n ≤ 255 := by
  have hpre := clzPreFinal_n_le x
  have hlast := stage1_n_le (x := (clzPreFinal x).x) hpre
  rw [clzResult_n_eq_stage1]
  simpa only [clzFinalStage] using hlast

theorem clzPreFinal_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 254 ≤ (clzPreFinal x).x.toNat := by
  simpa only [clzPreFinal] using through2_lower hx

theorem clzPreFinal_relation (x : UInt256) :
    (clzPreFinal x).x.toNat = x.toNat * 2 ^ (clzPreFinal x).n := by
  simpa only [clzPreFinal] using through2_relation x

theorem normalizedTop_relation (x : UInt256) :
    (normalizedTop x).toNat = x.toNat * 2 ^ (clzResult x).n := by
  rw [clzResult_n_eq_stage1]
  unfold clzFinalStage
  dsimp only
  have hrel := clzPreFinal_relation x
  unfold normalizedTop
  dsimp only
  by_cases hlt : (clzPreFinal x).x.toNat < 2 ^ 255
  · rw [if_pos hlt, shiftLeft1_toNat_exact hlt]
    unfold stage1
    rw [if_pos hlt]
    dsimp only
    rw [hrel, Nat.pow_add]
    simp only [pow_one, Nat.mul_assoc]
  · rw [if_neg hlt]
    unfold stage1
    rw [if_neg hlt]
    dsimp only
    exact hrel

theorem normalizedTop_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 255 ≤ (normalizedTop x).toNat := by
  have hpre := clzPreFinal_lower hx
  unfold normalizedTop
  dsimp only
  by_cases hlt : (clzPreFinal x).x.toNat < 2 ^ 255
  · rw [if_pos hlt, shiftLeft1_toNat_exact hlt]
    norm_num
    omega
  · rw [if_neg hlt]
    omega

theorem normalizedTop_upper (x : UInt256) :
    (normalizedTop x).toNat < 2 ^ 256 := by
  exact (normalizedTop x).val.isLt

/-- The staged pure model returns the mathematical leading-zero count of a nonzero word. -/
theorem clzResult_eq_leadingZeros {x : UInt256} (hx : x.toNat ≠ 0) :
    (clzResult x).n = 255 - Nat.log2 x.toNat := by
  let n := (clzResult x).n
  have hn : n ≤ 255 := clzResult_n_le x
  have hrel : (normalizedTop x).toNat = x.toNat * 2 ^ n := normalizedTop_relation x
  have hlo : 2 ^ 255 ≤ x.toNat * 2 ^ n := by
    rw [← hrel]
    exact normalizedTop_lower hx
  have hhi : x.toNat * 2 ^ n < 2 ^ 256 := by
    rw [← hrel]
    exact normalizedTop_upper x
  have hloPow : 2 ^ (255 - n) ≤ x.toNat := by
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ n) _ (by positivity)
    rw [← Nat.pow_add, Nat.sub_add_cancel hn]
    exact hlo
  have hhiPow : x.toNat < 2 ^ (256 - n) := by
    have hn256 : n ≤ 256 := hn.trans (by decide)
    apply Nat.lt_of_mul_lt_mul_right
    rw [← Nat.pow_add, Nat.sub_add_cancel hn256]
    exact hhi
  have hlog : Nat.log2 x.toNat = 255 - n := by
    apply (Nat.log2_eq_iff hx).2
    refine ⟨hloPow, ?_⟩
    have hsubSucc : 255 - n + 1 = 256 - n := by
      simpa only [Nat.succ_eq_add_one] using (Nat.succ_sub hn).symm
    rw [hsubSucc]
    exact hhiPow
  change n = 255 - Nat.log2 x.toNat
  rw [hlog, Nat.sub_sub_self hn]

end Modexp.MultiLimbClz
