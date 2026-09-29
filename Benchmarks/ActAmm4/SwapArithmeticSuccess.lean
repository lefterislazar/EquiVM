import Benchmarks.ActAmm4.SwapArithmeticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 10000000 in
theorem amm4SwapX_successFromBalances
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 a0 a1 : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3128⟩
      [v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true)
    (hle0 : q0.toNat ≤ (solcSlotWord σ I ⟨5⟩).toNat)
    (hle1 : q1.toNat ≤ (solcSlotWord σ I ⟨6⟩).toNat)
    (hcase0 :
      ((UInt256.sub (solcSlotWord σ I ⟨5⟩) q0).toNat < v0.toNat ∧
        a0 = UInt256.sub v0 (UInt256.sub (solcSlotWord σ I ⟨5⟩) q0)) ∨
      (v0.toNat ≤ (UInt256.sub (solcSlotWord σ I ⟨5⟩) q0).toNat ∧ a0 = ⟨0⟩))
    (hcase1 :
      ((UInt256.sub (solcSlotWord σ I ⟨6⟩) q1).toNat < v1.toNat ∧
        a1 = UInt256.sub v1 (UInt256.sub (solcSlotWord σ I ⟨6⟩) q1)) ∨
      (v1.toNat ≤ (UInt256.sub (solcSlotWord σ I ⟨6⟩) q1).toNat ∧ a1 = ⟨0⟩))
    (hpos : 0 < a0.toNat ∨ 0 < a1.toNat)
    (hfitOld : (solcSlotWord σ I ⟨5⟩).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat < UInt256.size)
    (hfitNew : v0.toNat * v1.toNat < UInt256.size)
    (hk : (solcSlotWord σ I ⟨5⟩).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat ≤ v0.toNat * v1.toNat) :
    RDret amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨5⟩ v0) ⟨6⟩ v1)
      ByteArray.empty := by
  obtain ⟨_, _, rd3142⟩ := amm4SwapX_reserve0AfterOut rd hle0
  have rd3183 : ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3183⟩
      [a0, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret (cA, σ) k' C' := by
    rcases hcase0 with ⟨hgt, rfl⟩ | ⟨hle, rfl⟩
    · obtain ⟨_, _, rd3154⟩ :=
        amm4SwapX_amount0InPositiveBranch rd3142 hgt
      exact amm4SwapX_amount0InPositive rd3154 hle0 hgt
    · exact amm4SwapX_amount0InZero rd3142 hle
  obtain ⟨_, _, rd3183⟩ := rd3183
  obtain ⟨_, _, rd3197⟩ := amm4SwapX_reserve1AfterOut rd3183 hle1
  have rd3238 : ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3238⟩
      [a1, a0, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret (cA, σ) k' C' := by
    rcases hcase1 with ⟨hgt, rfl⟩ | ⟨hle, rfl⟩
    · obtain ⟨_, _, rd3209⟩ :=
        amm4SwapX_amount1InPositiveBranch rd3197 hgt
      exact amm4SwapX_amount1InPositive rd3209 hle1 hgt
    · exact amm4SwapX_amount1InZero rd3197 hle
  obtain ⟨_, _, rd3238⟩ := rd3238
  obtain ⟨_, _, rd3313⟩ := amm4SwapX_inputGuardOk rd3238 hpos
  obtain ⟨_, _, rd3329⟩ := amm4SwapX_oldProduct rd3313 hfitOld
  obtain ⟨_, _, rd3341⟩ := amm4SwapX_newProduct rd3329 hfitNew
  have hprodOld : (UInt256.mul (solcSlotWord σ I ⟨5⟩)
      (solcSlotWord σ I ⟨6⟩)).toNat =
      (solcSlotWord σ I ⟨5⟩).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt hfitOld]
  have hprodNew : (UInt256.mul v0 v1).toNat =
      v0.toNat * v1.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt hfitNew]
  obtain ⟨_, _, rd3406⟩ := amm4SwapX_kGuardOk rd3341
    (by rw [hprodOld, hprodNew]; exact hk)
  obtain ⟨_, _, rd3414⟩ := amm4SwapX_reserve0Stored rd3406 hperm
  obtain ⟨_, _, rd3421⟩ := amm4SwapX_reserve1Stored rd3414 hperm
  exact amm4SwapX_swapStop rd3421

end Benchmarks.ActAmm4
