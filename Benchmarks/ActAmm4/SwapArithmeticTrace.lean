import Benchmarks.ActAmm4.SwapBalance1Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_reserve0AfterOut
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3128⟩
      [v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : q0.toNat ≤ (solcSlotWord acc.2 I ⟨5⟩).toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3142⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0,
        ⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd3132 := evm_run rd with [push0, dup6, push1 ⟨5⟩]
  obtain ⟨_, _, rd3133⟩ := rd3132.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3133 with [
    push2 ⟨3142⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3142⟩ := RD.amm4CheckedSubOk rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hle)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using rd3142⟩

theorem amm4SwapX_amount0InPositiveBranch
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3142⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0,
        ⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hgt : (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0).toNat <
      v0.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3154⟩
      [⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have hgt' : UInt256.gt v0
      (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0) = ⟨1⟩ :=
    ugt_one hgt
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup4, gt, push2 ⟨3154⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]⟩

theorem amm4SwapX_amount0InPositive
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3154⟩
      [⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : q0.toNat ≤ (solcSlotWord acc.2 I ⟨5⟩).toNat)
    (hgt : (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0).toNat <
      v0.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3183⟩
      [UInt256.sub v0 (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0),
        v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd3158 := evm_run rd with [jumpdest, dup6, push1 ⟨5⟩]
  obtain ⟨_, _, rd3159⟩ := rd3158.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3159 with [
    push2 ⟨3168⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3168⟩ := RD.amm4CheckedSubOk rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hle)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5253' := evm_run rd3168 with [
    jumpdest, dup4, push2 ⟨3179⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3179⟩ := RD.amm4CheckedSubOk rd5253'
    (by simpa [solcSlotWord, codeOwnerStorageWord]
      using Nat.le_of_lt hgt)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using
      (evm_run rd3179 with [jumpdest, jumpdest, swap1, pop])⟩

theorem amm4SwapX_amount0InZero
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3142⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0,
        ⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : v0.toNat ≤
      (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0).toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3183⟩
      [⟨0⟩, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have hgt : UInt256.gt v0
      (UInt256.sub (solcSlotWord acc.2 I ⟨5⟩) q0) = ⟨0⟩ :=
    ugt_zero hle
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup4, gt, push2 ⟨3154⟩,
    jumpiNT (by rw [hgt]), push0,
    push2 ⟨3180⟩, jump (by jump_dest), jumpdest,
    swap1, pop]⟩

theorem amm4SwapX_reserve1AfterOut
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3183⟩
      [amount0In, v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : q1.toNat ≤ (solcSlotWord acc.2 I ⟨6⟩).toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3197⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1,
        ⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd3187 := evm_run rd with [push0, dup6, push1 ⟨6⟩]
  obtain ⟨_, _, rd3188⟩ := rd3187.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3188 with [
    push2 ⟨3197⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3197⟩ := RD.amm4CheckedSubOk rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hle)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using rd3197⟩

theorem amm4SwapX_amount1InPositiveBranch
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3197⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1,
        ⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k C)
    (hgt : (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1).toNat <
      v1.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3209⟩
      [⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have hgt' : UInt256.gt v1
      (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1) = ⟨1⟩ :=
    ugt_one hgt
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup4, gt, push2 ⟨3209⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]⟩

theorem amm4SwapX_amount1InPositive
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3209⟩
      [⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : q1.toNat ≤ (solcSlotWord acc.2 I ⟨6⟩).toNat)
    (hgt : (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1).toNat <
      v1.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3238⟩
      [UInt256.sub v1 (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1),
        amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd3213 := evm_run rd with [jumpdest, dup6, push1 ⟨6⟩]
  obtain ⟨_, _, rd3214⟩ := rd3213.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3214 with [
    push2 ⟨3223⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3223⟩ := RD.amm4CheckedSubOk rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hle)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5253' := evm_run rd3223 with [
    jumpdest, dup4, push2 ⟨3234⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3234⟩ := RD.amm4CheckedSubOk rd5253'
    (by simpa [solcSlotWord, codeOwnerStorageWord]
      using Nat.le_of_lt hgt)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using
      (evm_run rd3234 with [jumpdest, jumpdest, swap1, pop])⟩

theorem amm4SwapX_amount1InZero
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3197⟩
      [UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1,
        ⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : v1.toNat ≤
      (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1).toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3238⟩
      [⟨0⟩, amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have hgt : UInt256.gt v1
      (UInt256.sub (solcSlotWord acc.2 I ⟨6⟩) q1) = ⟨0⟩ :=
    ugt_zero hle
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup4, gt, push2 ⟨3209⟩,
    jumpiNT (by rw [hgt]), push0,
    push2 ⟨3235⟩, jump (by jump_dest), jumpdest,
    swap1, pop]⟩

theorem amm4SwapX_inputGuardOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3238⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hpos : 0 < amount0In.toNat ∨ 0 < amount1In.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3313⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  by_cases h0 : 0 < amount0In.toNat
  · have hgt : UInt256.gt amount0In ⟨0⟩ = ⟨1⟩ :=
      ugt_one (by simpa using h0)
    have rd3250 := evm_run rd with [
      push0, dup3, gt, dup1, push2 ⟨3250⟩,
      jumpiT (by rw [hgt]; decide) (by jump_dest)]
    have rd3250' := rd3250
    rw [hgt] at rd3250'
    exact ⟨_, _, evm_run rd3250' with [
      jumpdest, push2 ⟨3313⟩,
      jumpiT (by decide) (by jump_dest)]⟩

  · have h1 : 0 < amount1In.toNat := hpos.resolve_left h0
    have hgt0 : UInt256.gt amount0In ⟨0⟩ = ⟨0⟩ :=
      ugt_zero (by simpa using Nat.eq_zero_of_not_pos h0)
    have hgt1 : UInt256.gt amount1In ⟨0⟩ = ⟨1⟩ :=
      ugt_one (by simpa using h1)
    have rd3250 := evm_run rd with [
      push0, dup3, gt, dup1, push2 ⟨3250⟩,
      jumpiNT (by rw [hgt0]), pop, push0, dup2, gt]
    have rd3250' := rd3250
    rw [hgt1] at rd3250'
    exact ⟨_, _, evm_run rd3250' with [
      jumpdest, push2 ⟨3313⟩,
      jumpiT (by decide) (by jump_dest)]⟩


theorem amm4SwapX_oldProduct
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3313⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hfit : (solcSlotWord acc.2 I ⟨5⟩).toNat *
      (solcSlotWord acc.2 I ⟨6⟩).toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3329⟩
      [UInt256.mul (solcSlotWord acc.2 I ⟨5⟩)
        (solcSlotWord acc.2 I ⟨6⟩),
        amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd3316 := evm_run rd with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, rd3317⟩ := rd3316.sload (by native_decide) (by evm_ov)
  have rd3319 := evm_run rd3317 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd3320⟩ := rd3319.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3320 with [
    push2 ⟨3329⟩, swap2, swap1,
    push2 ⟨5458⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3329⟩ := RD.amm4CheckedMulOk rd5458
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hfit)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using rd3329⟩

theorem amm4SwapX_newProduct
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In oldProduct : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3329⟩
      [oldProduct, amount1In, amount0In, v1, v0,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hfit : v0.toNat * v1.toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3341⟩
      [UInt256.mul v0 v1, oldProduct, amount1In, amount0In,
        v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have rd5458 := evm_run rd with [
    jumpdest, dup4, dup6, push2 ⟨3341⟩, swap2, swap1,
    push2 ⟨5458⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3341⟩ := RD.amm4CheckedMulOk rd5458
    hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd3341⟩

theorem amm4SwapX_kGuardOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In oldProduct newProduct : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3341⟩
      [newProduct, oldProduct, amount1In, amount0In,
        v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hle : oldProduct.toNat ≤ newProduct.toNat) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3406⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k' C' := by
  have hlt : UInt256.lt newProduct oldProduct = ⟨0⟩ :=
    ult_zero hle
  exact ⟨_, _, evm_run rd with [
    jumpdest, lt, iszero, push2 ⟨3406⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest)]⟩

theorem amm4SwapX_reserve0Stored
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3406⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3414⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ v0) k' C' := by
  have rd3412 := evm_run rd with [
    jumpdest, dup4, push1 ⟨5⟩, dup2, swap1]
  obtain ⟨_, _, rd3413⟩ := rd3412.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3413 with [pop]⟩

theorem amm4SwapX_reserve1Stored
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3414⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3421⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ v1) k' C' := by
  have rd3419 := evm_run rd with [dup3, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd3420⟩ := rd3419.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3420 with [pop]⟩

theorem amm4SwapX_swapStop
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In amount1In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3421⟩
      [amount1In, amount0In, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C) :
    RDret amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I)
      acc ByteArray.empty := by
  have rd349 := evm_run rd with [
    pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd349.stop (by native_decide) (by evm_ov)

end Benchmarks.ActAmm4
