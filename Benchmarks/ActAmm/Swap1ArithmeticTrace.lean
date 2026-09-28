import Benchmarks.ActAmm.Swap1Balance1Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_inputGuardOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3400⟩
      [q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hgt : (solcSlotWord acc.2 I ⟨6⟩).toNat < q1.toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3467⟩
      [q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have rd1589 := evm_run rd with [push1 ⟨6⟩]
  obtain ⟨_, _, rd1590⟩ := rd1589.sload
    (by native_decide) (by evm_ov)
  have hgt' : UInt256.gt q1 (solcSlotWord acc.2 I ⟨6⟩) = ⟨1⟩ :=
    ugt_one hgt
  exact ⟨_, _, evm_run rd1590 with [
    dup2, gt, push2 ⟨3467⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]⟩

theorem ammSwap1X_amount1In
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3467⟩
      [q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hgt : (solcSlotWord acc.2 I ⟨6⟩).toNat < q1.toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3485⟩
      [UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have rd1658 := evm_run rd with [jumpdest, push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1659⟩ := rd1658.sload
    (by native_decide) (by evm_ov)
  have rd6645 := evm_run rd1659 with [
    dup3, push2 ⟨3482⟩, swap2, swap1,
    push2 ⟨6645⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1669⟩ := RD.ammCheckedSubOk rd6645
    (by simpa [solcSlotWord, codeOwnerStorageWord]
      using Nat.le_of_lt hgt) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd1669 with [jumpdest, swap1, pop]⟩

theorem ammSwap1X_denominator
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3485⟩
      [UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hfit : (solcSlotWord acc.2 I ⟨6⟩).toNat +
      (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)).toNat < UInt256.size) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3498⟩
      [(solcSlotWord acc.2 I ⟨6⟩) +
          UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have rd1675 := evm_run rd with [dup1, push1 ⟨6⟩]
  obtain ⟨_, _, rd1676⟩ := rd1675.sload
    (by native_decide) (by evm_ov)
  have rd6696 := evm_run rd1676 with [
    push2 ⟨3498⟩, swap2, swap1,
    push2 ⟨6696⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1685⟩ := RD.ammCheckedAddOk rd6696
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hfit)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using rd1685⟩

theorem ammSwap1X_numerator
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3498⟩
      [(solcSlotWord acc.2 I ⟨6⟩) +
          UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hfit : (solcSlotWord acc.2 I ⟨5⟩).toNat *
      (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)).toNat < UInt256.size) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3512⟩
      [UInt256.mul (solcSlotWord acc.2 I ⟨5⟩)
          (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)),
        (solcSlotWord acc.2 I ⟨6⟩) +
          UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have rd1689 := evm_run rd with [jumpdest, dup2, push1 ⟨5⟩]
  obtain ⟨_, _, rd1690⟩ := rd1689.sload
    (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd1690 with [
    push2 ⟨3512⟩, swap2, swap1,
    push2 ⟨6747⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1699⟩ := RD.ammCheckedMulOk rd6747
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hfit)
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa only [solcSlotWord, codeOwnerStorageWord] using rd1699⟩

theorem ammSwap1X_numeratorOverflow
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3498⟩
      [(solcSlotWord acc.2 I ⟨6⟩) +
          UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hover : UInt256.size ≤ (solcSlotWord acc.2 I ⟨5⟩).toNat *
      (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1689 := evm_run rd with [jumpdest, dup2, push1 ⟨5⟩]
  obtain ⟨_, _, rd1690⟩ := rd1689.sload
    (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd1690 with [
    push2 ⟨3512⟩, swap2, swap1,
    push2 ⟨6747⟩, jump (by jump_dest)]
  exact RD.ammCheckedMulOverflowWide rd6747
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hover)
    haw (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammSwap1X_kQuotient
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3512⟩
      [UInt256.mul (solcSlotWord acc.2 I ⟨5⟩)
          (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)),
        (solcSlotWord acc.2 I ⟨6⟩) +
          UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hdenom : (solcSlotWord acc.2 I ⟨6⟩) +
      UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩) ≠ ⟨0⟩) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3522⟩
      [UInt256.div
          (UInt256.mul (solcSlotWord acc.2 I ⟨5⟩)
            (UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)))
          ((solcSlotWord acc.2 I ⟨6⟩) +
            UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩)),
        UInt256.sub q1 (solcSlotWord acc.2 I ⟨6⟩),
        q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have rd6857 := evm_run rd with [
    jumpdest, push2 ⟨3522⟩, swap2, swap1,
    push2 ⟨6857⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1709⟩ := RD.ammCheckedDivOk rd6857
    hdenom (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd1709⟩

theorem ammSwap1X_kGuardOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn quotient : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3522⟩
      [quotient, amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hle : (ammSwap1AmountWord I).toNat ≤ quotient.toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3588⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k' C' := by
  have hgt : UInt256.gt (ammSwap1AmountWord I) quotient = ⟨0⟩ :=
    ugt_zero hle
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup6, gt, iszero, push2 ⟨3588⟩,
    jumpiT (by rw [hgt]; decide) (by jump_dest)]⟩

theorem ammSwap1X_reserve0Stored
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3588⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3596⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ q0) k' C' := by
  have rd1780 := evm_run rd with [
    jumpdest, dup3, push1 ⟨5⟩, dup2, swap1]
  obtain ⟨_, _, rd1781⟩ := rd1780.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1781 with [pop]⟩

theorem ammSwap1X_reserve1Stored
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3596⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3603⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ q1) k' C' := by
  have rd1788 := evm_run rd with [dup2, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1789⟩ := rd1788.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1789 with [pop]⟩

theorem ammSwap1X_swapStop
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3603⟩
      [amountIn, q1, q0,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C) :
    RDret ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I)
      acc ByteArray.empty := by
  have rd235 := evm_run rd with [
    pop, pop, pop, pop, pop, jump (by jump_dest), jumpdest]
  exact rd235.stop (by native_decide) (by evm_ov)


theorem ammSwap1Quotient_toNat (r1 r0 q1 : UInt256)
    (hle : r1.toNat ≤ q1.toNat)
    (haddFit : r1.toNat + (UInt256.sub q1 r1).toNat < UInt256.size)
    (hmulFit : r0.toNat * (UInt256.sub q1 r1).toNat < UInt256.size) :
    (UInt256.div (UInt256.mul r0 (UInt256.sub q1 r1))
      (r1 + UInt256.sub q1 r1)).toNat =
      (r0.toNat * (q1.toNat - r1.toNat)) /
        (r1.toNat + (q1.toNat - r1.toNat)) := by
  rw [udiv_toNat, u256_mul_toNat,
    Nat.mod_eq_of_lt hmulFit, uadd_toNat,
    Nat.mod_eq_of_lt haddFit, usub_toNat hle]

end Benchmarks.ActAmm
