import Benchmarks.ActAmm4.SwapDecodeTrace
import Benchmarks.ActAmm4.MintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_outputGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2111⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2187⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  by_cases h0 : 0 < (amm4SwapAmount0Word I).toNat
  · have hgt : UInt256.gt (amm4SwapAmount0Word I) ⟨0⟩ = ⟨1⟩ :=
      ugt_one (by simpa using h0)
    have rd2124 := evm_run rd with [
      jumpdest, push0, dup4, gt, dup1, push2 ⟨2124⟩,
      jumpiT (by rw [hgt]; decide) (by jump_dest)]
    have rd2124' := rd2124
    rw [hgt] at rd2124'
    exact ⟨_, _, evm_run rd2124' with [
      jumpdest, push2 ⟨2187⟩, jumpiT (by decide) (by jump_dest)]⟩
  · have h1 : 0 < (amm4SwapAmount1Word I).toNat := hpos.resolve_left h0
    have hgt0 : UInt256.gt (amm4SwapAmount0Word I) ⟨0⟩ = ⟨0⟩ :=
      ugt_zero (by simpa using Nat.eq_zero_of_not_pos h0)
    have hgt1 : UInt256.gt (amm4SwapAmount1Word I) ⟨0⟩ = ⟨1⟩ :=
      ugt_one (by simpa using h1)
    have rd2124 := evm_run rd with [
      jumpdest, push0, dup4, gt, dup1, push2 ⟨2124⟩,
      jumpiNT (by rw [hgt0]), pop, push0, dup3, gt]
    have rd2124' := rd2124
    rw [hgt1] at rd2124'
    exact ⟨_, _, evm_run rd2124' with [
      jumpdest, push2 ⟨2187⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem amm4SwapX_liquidityGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2187⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hliq0 : (amm4SwapAmount0Word I).toNat < (solcSlotWord σ I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat < (solcSlotWord σ I ⟨6⟩).toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2268⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2190 := evm_run rd with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd2191⟩ := rd2190.sload (by native_decide) (by evm_ov)
  have hlt0 : UInt256.lt (amm4SwapAmount0Word I) (solcSlotWord σ I ⟨5⟩) = ⟨1⟩ :=
    ult_one hliq0
  have rd2198 := evm_run rd2191 with [
    dup4, lt, dup1, iszero, push2 ⟨2205⟩,
    jumpiNT (by rw [hlt0]; decide)]
  have rd2202 := evm_run rd2198 with [pop, push1 ⟨6⟩]
  obtain ⟨_, _, rd2203⟩ := rd2202.sload (by native_decide) (by evm_ov)
  have hlt1 : UInt256.lt (amm4SwapAmount1Word I) (solcSlotWord σ I ⟨6⟩) = ⟨1⟩ :=
    ult_one hliq1
  have rd2205 := evm_run rd2203 with [dup3, lt]
  have rd2205' := rd2205
  rw [hlt1] at rd2205'
  exact ⟨_, _, evm_run rd2205' with [
    jumpdest, push2 ⟨2268⟩, jumpiT (by decide) (by jump_dest)]⟩

theorem amm4SwapX_token0Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2268⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2325⟩
      [amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd2273 := evm_run rd with [
    jumpdest, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd2274⟩ := rd2273.sload
    (by native_decide) (by evm_ov)
  have rd2325 := evm_run rd2274 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken0Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd2325⟩

theorem amm4SwapX_token0Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2325⟩
      [amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hne : amm4SwapToWord I ≠ amm4MintToken0Word σ I) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2357⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (amm4SwapToWord I) solcAddrMask =
      amm4SwapToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (amm4SwapToWord I)
      (amm4MintToken0Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd2348 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd2348' := rd2348
  rw [u256_land_comm solcAddrMask (amm4SwapToWord I), hclean]
    at rd2348'
  have rd2350 := evm_run rd2348' with [eq, iszero]
  have rd2350' := rd2350
  rw [heq] at rd2350'
  have rd2355 := evm_run rd2350' with [
    dup1, iszero, push2 ⟨2438⟩, jumpiNT (by decide)]
  exact ⟨_, _, evm_run rd2355 with [pop]⟩

theorem amm4SwapX_token1Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2357⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2413⟩
      [amm4MintToken1Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd2361 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd2362⟩ := rd2361.sload
    (by native_decide) (by evm_ov)
  have rd2413 := evm_run rd2362 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken1Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd2413⟩

theorem amm4SwapX_token1Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2413⟩
      [amm4MintToken1Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hne : amm4SwapToWord I ≠ amm4MintToken1Word σ I) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2501⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (amm4SwapToWord I) solcAddrMask =
      amm4SwapToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (amm4SwapToWord I)
      (amm4MintToken1Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd2436 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd2436' := rd2436
  rw [u256_land_comm solcAddrMask (amm4SwapToWord I), hclean]
    at rd2436'
  have rd2438 := evm_run rd2436' with [eq, iszero]
  have rd2438' := rd2438
  rw [heq] at rd2438'
  exact ⟨_, _, evm_run rd2438' with [
    jumpdest, push2 ⟨2501⟩,
    jumpiT (by decide) (by jump_dest)]⟩

end Benchmarks.ActAmm4
