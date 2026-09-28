import Benchmarks.ActAmm.Swap1DecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_amountPositive
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2563⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hpos : 0 < (ammSwap1AmountWord I).toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2629⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hgt : UInt256.gt (ammSwap1AmountWord I) ⟨0⟩ = ⟨1⟩ := by
    apply ugt_one
    simpa using hpos
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup3, gt, push2 ⟨2629⟩,
    jumpiT (by rw [hgt]; decide) (by jump_dest)]⟩

theorem ammSwap1X_liquidityAvailable
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2629⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ I ⟨5⟩).toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2697⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd819 := evm_run rd with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd820⟩ := rd819.sload (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (ammSwap1AmountWord I)
      (solcSlotWord σ I ⟨5⟩) = ⟨1⟩ := ult_one hliq
  exact ⟨_, _, evm_run rd820 with [
    dup3, lt, push2 ⟨2697⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest)]⟩

theorem ammSwap1X_token0Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2697⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2754⟩
      [ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd889 := evm_run rd with [
    jumpdest, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd890⟩ := rd889.sload
    (by native_decide) (by evm_ov)
  have rd941 := evm_run rd890 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd941⟩

theorem ammSwap1X_token0Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2754⟩
      [ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hne : ammSwap1ToWord I ≠ ammMintToken0Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2786⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap1ToWord I) solcAddrMask =
      ammSwap1ToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (ammSwap1ToWord I)
      (ammMintToken0Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd964 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd964' := rd964
  rw [u256_land_comm solcAddrMask (ammSwap1ToWord I), hclean]
    at rd964'
  have rd966 := evm_run rd964' with [eq, iszero]
  have rd966' := rd966
  rw [heq] at rd966'
  have rd971 := evm_run rd966' with [
    dup1, iszero, push2 ⟨2867⟩, jumpiNT (by decide)]
  exact ⟨_, _, evm_run rd971 with [pop]⟩

theorem ammSwap1X_token1Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2786⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2842⟩
      [ammMintToken1Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd977 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd978⟩ := rd977.sload
    (by native_decide) (by evm_ov)
  have rd1029 := evm_run rd978 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken1Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd1029⟩

theorem ammSwap1X_token1Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2842⟩
      [ammMintToken1Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hne : ammSwap1ToWord I ≠ ammMintToken1Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2930⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap1ToWord I) solcAddrMask =
      ammSwap1ToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (ammSwap1ToWord I)
      (ammMintToken1Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd1052 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd1052' := rd1052
  rw [u256_land_comm solcAddrMask (ammSwap1ToWord I), hclean]
    at rd1052'
  have rd1054 := evm_run rd1052' with [eq, iszero]
  have rd1054' := rd1054
  rw [heq] at rd1054'
  exact ⟨_, _, evm_run rd1054' with [
    jumpdest, push2 ⟨2930⟩,
    jumpiT (by decide) (by jump_dest)]⟩

theorem ammSwap1X_token0Equal
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2754⟩
      [ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (heq : ammSwap1ToWord I = ammMintToken0Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2872⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap1ToWord I) solcAddrMask =
      ammSwap1ToWord I := solcAddrMask_clean hcanon
  have hword : UInt256.eq (ammSwap1ToWord I)
      (ammMintToken0Word σ I) = ⟨1⟩ := by
    rw [heq]
    exact uInt256_eq_self _
  have rd964 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd964' := rd964
  rw [u256_land_comm solcAddrMask (ammSwap1ToWord I), hclean]
    at rd964'
  have rd966 := evm_run rd964' with [eq, iszero]
  have rd966' := rd966
  rw [hword] at rd966'
  have rd1054 := evm_run rd966' with [
    dup1, iszero, push2 ⟨2867⟩,
    jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd1054 with [
    jumpdest, push2 ⟨2930⟩, jumpiNT (by decide)]⟩

theorem ammSwap1X_token1Equal
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2842⟩
      [ammMintToken1Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (heq : ammSwap1ToWord I = ammMintToken1Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2872⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap1ToWord I) solcAddrMask =
      ammSwap1ToWord I := solcAddrMask_clean hcanon
  have hword : UInt256.eq (ammSwap1ToWord I)
      (ammMintToken1Word σ I) = ⟨1⟩ := by
    rw [heq]
    exact uInt256_eq_self _
  have rd1052 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd1052' := rd1052
  rw [u256_land_comm solcAddrMask (ammSwap1ToWord I), hclean]
    at rd1052'
  have rd1054 := evm_run rd1052' with [eq, iszero]
  have rd1054' := rd1054
  rw [hword] at rd1054'
  exact ⟨_, _, evm_run rd1054' with [
    jumpdest, push2 ⟨2930⟩, jumpiNT (by decide)]⟩

end Benchmarks.ActAmm
