import Benchmarks.ActAmm.Swap0DecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0X_amountPositive
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨750⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hpos : 0 < (ammSwap0AmountWord I).toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hgt : UInt256.gt (ammSwap0AmountWord I) ⟨0⟩ = ⟨1⟩ := by
    apply ugt_one
    simpa using hpos
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup3, gt, push2 ⟨816⟩,
    jumpiT (by rw [hgt]; decide) (by jump_dest)]⟩

theorem ammSwap0X_liquidityAvailable
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq : (ammSwap0AmountWord I).toNat <
      (solcSlotWord σ I ⟨6⟩).toNat) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨884⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd819 := evm_run rd with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, rd820⟩ := rd819.sload (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (ammSwap0AmountWord I)
      (solcSlotWord σ I ⟨6⟩) = ⟨1⟩ := ult_one hliq
  exact ⟨_, _, evm_run rd820 with [
    dup3, lt, push2 ⟨884⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest)]⟩

theorem ammSwap0X_token0Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨884⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨941⟩
      [ammMintToken0Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
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

theorem ammSwap0X_token0Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨941⟩
      [ammMintToken0Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hne : ammSwap0ToWord I ≠ ammMintToken0Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨973⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap0ToWord I) solcAddrMask =
      ammSwap0ToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (ammSwap0ToWord I)
      (ammMintToken0Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd964 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd964' := rd964
  rw [u256_land_comm solcAddrMask (ammSwap0ToWord I), hclean]
    at rd964'
  have rd966 := evm_run rd964' with [eq, iszero]
  have rd966' := rd966
  rw [heq] at rd966'
  have rd971 := evm_run rd966' with [
    dup1, iszero, push2 ⟨1054⟩, jumpiNT (by decide)]
  exact ⟨_, _, evm_run rd971 with [pop]⟩

theorem ammSwap0X_token1Address
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨973⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [ammMintToken1Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
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

theorem ammSwap0X_token1Distinct
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [ammMintToken1Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hne : ammSwap0ToWord I ≠ ammMintToken1Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1117⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap0ToWord I) solcAddrMask =
      ammSwap0ToWord I := solcAddrMask_clean hcanon
  have heq : UInt256.eq (ammSwap0ToWord I)
      (ammMintToken1Word σ I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun h => hne (uInt256_eq_one_eq h))
  have rd1052 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd1052' := rd1052
  rw [u256_land_comm solcAddrMask (ammSwap0ToWord I), hclean]
    at rd1052'
  have rd1054 := evm_run rd1052' with [eq, iszero]
  have rd1054' := rd1054
  rw [heq] at rd1054'
  exact ⟨_, _, evm_run rd1054' with [
    jumpdest, push2 ⟨1117⟩,
    jumpiT (by decide) (by jump_dest)]⟩

theorem ammSwap0X_token0Equal
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨941⟩
      [ammMintToken0Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (heq : ammSwap0ToWord I = ammMintToken0Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1059⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap0ToWord I) solcAddrMask =
      ammSwap0ToWord I := solcAddrMask_clean hcanon
  have hword : UInt256.eq (ammSwap0ToWord I)
      (ammMintToken0Word σ I) = ⟨1⟩ := by
    rw [heq]
    exact uInt256_eq_self _
  have rd964 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd964' := rd964
  rw [u256_land_comm solcAddrMask (ammSwap0ToWord I), hclean]
    at rd964'
  have rd966 := evm_run rd964' with [eq, iszero]
  have rd966' := rd966
  rw [hword] at rd966'
  have rd1054 := evm_run rd966' with [
    dup1, iszero, push2 ⟨1054⟩,
    jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd1054 with [
    jumpdest, push2 ⟨1117⟩, jumpiNT (by decide)]⟩

theorem ammSwap0X_token1Equal
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [ammMintToken1Word σ I, ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (heq : ammSwap0ToWord I = ammMintToken1Word σ I) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1059⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hclean : UInt256.land (ammSwap0ToWord I) solcAddrMask =
      ammSwap0ToWord I := solcAddrMask_clean hcanon
  have hword : UInt256.eq (ammSwap0ToWord I)
      (ammMintToken1Word σ I) = ⟨1⟩ := by
    rw [heq]
    exact uInt256_eq_self _
  have rd1052 := evm_run rd with [dup2, push20 solcAddrMask, and]
  have rd1052' := rd1052
  rw [u256_land_comm solcAddrMask (ammSwap0ToWord I), hclean]
    at rd1052'
  have rd1054 := evm_run rd1052' with [eq, iszero]
  have rd1054' := rd1054
  rw [hword] at rd1054'
  exact ⟨_, _, evm_run rd1054' with [
    jumpdest, push2 ⟨1117⟩, jumpiNT (by decide)]⟩

end Benchmarks.ActAmm
