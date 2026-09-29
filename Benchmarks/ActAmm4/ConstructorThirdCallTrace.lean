import Benchmarks.ActAmm4.ConstructorPostGuardBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorPostGuardMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩
    (twoWordHashMem (UInt256.ofNat I.codeOwner.val) ⟨1⟩
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2))

theorem amm4CtorPostGuardMem_baseSize
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2).size =
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
  have hretsz2 : ret2.size < UInt256.size := by
    have hb := hbound2
    norm_num [UInt256.size] at *
    omega
  have hbase : 96 ≤
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hs := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  unfold amm4CtorPostGuardMem
  rw [amm4CtorTwoWordHashMem_size _ _ _ (by
    rw [amm4CtorTwoWordHashMem_size _ _ _ (by omega)]
    omega),
    amm4CtorTwoWordHashMem_size _ _ _ (by omega)]

theorem amm4CtorPostGuardMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray (amm4CtorAfterSecondReturnFreePtr ret1 ret2) := by
  have hretsz2 : ret2.size < UInt256.size := by
    have hb := hbound2
    norm_num [UInt256.size] at *
    omega
  have hbase : 96 ≤
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hs := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  unfold amm4CtorPostGuardMem
  rw [amm4CtorTwoWordHashMem_read64 _ _ _ (by
    rw [amm4CtorTwoWordHashMem_size _ _ _ (by omega)]
    exact hbase),
    amm4CtorTwoWordHashMem_read64 _ _ _ hbase]
  exact amm4CtorSecondCallDecodeMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem amm4CtorAfterSecondReturnFreePtr_toNat (ret1 ret2 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * ((ret1.size + 31) / 32) +
        32 * ((ret2.size + 31) / 32) := by
  unfold amm4CtorAfterSecondReturnFreePtr
  rw [uadd_toNat, amm4CtorSecondCallFreePtr_toNat ret1 hbound1,
    amm4MintReturndataRounded_toNat ret2 hbound2]
  rw [Nat.mod_eq_of_lt]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorAfterSecondReturnFreePtr_bounds (ret1 ret2 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    224 ≤ (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat ∧
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat < 2 ^ 141 := by
  rw [amm4CtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  omega

theorem amm4CtorThirdCallTarget
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨931⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨987⟩ [amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k' C' := by
  have rd935 := amm4_ctor_run rd with [
    push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd936⟩ := rd935.sload (by amm4_ctor_decode) (by evm_ov)
  have rd987 := amm4_ctor_run rd936 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have htop : UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩))
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      amm4CtorInitialToken0Target I σ := by
    simpa only [amm4CtorStorageWord] using
      amm4CtorInitialToken0Target_eq_doubleMask I σ
  rw [htop] at rd987
  exact ⟨_, _, by simpa using rd987⟩

theorem amm4CtorThirdCallFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨987⟩ [amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 (cA, σ) k C)
    (haw : 3 ≤ (amm4CtorSecondCallArgWords ret1).toNat)
    (hload :
      (if (⟨64⟩ : UInt256).toNat ≥
            (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2).size ∨
          (⟨64⟩ : UInt256) ≥ amm4CtorSecondCallArgWords ret1 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2).readWithPadding
           64 32))) = amm4CtorAfterSecondReturnFreePtr ret1 ret2) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨996⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 (cA, σ) k' C' := by
  let aw := amm4CtorSecondCallArgWords ret1
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    change UInt256.ofNat (max aw.toNat 3) = aw
    rw [max_eq_left haw]
    exact u256_ofNat_toNat aw
  dsimp only [aw] at hM64
  have rd995 := amm4_ctor_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd996 := rd995.mload 0 (amm4CtorAfterSecondReturnFreePtr ret1 ret2) aw
    (by amm4_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    hload (by simpa using hM64) (by evm_ov)
  exact ⟨_, _, by simpa only [aw] using rd996⟩

end Benchmarks.ActAmm4
