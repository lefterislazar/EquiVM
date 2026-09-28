import Benchmarks.ActAmm.ConstructorPostGuardBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorPostGuardMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩
    (twoWordHashMem (UInt256.ofNat I.codeOwner.val) ⟨1⟩
      (ammCtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2))

theorem ammCtorPostGuardMem_baseSize
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2).size =
      (ammCtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
  have hretsz2 : ret2.size < UInt256.size := by
    have hb := hbound2
    norm_num [UInt256.size] at *
    omega
  have hbase : 96 ≤
      (ammCtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
    rw [ammCtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hs := ammCtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (ammCtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  unfold ammCtorPostGuardMem
  rw [ammCtorTwoWordHashMem_size _ _ _ (by
    rw [ammCtorTwoWordHashMem_size _ _ _ (by omega)]
    omega),
    ammCtorTwoWordHashMem_size _ _ _ (by omega)]

theorem ammCtorPostGuardMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray (ammCtorAfterSecondReturnFreePtr ret1 ret2) := by
  have hretsz2 : ret2.size < UInt256.size := by
    have hb := hbound2
    norm_num [UInt256.size] at *
    omega
  have hbase : 96 ≤
      (ammCtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
    rw [ammCtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hs := ammCtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (ammCtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  unfold ammCtorPostGuardMem
  rw [ammCtorTwoWordHashMem_read64 _ _ _ (by
    rw [ammCtorTwoWordHashMem_size _ _ _ (by omega)]
    exact hbase),
    ammCtorTwoWordHashMem_read64 _ _ _ hbase]
  exact ammCtorSecondCallDecodeMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem ammCtorAfterSecondReturnFreePtr_toNat (ret1 ret2 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * ((ret1.size + 31) / 32) +
        32 * ((ret2.size + 31) / 32) := by
  unfold ammCtorAfterSecondReturnFreePtr
  rw [uadd_toNat, ammCtorSecondCallFreePtr_toNat ret1 hbound1,
    ammMintReturndataRounded_toNat ret2 hbound2]
  rw [Nat.mod_eq_of_lt]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  norm_num [UInt256.size] at *
  omega

theorem ammCtorAfterSecondReturnFreePtr_bounds (ret1 ret2 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    224 ≤ (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat ∧
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat < 2 ^ 141 := by
  rw [ammCtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  omega

theorem ammCtorThirdCallTarget
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
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨931⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨987⟩ [ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k' C' := by
  have rd935 := amm_ctor_run rd with [
    push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd936⟩ := rd935.sload (by amm_ctor_decode) (by evm_ov)
  have rd987 := amm_ctor_run rd936 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have htop : UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩))
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      ammCtorInitialToken0Target I σ := by
    simpa only [ammCtorStorageWord] using
      ammCtorInitialToken0Target_eq_doubleMask I σ
  rw [htop] at rd987
  exact ⟨_, _, by simpa using rd987⟩

theorem ammCtorThirdCallFreePtrLoaded
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
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨987⟩ [ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (ammCtorSecondCallArgWords ret1) ret2 (cA, σ) k C)
    (haw : 3 ≤ (ammCtorSecondCallArgWords ret1).toNat)
    (hload :
      (if (⟨64⟩ : UInt256).toNat ≥
            (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2).size ∨
          (⟨64⟩ : UInt256) ≥ ammCtorSecondCallArgWords ret1 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2).readWithPadding
           64 32))) = ammCtorAfterSecondReturnFreePtr ret1 ret2) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨996⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (ammCtorSecondCallArgWords ret1) ret2 (cA, σ) k' C' := by
  let aw := ammCtorSecondCallArgWords ret1
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    change UInt256.ofNat (max aw.toNat 3) = aw
    rw [max_eq_left haw]
    exact u256_ofNat_toNat aw
  dsimp only [aw] at hM64
  have rd995 := amm_ctor_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd996 := rd995.mload 0 (ammCtorAfterSecondReturnFreePtr ret1 ret2) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    hload (by simpa using hM64) (by evm_ov)
  exact ⟨_, _, by simpa only [aw] using rd996⟩

end Benchmarks.ActAmm
