import Benchmarks.ActAmm4.ConstructorReserve0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorFinalToken1Target (I : ExecutionEnv)
    (σ : AccountMap) : UInt256 :=
  UInt256.land (amm4CtorStorageWord σ I ⟨4⟩) solcAddrMask

theorem amm4CtorFinalToken1Target_eq_doubleMask
    (I : ExecutionEnv) (σ : AccountMap) :
    UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div (amm4CtorStorageWord σ I ⟨4⟩)
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      amm4CtorFinalToken1Target I σ := by
  let w := amm4CtorStorageWord σ I ⟨4⟩
  have hpow : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv : UInt256.div w (UInt256.exp ⟨256⟩ ⟨0⟩) = w := by
    rw [hpow]
    apply u256_inj
    rw [udiv_toNat]
    change w.toNat / 1 = w.toNat
    simp
  have hmask : UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land w solcAddrMask := by
    rw [u256_land_comm solcAddrMask w]
    exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)
  unfold amm4CtorFinalToken1Target
  simp only [w, hdiv, hmask]

theorem amm4CtorFourthCallTarget
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1090⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1146⟩ [amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k' C' := by
  have rd1094 := amm4_ctor_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd1095⟩ := rd1094.sload (by amm4_ctor_decode) (by evm_ov)
  have rd1146 := amm4_ctor_run rd1095 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have htop : UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩))
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      amm4CtorFinalToken1Target I σ := by
    simpa only [amm4CtorStorageWord] using
      amm4CtorFinalToken1Target_eq_doubleMask I σ
  rw [htop] at rd1146
  exact ⟨_, _, by simpa using rd1146⟩

theorem amm4CtorThirdCallDecodeMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size) :
    (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) := by
  unfold amm4CtorThirdCallDecodeMem
  exact toByteArray_write32_read_back _ _ 64 (by
    rw [amm4CtorThirdCallPostCallMem_size I t0 t1 liquidity
      ret1 ret2 ret3 hbound1 hbound2 hretsz3]
    have hs := amm4CtorThirdCallArgMem_size I t0 t1 liquidity
      ret1 ret2 hbound1 hbound2
    have hp := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    omega)

theorem amm4CtorFourthCallFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1146⟩ [amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorThirdCallArgWords ret1 ret2) ret3 (cA, σ) k C)
    (haw : 3 ≤ (amm4CtorThirdCallArgWords ret1 ret2).toNat)
    (hload :
      (if (⟨64⟩ : UInt256).toNat ≥
            (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size ∨
          (⟨64⟩ : UInt256) ≥ amm4CtorThirdCallArgWords ret1 ret2 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
           64 32))) = amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1155⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorThirdCallArgWords ret1 ret2) ret3 (cA, σ) k' C' := by
  let aw := amm4CtorThirdCallArgWords ret1 ret2
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    change UInt256.ofNat (max aw.toNat 3) = aw
    rw [max_eq_left haw]
    exact u256_ofNat_toNat aw
  dsimp only [aw] at hM64
  have rd1154 := amm4_ctor_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1155 := rd1154.mload 0
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) aw
    (by amm4_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    hload (by simpa using hM64) (by evm_ov)
  exact ⟨_, _, by simpa only [aw] using rd1155⟩

end Benchmarks.ActAmm4
