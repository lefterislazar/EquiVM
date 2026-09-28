import Benchmarks.ActAmm.ConstructorReserve0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorFinalToken1Target (I : ExecutionEnv)
    (σ : AccountMap) : UInt256 :=
  UInt256.land (ammCtorStorageWord σ I ⟨4⟩) solcAddrMask

theorem ammCtorFinalToken1Target_eq_doubleMask
    (I : ExecutionEnv) (σ : AccountMap) :
    UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div (ammCtorStorageWord σ I ⟨4⟩)
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      ammCtorFinalToken1Target I σ := by
  let w := ammCtorStorageWord σ I ⟨4⟩
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
  unfold ammCtorFinalToken1Target
  simp only [w, hdiv, hmask]

theorem ammCtorFourthCallTarget
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1090⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1146⟩ [ammCtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata (cA, σ) k' C' := by
  have rd1094 := amm_ctor_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd1095⟩ := rd1094.sload (by amm_ctor_decode) (by evm_ov)
  have rd1146 := amm_ctor_run rd1095 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have htop : UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩))
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      ammCtorFinalToken1Target I σ := by
    simpa only [ammCtorStorageWord] using
      ammCtorFinalToken1Target_eq_doubleMask I σ
  rw [htop] at rd1146
  exact ⟨_, _, by simpa using rd1146⟩

theorem ammCtorThirdCallDecodeMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size) :
    (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      64 32 = UInt256.toByteArray
        (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3) := by
  unfold ammCtorThirdCallDecodeMem
  exact toByteArray_write32_read_back _ _ 64 (by
    rw [ammCtorThirdCallPostCallMem_size I t0 t1 liquidity
      ret1 ret2 ret3 hbound1 hbound2 hretsz3]
    have hs := ammCtorThirdCallArgMem_size I t0 t1 liquidity
      ret1 ret2 hbound1 hbound2
    have hp := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    omega)

theorem ammCtorFourthCallFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1146⟩ [ammCtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 (cA, σ) k C)
    (haw : 3 ≤ (ammCtorThirdCallArgWords ret1 ret2).toNat)
    (hload :
      (if (⟨64⟩ : UInt256).toNat ≥
            (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size ∨
          (⟨64⟩ : UInt256) ≥ ammCtorThirdCallArgWords ret1 ret2 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
           64 32))) = ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1155⟩ [ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 (cA, σ) k' C' := by
  let aw := ammCtorThirdCallArgWords ret1 ret2
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    change UInt256.ofNat (max aw.toNat 3) = aw
    rw [max_eq_left haw]
    exact u256_ofNat_toNat aw
  dsimp only [aw] at hM64
  have rd1154 := amm_ctor_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1155 := rd1154.mload 0
    (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    hload (by simpa using hM64) (by evm_ov)
  exact ⟨_, _, by simpa only [aw] using rd1155⟩

end Benchmarks.ActAmm
