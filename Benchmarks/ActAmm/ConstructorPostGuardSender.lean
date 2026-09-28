import Benchmarks.ActAmm.ConstructorPostGuardStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorPostGuardSenderBalanceStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity base : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨865⟩ [base, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hperm : I.perm = true)
    (haw : 3 ≤ aw.toNat) (hmem : 64 ≤ mem.size) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨931⟩ [liquidity, EVM.word t1, EVM.word t0]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ mem)
      aw rdata
      (acc.1, sstoreAccountMap I.codeOwner acc.2
        (solcMappingSlot ⟨1⟩ (solcSourceWord I)) base)
      k' C' := by
  let caller := solcSourceWord I
  have hclean : UInt256.land solcAddrMask caller = caller :=
    solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd914 := amm_ctor_run rd with [
    jumpdest, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and, dup2]
  rw [hclean, hclean] at rd914
  have rd915 := rd914.mstore 0 (wordAt0Mem caller mem) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        hM0, Nat.sub_self])
    (by rfl) (by simpa using hM0) (by evm_ov)
  have rd921 := amm_ctor_run rd915 with [push1 ⟨32⟩, add, swap1, dup2]
  have h32 : (⟨32⟩ : UInt256) + ⟨0⟩ = ⟨32⟩ := by decide
  rw [h32] at rd921
  have rd922 := rd921.mstore 0 (twoWordHashMem caller ⟨1⟩ mem) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
        hM32, Nat.sub_self])
    (by rfl) (by simpa using hM32) (by evm_ov)
  have rd926 := amm_ctor_run rd922 with [push1 ⟨32⟩, add, push0]
  have hlen64 : (⟨32⟩ : UInt256) + ⟨32⟩ = ⟨64⟩ := by decide
  rw [hlen64] at rd926
  have rd927 := rd926.keccak256 0
    (solcMappingSlot ⟨1⟩ caller) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    (by simpa only [caller] using ammCtorTwoWordHashMem_keccak caller ⟨1⟩ mem hmem)
    (by simpa using hM64) (by evm_ov)
  have rd929 := amm_ctor_run rd927 with [dup2, swap1]
  obtain ⟨_, _, rd930⟩ := rd929.sstore hperm (by amm_ctor_decode)
    (by evm_ov)
  exact ⟨_, _, by simpa only [caller, twoWordHashMem, wordAt32Mem] using
    (amm_ctor_run rd930 with [pop])⟩

end Benchmarks.ActAmm
