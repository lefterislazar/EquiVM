import Benchmarks.ActAmm4.ConstructorPostGuardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

def amm4CtorPostGuardEvmMap (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ liquidity)
      (solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val)) ⟨1000⟩)
    (solcMappingSlot ⟨1⟩ (solcSourceWord I))
    (UInt256.sub liquidity ⟨1000⟩)

theorem amm4CtorPostGuardSourceAccountMap
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    (amm4CtorPostGuardAfterSender
      (amm4CtorPostGuardAfterSelf
        (amm4CtorPostGuardAfterSupply evm liquidity)) I liquidity).accountMap =
      amm4CtorPostGuardEvmMap I σ (EVM.word liquidity.toNat) := by
  intro evm
  let evm3 := amm4CtorPostGuardAfterSupply evm liquidity
  let evm4 := amm4CtorPostGuardAfterSelf evm3
  have howner : evm.executionEnv.codeOwner = I.codeOwner := by
    simp [evm, initState]
  have howner3 : evm3.executionEnv.codeOwner = I.codeOwner := by
    simp [evm3, amm4CtorPostGuardAfterSupply, storageStore_executionEnv, howner]
  have howner4 : evm4.executionEnv.codeOwner = I.codeOwner := by
    simp [evm4, amm4CtorPostGuardAfterSelf, storageStore_executionEnv, howner3]
  have hword := amm4CtorBaseSupplyWord_eq liquidity h0 hle hfit
  change (Solm.EVM.storageStore evm4 evm4.executionEnv.codeOwner
    (amm4TransferSenderSlot I) (UInt256.ofNat (liquidity.toNat - 1000))).accountMap = _
  rw [storageStore_accountMap, howner4, ← amm4TransferSenderSlot_eq_solc I]
  change sstoreAccountMap I.codeOwner
    (Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner
      (balanceOfSlot (.address evm3.executionEnv.codeOwner)) ⟨1000⟩).accountMap
    (solcMappingSlot ⟨1⟩ (solcSourceWord I))
    (UInt256.ofNat (liquidity.toNat - 1000)) = _
  rw [storageStore_accountMap, howner3,
    show balanceOfSlot (.address I.codeOwner) =
      solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val) from by
        simpa only [amm4CtorSelfSlot] using (amm4CtorSelfSlot_eq_solc I).symm]
  change sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (UInt256.ofNat liquidity.toNat)).accountMap
      (solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val)) ⟨1000⟩)
    (solcMappingSlot ⟨1⟩ (solcSourceWord I))
    (UInt256.ofNat (liquidity.toNat - 1000)) = _
  rw [storageStore_accountMap, howner, hword]
  rfl

theorem amm4CtorPostGuardMaps_equiv
    (I : ExecutionEnv) (σE σS : AccountMap) (liquidity : UInt256)
    (hAccounts : accountMapEquiv σE σS) :
    accountMapEquiv (amm4CtorPostGuardEvmMap I σE liquidity)
      (amm4CtorPostGuardEvmMap I σS liquidity) := by
  unfold amm4CtorPostGuardEvmMap
  exact accountMapEquiv_sstoreAccountMap I.codeOwner
    (solcMappingSlot ⟨1⟩ (solcSourceWord I))
    (UInt256.sub liquidity ⟨1000⟩)
    (accountMapEquiv_sstoreAccountMap I.codeOwner
      (solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val)) ⟨1000⟩
      (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ liquidity hAccounts))

theorem amm4CtorPostGuardSourceState_shape
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    amm4CtorPostGuardAfterSender
      (amm4CtorPostGuardAfterSelf
        (amm4CtorPostGuardAfterSupply evm liquidity)) I liquidity =
      initState createdAccounts genesisBlockHeader blocks
        (amm4CtorPostGuardEvmMap I σ (EVM.word liquidity.toNat)) σ₀
        (Sat256.ofUInt256 g) A I := by
  intro evm
  have hmap := amm4CtorPostGuardSourceAccountMap
    (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
    (σ := σ) (σ₀ := σ₀) (g := g) (A := A) (I := I)
    liquidity h0 hle hfit
  have hshape :
      amm4CtorPostGuardAfterSender
        (amm4CtorPostGuardAfterSelf
          (amm4CtorPostGuardAfterSupply evm liquidity)) I liquidity =
        { evm with accountMap :=
          (amm4CtorPostGuardAfterSender
            (amm4CtorPostGuardAfterSelf
              (amm4CtorPostGuardAfterSupply evm liquidity)) I liquidity).accountMap } := by
    simp [amm4CtorPostGuardAfterSender, amm4CtorPostGuardAfterSelf,
      amm4CtorPostGuardAfterSupply, amm4CtorStorageStore_eq_updateAccountMap]
  rw [hshape, hmap]
  rfl

end Benchmarks.ActAmm4
