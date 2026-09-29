import Benchmarks.ActAmm4.ConstructorInitialCallTrace
import Benchmarks.ActAmm4.ConstructorSourceStorage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorStorageStore_eq_updateAccountMap
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    Solm.EVM.storageStore evm a slot val =
      { evm with accountMap := sstoreAccountMap a evm.accountMap slot val } := by
  simp only [Solm.EVM.storageStore, Ethereum.State.lookupAccount,
    sstoreAccountMap]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, Ethereum.State.setAccount,
      Ethereum.Account.updateStorage]

theorem amm4CtorBaseSupplyWord_eq (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    UInt256.ofNat (liquidity.toNat - 1000) =
      UInt256.sub (EVM.word liquidity.toNat) ⟨1000⟩ := by
  have hlt : liquidity < Int.ofNat (EVM.twoPow 256) := by
    change liquidity.toNat < 2 ^ 256 at hfit
    change liquidity < (2 ^ 256 : ℕ)
    omega
  apply u256_inj
  rw [ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)]
  rw [usub_toNat]
  · rw [constructorUInt256Word_toNat liquidity h0 hlt]
    rfl
  · rw [constructorUInt256Word_toNat liquidity h0 hlt]
    exact hle

theorem amm4CtorStoredSourceAccountMap
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    evm4.accountMap =
      amm4CtorToken1Storage I σ (EVM.word liquidity.toNat) t0 t1 := by
  intro evm evm1 evm2 evm3 evm4
  have hword := amm4CtorBaseSupplyWord_eq liquidity h0 hle hfit
  have howner0 : evm.executionEnv.codeOwner = I.codeOwner := by
    simp [evm, initState]
  have howner1 : evm1.executionEnv.codeOwner = I.codeOwner := by
    simp [evm1, amm4CtorAfterSupply, storageStore_executionEnv, howner0]
  have howner2 : evm2.executionEnv.codeOwner = I.codeOwner := by
    simp [evm2, amm4CtorAfterSender, storageStore_executionEnv, howner1]
  have howner3 : evm3.executionEnv.codeOwner = I.codeOwner := by
    simp [evm3, amm4CtorAfterToken0, storageStore_executionEnv, howner2]
  have he1 : evm1.accountMap =
      sstoreAccountMap I.codeOwner σ ⟨0⟩
        (UInt256.sub (EVM.word liquidity.toNat) ⟨1000⟩) := by
    change (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
      (UInt256.ofNat (liquidity.toNat - 1000))).accountMap = _
    rw [storageStore_accountMap, howner0, hword]
    rfl
  have he2 : evm2.accountMap =
      amm4CtorSenderStorage I σ (EVM.word liquidity.toNat) := by
    change (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner
      (amm4TransferSenderSlot I)
      (UInt256.ofNat (liquidity.toNat - 1000))).accountMap = _
    rw [storageStore_accountMap, howner1, he1, hword,
      ← amm4TransferSenderSlot_eq_solc]
    rfl
  have hload3 : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨3⟩ =
      amm4CtorStorageWord (amm4CtorSenderStorage I σ (EVM.word liquidity.toNat))
        I ⟨3⟩ := by
    simp only [Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
      Account.lookupStorage, howner2, he2, amm4CtorStorageWord]
  have he3 : evm3.accountMap =
      amm4CtorToken0Storage I σ (EVM.word liquidity.toNat) t0 := by
    change (Solm.EVM.storageStore evm2 evm2.executionEnv.codeOwner ⟨3⟩
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨3⟩)
        (EVM.word t0))).accountMap = _
    rw [storageStore_accountMap, hload3, howner2, he2]
    rfl
  have hload4 : Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner ⟨4⟩ =
      amm4CtorStorageWord
        (amm4CtorToken0Storage I σ (EVM.word liquidity.toNat) t0) I ⟨4⟩ := by
    simp only [Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
      Account.lookupStorage, howner3, he3, amm4CtorStorageWord]
  change (Solm.EVM.storageStore evm3 evm3.executionEnv.codeOwner ⟨4⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm3 evm3.executionEnv.codeOwner ⟨4⟩)
      (EVM.word t1))).accountMap = _
  rw [storageStore_accountMap, hload4, howner3, he3]
  rfl

theorem amm4CtorStoredSourceState_shape
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    evm4 = { evm with accountMap :=
      amm4CtorToken1Storage I σ (EVM.word liquidity.toNat) t0 t1 } := by
  intro evm evm1 evm2 evm3 evm4
  have hmap : evm4.accountMap =
      amm4CtorToken1Storage I σ (EVM.word liquidity.toNat) t0 t1 :=
    amm4CtorStoredSourceAccountMap t0 t1 liquidity h0 hle hfit
  have hshape : evm4 = { evm with accountMap := evm4.accountMap } := by
    simp [evm4, evm3, evm2, evm1, amm4CtorAfterToken1,
      amm4CtorAfterToken0, amm4CtorAfterSender, amm4CtorAfterSupply,
      amm4CtorStorageStore_eq_updateAccountMap]
  simpa only [hmap] using hshape

theorem amm4CtorInitialToken1Target_source
    (evm : EVM.State) (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress)
    (hmap : evm.accountMap = amm4CtorToken1Storage I σ liquidity t0 t1)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    storageLocLoad evm (addrLoc ⟨4⟩) =
      .address (AccountAddress.ofUInt256
        (amm4CtorInitialToken1Target I σ liquidity t0 t1)) := by
  have hread : storageLocLoad evm (addrLoc ⟨4⟩) =
      .address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat) := by
    simpa only [addrLoc, addressOffset0Loc] using
      storageLocLoad_address_offset0 evm ⟨4⟩
  have hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩ =
      amm4CtorStorageWord (amm4CtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩ := by
    simp only [Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
      Account.lookupStorage, howner, hmap, amm4CtorStorageWord]
  rw [hread, hload, amm4CtorInitialToken1Target_eq_masked,
    accountAddress_ofUInt256_eq_ofNat_toNat]

theorem amm4CtorToken1Storage_equiv
    (I : ExecutionEnv) (σ_evm σ_solm : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (amm4CtorToken1Storage I σ_evm liquidity t0 t1)
      (amm4CtorToken1Storage I σ_solm liquidity t0 t1) := by
  have hsender : accountMapEquiv
      (amm4CtorSenderStorage I σ_evm liquidity)
      (amm4CtorSenderStorage I σ_solm liquidity) := by
    unfold amm4CtorSenderStorage
    exact accountMapEquiv_sstoreAccountMap I.codeOwner
      (solcMappingSlot ⟨1⟩ (solcSourceWord I))
      (UInt256.sub liquidity ⟨1000⟩)
      (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (UInt256.sub liquidity ⟨1000⟩) hAccounts)
  have hread3 :
      amm4CtorStorageWord (amm4CtorSenderStorage I σ_evm liquidity) I ⟨3⟩ =
      amm4CtorStorageWord (amm4CtorSenderStorage I σ_solm liquidity) I ⟨3⟩ := by
    exact accountMapEquiv_storage_findD hsender I.codeOwner ⟨3⟩ ⟨0⟩
  have htoken0 : accountMapEquiv
      (amm4CtorToken0Storage I σ_evm liquidity t0)
      (amm4CtorToken0Storage I σ_solm liquidity t0) := by
    unfold amm4CtorToken0Storage
    rw [hread3]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩
      (setAddressOffset0Word
        (amm4CtorStorageWord (amm4CtorSenderStorage I σ_solm liquidity) I ⟨3⟩)
        (EVM.word t0)) hsender
  have hread4 :
      amm4CtorStorageWord (amm4CtorToken0Storage I σ_evm liquidity t0) I ⟨4⟩ =
      amm4CtorStorageWord (amm4CtorToken0Storage I σ_solm liquidity t0) I ⟨4⟩ := by
    exact accountMapEquiv_storage_findD htoken0 I.codeOwner ⟨4⟩ ⟨0⟩
  unfold amm4CtorToken1Storage
  rw [hread4]
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩
    (setAddressOffset0Word
      (amm4CtorStorageWord
        (amm4CtorToken0Storage I σ_solm liquidity t0) I ⟨4⟩)
      (EVM.word t1)) htoken0

theorem amm4CtorInitialToken1Target_equiv
    (I : ExecutionEnv) (σ_evm σ_solm : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    amm4CtorInitialToken1Target I σ_evm liquidity t0 t1 =
      amm4CtorInitialToken1Target I σ_solm liquidity t0 t1 := by
  rw [amm4CtorInitialToken1Target_eq_masked,
    amm4CtorInitialToken1Target_eq_masked]
  rw [show amm4CtorStorageWord
      (amm4CtorToken1Storage I σ_evm liquidity t0 t1) I ⟨4⟩ =
      amm4CtorStorageWord
        (amm4CtorToken1Storage I σ_solm liquidity t0 t1) I ⟨4⟩ from
    accountMapEquiv_storage_findD
      (amm4CtorToken1Storage_equiv I σ_evm σ_solm liquidity t0 t1 hAccounts)
      I.codeOwner ⟨4⟩ ⟨0⟩]

end Benchmarks.ActAmm4
