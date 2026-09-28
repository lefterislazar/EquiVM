import Benchmarks.ActAmm.Swap1ErrorTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1Recipient0Body
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (heq : ammSwap1ToWord I = ammMintToken0Word σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
      solcSlotWord σ_solm I ⟨5⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have htoken0 : ammMintToken0Word σ_evm I =
      ammMintToken0Word σ_solm I := by
    simp only [ammMintToken0Word, hslot3]
  have hliqS : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨5⟩).toNat := by
    change (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_solm I ⟨5⟩).toNat
    rw [← hslot5]
    exact hliq
  have hto0S : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (ammMintToken0Word σ_solm I)
    rw [← htoken0, ← heq, accountAddress_ofUInt256_eq_ofNat_toNat]
  have hbody := ammSwap1SourceInvalidRecipient0 evmS I
    (by simpa [evmS, initState] using hwv) hpos hliqS hto0S
  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
    hsz68 hsize hbig hcanon hreach
  obtain ⟨_, _, rd816⟩ := ammSwap1X_amountPositive rd750 hpos
  obtain ⟨_, _, rd884⟩ := ammSwap1X_liquidityAvailable rd816 hliq
  obtain ⟨_, _, rd941⟩ := ammSwap1X_token0Address rd884
  obtain ⟨_, _, rd1059⟩ := ammSwap1X_token0Equal rd941 hcanon heq
  have hrev := ammSwap1X_recipientRevert rd1059
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

theorem ammSwap1Recipient1Body
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hne0 : ammSwap1ToWord I ≠ ammMintToken0Word σ_evm I)
    (heq1 : ammSwap1ToWord I = ammMintToken1Word σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hslot4 : solcSlotWord σ_evm I ⟨4⟩ =
      solcSlotWord σ_solm I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
      solcSlotWord σ_solm I ⟨5⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have htoken0 : ammMintToken0Word σ_evm I =
      ammMintToken0Word σ_solm I := by
    simp only [ammMintToken0Word, hslot3]
  have htoken1 : ammMintToken1Word σ_evm I =
      ammMintToken1Word σ_solm I := by
    simp only [ammMintToken1Word, hslot4]
  have hliqS : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨5⟩).toNat := by
    change (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_solm I ⟨5⟩).toNat
    rw [← hslot5]
    exact hliq
  have hto0S : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (ammMintToken0Word σ_solm I)
    rw [← htoken0]
    intro haddr
    exact hne0 ((ammCanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨3⟩))).mp haddr)
  have hto1S : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (ammMintToken1Word σ_solm I)
    rw [← htoken1, ← heq1, accountAddress_ofUInt256_eq_ofNat_toNat]
  have hbody := ammSwap1SourceInvalidRecipient1 evmS I
    (by simpa [evmS, initState] using hwv) hpos hliqS hto0S hto1S
  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
    hsz68 hsize hbig hcanon hreach
  obtain ⟨_, _, rd816⟩ := ammSwap1X_amountPositive rd750 hpos
  obtain ⟨_, _, rd884⟩ := ammSwap1X_liquidityAvailable rd816 hliq
  obtain ⟨_, _, rd941⟩ := ammSwap1X_token0Address rd884
  obtain ⟨_, _, rd973⟩ := ammSwap1X_token0Distinct rd941 hcanon hne0
  obtain ⟨_, _, rd1029⟩ := ammSwap1X_token1Address rd973
  obtain ⟨_, _, rd1059⟩ := ammSwap1X_token1Equal rd1029 hcanon heq1
  have hrev := ammSwap1X_recipientRevert rd1059
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
