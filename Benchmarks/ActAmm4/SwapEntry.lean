import Benchmarks.ActAmm4.SwapTransfer0Call
import Benchmarks.ActAmm4.SwapSourceGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_transfer0FrameFromEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ I ⟨6⟩).toNat)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ I)
    (hne1 : amm4SwapToWord I ≠ amm4MintToken1Word σ I)
    (hreach : ∃ k C, RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k C : Nat), RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2606⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2111⟩ := amm4SwapX_decoded hsz100 hsize hbig
    hcanon hreach
  obtain ⟨_, _, rd2187⟩ := amm4SwapX_outputGuardOk rd2111 hpos
  obtain ⟨_, _, rd2268⟩ := amm4SwapX_liquidityGuardOk rd2187
    hliq0 hliq1
  obtain ⟨_, _, rd2325⟩ := amm4SwapX_token0Address rd2268
  obtain ⟨_, _, rd2357⟩ := amm4SwapX_token0Distinct rd2325 hcanon hne0
  obtain ⟨_, _, rd2413⟩ := amm4SwapX_token1Address rd2357
  obtain ⟨_, _, rd2501⟩ := amm4SwapX_token1Distinct rd2413 hcanon hne1
  obtain ⟨_, _, rd2558⟩ := amm4SwapX_transfer0TokenAddress rd2501
  obtain ⟨_, _, rd2580⟩ := amm4SwapX_transfer0SelectorMem rd2558
  obtain ⟨_, _, rd2593⟩ := amm4SwapX_transfer0Args rd2580 hcanon
  exact amm4SwapX_transfer0CallFrame rd2593

theorem amm4SwapValidSourceGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ_evm I)
    (hne1 : amm4SwapToWord I ≠ amm4MintToken1Word σ_evm I) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩).toNat ∧
    (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨6⟩).toNat ∧
    AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) ∧
    AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
  let evmS := initState cA gh bl σ_solm σ₀ g A I
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
  have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
      solcSlotWord σ_solm I ⟨6⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hliq0S : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨5⟩).toNat := by
    change (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_solm I ⟨5⟩).toNat
    rw [← hslot5]
    exact hliq0
  have hliq1S : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨6⟩).toNat := by
    change (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_solm I ⟨6⟩).toNat
    rw [← hslot6]
    exact hliq1
  have h0S : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (amm4MintToken0Word σ_solm I)
    rw [← show amm4MintToken0Word σ_evm I =
      amm4MintToken0Word σ_solm I by
        simp only [amm4MintToken0Word, hslot3]]
    intro haddr
    exact hne0 ((amm4CanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨3⟩))).mp haddr)
  have h1S : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (amm4MintToken1Word σ_solm I)
    rw [← show amm4MintToken1Word σ_evm I =
      amm4MintToken1Word σ_solm I by
        simp only [amm4MintToken1Word, hslot4]]
    intro haddr
    exact hne1 ((amm4CanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨4⟩))).mp haddr)
  exact ⟨hliq0S, hliq1S, h0S, h1S⟩

end Benchmarks.ActAmm4
