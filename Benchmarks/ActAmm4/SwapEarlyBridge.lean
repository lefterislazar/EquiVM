import Benchmarks.ActAmm4.SwapRecipientRevert
import Benchmarks.ActAmm4.SwapOutputRevert
import Benchmarks.ActAmm4.SwapSourceEarlyRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

/-- Either an early swap guard reverts on both sides, or all guards needed
    to enter the first external transfer hold. -/
theorem amm4SwapEarlyGuardOrValid
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨323⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I ∨
    (0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat) ∧
    (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat ∧
    (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat ∧
    amm4SwapToWord I ≠ amm4MintToken0Word σ_evm I ∧
    amm4SwapToWord I ≠ amm4MintToken1Word σ_evm I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hdispatch := amm4Dispatch_swap hsel
  have hdec := amm4Decode_swap_ok hsz100 hbig hcanon
  have hwvS : evmS.executionEnv.weiValue = ⟨0⟩ := by
    simpa [evmS, initState] using hwv
  obtain ⟨_, _, rd2111⟩ := amm4SwapX_decoded hsz100 hsize hbig
    hcanon hreach
  by_cases hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat
  · obtain ⟨_, _, rd2187⟩ := amm4SwapX_outputGuardOk rd2111 hpos
    by_cases hliq0 : (amm4SwapAmount0Word I).toNat <
        (solcSlotWord σ_evm I ⟨5⟩).toNat
    · by_cases hliq1 : (amm4SwapAmount1Word I).toNat <
          (solcSlotWord σ_evm I ⟨6⟩).toNat
      · obtain ⟨_, _, rd2268⟩ :=
          amm4SwapX_liquidityGuardOk rd2187 hliq0 hliq1
        by_cases hne0 : amm4SwapToWord I ≠
            amm4MintToken0Word σ_evm I
        · by_cases hne1 : amm4SwapToWord I ≠
              amm4MintToken1Word σ_evm I
          · exact Or.inr ⟨hpos, hliq0, hliq1, hne0, hne1⟩
          · have heq1 : amm4SwapToWord I =
              amm4MintToken1Word σ_evm I := not_not.mp hne1
            have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
                solcSlotWord σ_solm I ⟨3⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  ⟨3⟩ ⟨0⟩
            have hslot4 : solcSlotWord σ_evm I ⟨4⟩ =
                solcSlotWord σ_solm I ⟨4⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  ⟨4⟩ ⟨0⟩
            have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
                solcSlotWord σ_solm I ⟨5⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  ⟨5⟩ ⟨0⟩
            have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
                solcSlotWord σ_solm I ⟨6⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  ⟨6⟩ ⟨0⟩
            have haddr0ne : AccountAddress.ofNat
                (amm4SwapToWord I).toNat ≠
                AccountAddress.ofUInt256 (UInt256.land
                  (Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨3⟩)
                  solcAddrMask) := by
              change AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
                AccountAddress.ofUInt256
                  (amm4MintToken0Word σ_solm I)
              rw [← show amm4MintToken0Word σ_evm I =
                amm4MintToken0Word σ_solm I by
                  simp only [amm4MintToken0Word, hslot3]]
              intro haddr
              exact hne0 ((amm4CanonicalAddressWordEq hcanon
                (solcAddrMask_result_canonical
                  (solcSlotWord σ_evm I ⟨3⟩))).mp haddr)
            -- The source's second recipient check uses the same canonical
            -- address as the EVM word comparison.
            have haddr1 : AccountAddress.ofNat
                (amm4SwapToWord I).toNat =
                AccountAddress.ofUInt256 (UInt256.land
                  (Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨4⟩)
                  solcAddrMask) := by
              change AccountAddress.ofNat (amm4SwapToWord I).toNat =
                AccountAddress.ofUInt256
                  (amm4MintToken1Word σ_solm I)
              rw [← show amm4MintToken1Word σ_evm I =
                amm4MintToken1Word σ_solm I by
                  simp only [amm4MintToken1Word, hslot4]]
              exact (amm4CanonicalAddressWordEq hcanon
                (solcAddrMask_result_canonical
                  (solcSlotWord σ_evm I ⟨4⟩))).mpr heq1
            have hbody := amm4SwapSourceRecipient1Revert evmS I
              hwvS hpos
              (by change _ < (solcSlotWord σ_solm I ⟨5⟩).toNat
                  rw [← hslot5]; exact hliq0)
              (by change _ < (solcSlotWord σ_solm I ⟨6⟩).toNat
                  rw [← hslot6]; exact hliq1)
              haddr0ne haddr1
            exact Or.inl ((amm4SwapX_recipient1Revert rd2268
              hcanon hne0 heq1).reEquivExecutionRevert
              hcode hdispatch hdec hbody)
        · have heq0 : amm4SwapToWord I =
              amm4MintToken0Word σ_evm I := not_not.mp hne0
          have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
              solcSlotWord σ_solm I ⟨3⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
          have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
              solcSlotWord σ_solm I ⟨5⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
          have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
              solcSlotWord σ_solm I ⟨6⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
          have haddr0 : AccountAddress.ofNat
              (amm4SwapToWord I).toNat =
              AccountAddress.ofUInt256 (UInt256.land
                (Solm.EVM.storageLoad evmS
                  evmS.executionEnv.codeOwner ⟨3⟩)
                solcAddrMask) := by
            change AccountAddress.ofNat (amm4SwapToWord I).toNat =
              AccountAddress.ofUInt256
                (amm4MintToken0Word σ_solm I)
            rw [← show amm4MintToken0Word σ_evm I =
              amm4MintToken0Word σ_solm I by
                simp only [amm4MintToken0Word, hslot3]]
            exact (amm4CanonicalAddressWordEq hcanon
              (solcAddrMask_result_canonical
                (solcSlotWord σ_evm I ⟨3⟩))).mpr heq0
          have hbody := amm4SwapSourceRecipient0Revert evmS I hwvS
            hpos (by change _ < (solcSlotWord σ_solm I ⟨5⟩).toNat
                     rw [← hslot5]; exact hliq0)
            (by change _ < (solcSlotWord σ_solm I ⟨6⟩).toNat
                rw [← hslot6]; exact hliq1) haddr0
          exact Or.inl ((amm4SwapX_recipient0Revert rd2268
            hcanon heq0).reEquivExecutionRevert
            hcode hdispatch hdec hbody)
      · have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
            solcSlotWord σ_solm I ⟨6⟩ := by
          simpa [solcSlotWord, codeOwnerStorageWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
        have hbody := amm4SwapSourceLiquidity1Revert evmS I hwvS
          hpos (by change _ < (solcSlotWord σ_solm I ⟨5⟩).toNat
                   rw [← show solcSlotWord σ_evm I ⟨5⟩ =
                     solcSlotWord σ_solm I ⟨5⟩ by
                       simpa [solcSlotWord, codeOwnerStorageWord] using
                         accountMapEquiv_storage_findD hAccounts
                           I.codeOwner ⟨5⟩ ⟨0⟩]
                   exact hliq0)
          (by change (solcSlotWord σ_solm I ⟨6⟩).toNat ≤ _
              rw [← hslot6]; omega)
        exact Or.inl ((amm4SwapX_liquidity1Revert rd2187
          hliq0 (by omega)).reEquivExecutionRevert
          hcode hdispatch hdec hbody)
    · have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
          solcSlotWord σ_solm I ⟨5⟩ := by
        simpa [solcSlotWord, codeOwnerStorageWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
      have hbody := amm4SwapSourceLiquidity0Revert evmS I hwvS
        hpos (by change (solcSlotWord σ_solm I ⟨5⟩).toNat ≤ _
                 rw [← hslot5]; omega)
      exact Or.inl ((amm4SwapX_liquidity0Revert rd2187
        (by omega)).reEquivExecutionRevert
        hcode hdispatch hdec hbody)
  · have hzero0 : (amm4SwapAmount0Word I).toNat = 0 := by omega
    have hzero1 : (amm4SwapAmount1Word I).toNat = 0 := by omega
    have hbody := amm4SwapSourceZeroOutput evmS I hwvS hzero0 hzero1
    exact Or.inl ((amm4SwapX_zeroOutputRevert rd2111
      hzero0 hzero1).reEquivExecutionRevert
      hcode hdispatch hdec hbody)

end Benchmarks.ActAmm4
