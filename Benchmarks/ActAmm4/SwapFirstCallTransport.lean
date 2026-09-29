import Benchmarks.ActAmm4.SwapFirstCallDepth
import Benchmarks.ActAmm4.SwapTransfer0Transport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapFirstCallRawTransport
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA1 : Batteries.RBSet AccountAddress compare}
    {σE1 : AccountMap} {A1 : Substate}
    {ret0 : ByteArray} {z0 : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcallE : typedCallViaEVM config
      (initState cA gh bl σ_evm σ₀ g A I)
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (z0, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE1, substate := A1,
        createdAccounts := cA1 }, ret0) true) :
    ∃ σS1 : AccountMap,
      accountMapEquiv σE1 σS1 ∧
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ g A I)
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            (initState cA gh bl σ_solm σ₀ g A I)
            I.codeOwner ⟨3⟩) solcAddrMask)).val)
        "transfer" 0
        [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
          .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
        (z0, { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS1, substate := A1,
          createdAccounts := cA1 }, ret0) true := by
  let evmE := initState cA gh bl σ_evm σ₀ g A I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hword0 : amm4MintToken0Word σ_evm I =
      amm4MintToken0Word σ_solm I :=
    congrArg (fun w => UInt256.land w solcAddrMask) hslot3
  obtain ⟨σS1, hcallS, hσ1⟩ :=
    amm4TypedCallTransport (evmS := evmS) hcallE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256
        (amm4MintToken0Word σ_evm I) := by
    rw [hword0]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken0Word σ_solm I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken0Word σ_solm I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σ_solm I)).isLt
  refine ⟨σS1, ?_, ?_⟩
  · simpa [evmE, evmS, initState] using hσ1
  · have htarget' :
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            (initState cA gh bl σ_solm σ₀ g A I)
            I.codeOwner ⟨3⟩) solcAddrMask)).val) =
        AccountAddress.ofUInt256
          (amm4MintToken0Word σ_evm I) := by
        simpa [evmS, initState] using htarget
    rw [htarget']
    simpa [evmS, initState] using hcallS

end Benchmarks.ActAmm4
