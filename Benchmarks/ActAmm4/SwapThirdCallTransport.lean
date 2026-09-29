import Benchmarks.ActAmm4.SwapSecondCallTransport
import Benchmarks.ActAmm4.SwapBalance0Transport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapThirdCallRawTransport
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA2 cA3 : Batteries.RBSet AccountAddress compare}
    {σE2 σS2 σE3 : AccountMap} {A2 A3 : Substate}
    {ret2 : ByteArray} {z2 : Bool}
    (hσ2 : accountMapEquiv σE2 σS2)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE2, substate := A2,
        createdAccounts := cA2 }
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σE2 I))
      "balanceOf" 0 [.address I.codeOwner]
      (z2, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE3, substate := A3,
        createdAccounts := cA3 }, ret2) false) :
    ∃ σS3 : AccountMap,
      accountMapEquiv σE3 σS3 ∧
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS2, substate := A2,
          createdAccounts := cA2 }
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS2, substate := A2,
              createdAccounts := cA2 }
            I.codeOwner ⟨3⟩) solcAddrMask)).val)
        "balanceOf" 0 [.address I.codeOwner]
        (z2, { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS3, substate := A3,
          createdAccounts := cA3 }, ret2) false := by
  let evmE := initState cA gh bl σ_evm σ₀ g A I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmE2 : EVM.State := { evmE with
    accountMap := σE2, substate := A2, createdAccounts := cA2 }
  let evmS2 : EVM.State := { evmS with
    accountMap := σS2, substate := A2, createdAccounts := cA2 }
  have hslot3 : solcSlotWord σE2 I ⟨3⟩ =
      solcSlotWord σS2 I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ2 I.codeOwner ⟨3⟩ ⟨0⟩
  have hword0 : amm4MintToken0Word σE2 I =
      amm4MintToken0Word σS2 I :=
    congrArg (fun w => UInt256.land w solcAddrMask) hslot3
  obtain ⟨σS3, hcallS, hσ3⟩ :=
    amm4TypedCallStaticTransport (evmS := evmS2) hcallE
      (by simpa [evmE2, evmS2, evmE, evmS, initState] using hσ2)
      (by simp [evmE2, evmS2, evmE, evmS, initState])
      (by simp [evmE2, evmS2, evmE, evmS, initState])
      (by simp [evmE2, evmS2, evmE, evmS, initState])
      (by simp [evmE2, evmS2, evmE, evmS, initState])
      (by simp [evmE2, evmS2, evmE, evmS, initState])
      (by simp [evmE2, evmS2, evmE, evmS, initState])
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS2
          evmS2.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256
        (amm4MintToken0Word σE2 I) := by
    rw [hword0]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken0Word σS2 I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken0Word σS2 I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σS2 I)).isLt
  refine ⟨σS3, ?_, ?_⟩
  · simpa [evmE2, evmS2, evmE, evmS, initState] using hσ3
  · have htarget' :
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS2, substate := A2,
              createdAccounts := cA2 }
            I.codeOwner ⟨3⟩) solcAddrMask)).val) =
        AccountAddress.ofUInt256
          (amm4MintToken0Word σE2 I) := by
        simpa [evmS2, evmS, initState] using htarget
    rw [htarget']
    simpa [evmS2, evmS, initState] using hcallS

end Benchmarks.ActAmm4
