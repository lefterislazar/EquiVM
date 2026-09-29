import Benchmarks.ActAmm4.SwapTransfer1Transport
import Benchmarks.ActAmm4.SwapSourceBalances

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapBalance0SourcePrefix
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA2 cA3 : Batteries.RBSet AccountAddress compare}
    {σE2 σE3 σS2 : AccountMap} {A2 A3 : Substate}
    {out0 : ByteArray} {b0 b1 : Bool}
    (hσ2 : accountMapEquiv σE2 σS2)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      (initState cA gh bl σ_solm σ₀ g A I)
      amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 }
        { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS2, substate := A2, createdAccounts := cA2 }))
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE2, substate := A2, createdAccounts := cA2 }
      (AccountAddress.ofUInt256 (amm4MintToken0Word σE2 I))
      "balanceOf" 0 [.address I.codeOwner]
      (true, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE3, substate := A3, createdAccounts := cA3 },
        out0) false)
    (hlo : 32 ≤ out0.size) (hbound : out0.size < 2 ^ 138) :
    ∃ σS3 : AccountMap,
      let evmS := initState cA gh bl σ_solm σ₀ g A I
      let evmS3 := { evmS with
        accountMap := σS3, substate := A3, createdAccounts := cA3 }
      accountMapEquiv σE3 σS3 ∧
      ExecBlock config { contract := contract, locals := amm4SwapStore I }
        evmS amm4SwapSourcePrefixBalance0
        (.ok { contract := contract, locals :=
          amm4SwapAfterBalance0Store I b0 b1 out0 } evmS3) := by
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
  let evmS3 : EVM.State := { evmS with
    accountMap := σS3, substate := A3, createdAccounts := cA3 }
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS2
          evmS2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val) =
      AccountAddress.ofUInt256 (amm4MintToken0Word σE2 I) := by
    rw [hword0]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken0Word σS2 I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken0Word σS2 I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256 (amm4MintToken0Word σS2 I)).isLt
  have hcallS' : typedCallViaEVM config evmS2
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS2
          evmS2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evmS2.executionEnv.codeOwner]
      (true, evmS3, out0) false := by
    rw [htarget]
    simpa [evmS2, evmS3, evmS, initState] using hcallS
  have hp3 := amm4SwapSourceBalance0CallOk I b0 b1 out0
    (by simpa [evmS2, evmS] using hprefix) hcallS' hlo hbound
  refine ⟨σS3, ?_, ?_⟩
  · simpa [evmE2, evmS2, evmS3, evmE, evmS, initState]
      using hσ3
  · simpa [evmS3, evmS] using hp3

end Benchmarks.ActAmm4
