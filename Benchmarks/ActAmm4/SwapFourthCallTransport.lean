import Benchmarks.ActAmm4.SwapThirdCallTransport
import Benchmarks.ActAmm4.SwapBalance1Transport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapFourthCallRawTransport
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA3 cA4 : Batteries.RBSet AccountAddress compare}
    {σE3 σS3 σE4 : AccountMap} {A3 A4 : Substate}
    {ret3 : ByteArray} {z3 : Bool}
    (hσ3 : accountMapEquiv σE3 σS3)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE3, substate := A3,
        createdAccounts := cA3 }
      (AccountAddress.ofUInt256
        (amm4MintToken1Word σE3 I))
      "balanceOf" 0 [.address I.codeOwner]
      (z3, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE4, substate := A4,
        createdAccounts := cA4 }, ret3) false) :
    ∃ σS4 : AccountMap,
      accountMapEquiv σE4 σS4 ∧
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS3, substate := A3,
          createdAccounts := cA3 }
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS3, substate := A3,
              createdAccounts := cA3 }
            I.codeOwner ⟨4⟩) solcAddrMask)).val)
        "balanceOf" 0 [.address I.codeOwner]
        (z3, { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS4, substate := A4,
          createdAccounts := cA4 }, ret3) false := by
  let evmE := initState cA gh bl σ_evm σ₀ g A I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmE3 : EVM.State := { evmE with
    accountMap := σE3, substate := A3, createdAccounts := cA3 }
  let evmS3 : EVM.State := { evmS with
    accountMap := σS3, substate := A3, createdAccounts := cA3 }
  have hslot4 : solcSlotWord σE3 I ⟨4⟩ =
      solcSlotWord σS3 I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ3 I.codeOwner ⟨4⟩ ⟨0⟩
  have hword1 : amm4MintToken1Word σE3 I =
      amm4MintToken1Word σS3 I :=
    congrArg (fun w => UInt256.land w solcAddrMask) hslot4
  obtain ⟨σS4, hcallS, hσ4⟩ :=
    amm4TypedCallStaticTransport (evmS := evmS3) hcallE
      (by simpa [evmE3, evmS3, evmE, evmS, initState] using hσ3)
      (by simp [evmE3, evmS3, evmE, evmS, initState])
      (by simp [evmE3, evmS3, evmE, evmS, initState])
      (by simp [evmE3, evmS3, evmE, evmS, initState])
      (by simp [evmE3, evmS3, evmE, evmS, initState])
      (by simp [evmE3, evmS3, evmE, evmS, initState])
      (by simp [evmE3, evmS3, evmE, evmS, initState])
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS3
          evmS3.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256
        (amm4MintToken1Word σE3 I) := by
    rw [hword1]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken1Word σS3 I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken1Word σS3 I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (amm4MintToken1Word σS3 I)).isLt
  refine ⟨σS4, ?_, ?_⟩
  · simpa [evmE3, evmS3, evmE, evmS, initState] using hσ4
  · have htarget' :
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS3, substate := A3,
              createdAccounts := cA3 }
            I.codeOwner ⟨4⟩) solcAddrMask)).val) =
        AccountAddress.ofUInt256
          (amm4MintToken1Word σE3 I) := by
        simpa [evmS3, evmS, initState] using htarget
    rw [htarget']
    simpa [evmS3, evmS, initState] using hcallS

end Benchmarks.ActAmm4
