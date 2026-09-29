import Benchmarks.ActAmm4.SwapFirstCallTransport
import Benchmarks.ActAmm4.SwapTransfer1Transport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapSecondCallRawTransport
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA1 cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σS1 σE2 : AccountMap} {A1 A2 : Substate}
    {ret1 : ByteArray} {z1 : Bool}
    (hσ1 : accountMapEquiv σE1 σS1)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE1, substate := A1,
        createdAccounts := cA1 }
      (AccountAddress.ofUInt256
        (amm4MintToken1Word σE1 I))
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (z1, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE2, substate := A2,
        createdAccounts := cA2 }, ret1) true) :
    ∃ σS2 : AccountMap,
      accountMapEquiv σE2 σS2 ∧
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS1, substate := A1,
          createdAccounts := cA1 }
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS1, substate := A1,
              createdAccounts := cA1 }
            I.codeOwner ⟨4⟩) solcAddrMask)).val)
        "transfer" 0
        [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
          .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
        (z1, { initState cA gh bl σ_solm σ₀ g A I with
          accountMap := σS2, substate := A2,
          createdAccounts := cA2 }, ret1) true := by
  let evmE := initState cA gh bl σ_evm σ₀ g A I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmE1 : EVM.State := { evmE with
    accountMap := σE1, substate := A1, createdAccounts := cA1 }
  let evmS1 : EVM.State := { evmS with
    accountMap := σS1, substate := A1, createdAccounts := cA1 }
  have hslot4 : solcSlotWord σE1 I ⟨4⟩ =
      solcSlotWord σS1 I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ1 I.codeOwner ⟨4⟩ ⟨0⟩
  have hword1 : amm4MintToken1Word σE1 I =
      amm4MintToken1Word σS1 I :=
    congrArg (fun w => UInt256.land w solcAddrMask) hslot4
  obtain ⟨σS2, hcallS, hσ2⟩ :=
    amm4TypedCallTransport (evmS := evmS1) hcallE
      (by simpa [evmE1, evmS1, evmE, evmS, initState] using hσ1)
      (by simp [evmE1, evmS1, evmE, evmS, initState])
      (by simp [evmE1, evmS1, evmE, evmS, initState])
      (by simp [evmE1, evmS1, evmE, evmS, initState])
      (by simp [evmE1, evmS1, evmE, evmS, initState])
      (by simp [evmE1, evmS1, evmE, evmS, initState])
      (by simp [evmE1, evmS1, evmE, evmS, initState])
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS1
          evmS1.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256
        (amm4MintToken1Word σE1 I) := by
    rw [hword1]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken1Word σS1 I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken1Word σS1 I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (amm4MintToken1Word σS1 I)).isLt
  refine ⟨σS2, ?_, ?_⟩
  · simpa [evmE1, evmS1, evmE, evmS, initState] using hσ2
  · have htarget' :
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σS1, substate := A1,
              createdAccounts := cA1 }
            I.codeOwner ⟨4⟩) solcAddrMask)).val) =
        AccountAddress.ofUInt256
          (amm4MintToken1Word σE1 I) := by
        simpa [evmS1, evmS, initState] using htarget
    rw [htarget']
    simpa [evmS1, evmS, initState] using hcallS

end Benchmarks.ActAmm4
