import Benchmarks.ActAmm4.SwapEntry
import Benchmarks.ActAmm4.SwapSourceCalls
import Benchmarks.ActAmm4.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapTransfer0SourcePrefix
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA1 : Batteries.RBSet AccountAddress compare}
    {σE1 : AccountMap} {A1 : Substate} {ret0 : ByteArray} {b0 : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ_evm I)
    (hne1 : amm4SwapToWord I ≠ amm4MintToken1Word σ_evm I)
    (hcallE : typedCallViaEVM config
      (initState cA gh bl σ_evm σ₀ g A I)
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σE1, substate := A1, createdAccounts := cA1 },
        ret0) true)
    (hdec : config.externalABI.decode? "transfer" ret0 =
      some [.bool b0]) :
    ∃ σS1 : AccountMap,
      let evmS := initState cA gh bl σ_solm σ₀ g A I
      let evmS1 := { evmS with
        accountMap := σS1, substate := A1, createdAccounts := cA1 }
      accountMapEquiv σE1 σS1 ∧
      ExecBlock config { contract := contract, locals := amm4SwapStore I }
        evmS amm4SwapSourcePrefixTransfer0
        (.ok { contract := contract, locals :=
          amm4SwapAfterTransfer0Store I b0 } evmS1) := by
  let evmE := initState cA gh bl σ_evm σ₀ g A I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hword0 : amm4MintToken0Word σ_evm I =
      amm4MintToken0Word σ_solm I := by
    exact congrArg (fun w => UInt256.land w solcAddrMask) hslot3
  obtain ⟨σS1, hcallS, hσ1⟩ :=
    amm4TypedCallTransport (evmS := evmS) hcallE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
  let evmS1 : EVM.State := { evmS with
    accountMap := σS1, substate := A1, createdAccounts := cA1 }
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val) =
      AccountAddress.ofUInt256 (amm4MintToken0Word σ_evm I) := by
    rw [hword0]
    change EVM.address (AccountAddress.ofUInt256
      (amm4MintToken0Word σ_solm I)).val = _
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (amm4MintToken0Word σ_solm I)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ_solm I)).isLt
  have hcallS' : typedCallViaEVM config evmS
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evmS1, ret0) true := by
    rw [htarget]
    simpa [evmS1, evmS, initState] using hcallS
  obtain ⟨hliq0S, hliq1S, h0S, h1S⟩ :=
    amm4SwapValidSourceGuards hAccounts hcanon hliq0 hliq1 hne0 hne1
  have hprefix := amm4SwapSourceTransfer0CallOk I ret0 b0
    (by simpa [evmS, initState] using hwv) hpos hliq0S hliq1S
    h0S h1S hcallS' hdec
  refine ⟨σS1, ?_, ?_⟩
  · simpa [evmE, evmS, evmS1, initState] using hσ1
  · simpa [evmS1, evmS] using hprefix

end Benchmarks.ActAmm4
