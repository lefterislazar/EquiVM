import Benchmarks.ActAmm.Swap0Balance1Source
import Benchmarks.ActAmm.Swap0Balance0Failure

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0TransportBalance1Call
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    {cA2 cA3 : Batteries.RBSet AccountAddress compare}
    {σE2 σS2 σE3 : AccountMap} {A2 A3 : Substate}
    {ret : ByteArray} {z : Bool}
    (hσ2 : accountMapEquiv σE2 σS2)
    (hcallE : typedCallViaEVM config
      { initState cA2 gh bl σE2 σ₀ (Sat256.ofUInt256 g) A2 I with
        accountMap := σE2 }
      (AccountAddress.ofUInt256 (ammMintToken1Word σE2 I))
      "balanceOf" 0 [.address I.codeOwner]
      (z, { initState cA2 gh bl σE2 σ₀
          (Sat256.ofUInt256 g) A2 I with
          accountMap := σE3, substate := A3, createdAccounts := cA3 }, ret)
      false) :
    ∃ σS3 : AccountMap,
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σS2, substate := A2, createdAccounts := cA2 }
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀
              (Sat256.ofUInt256 g) A I with
              accountMap := σS2, substate := A2,
              createdAccounts := cA2 }
            I.codeOwner ⟨4⟩) solcAddrMask)).val)
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σS3, substate := A3, createdAccounts := cA3 }, ret)
        false ∧ accountMapEquiv σE3 σS3 := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evmS2 : EVM.State := { evmS with
    accountMap := σS2, substate := A2, createdAccounts := cA2 }
  let evmE2 : EVM.State :=
    { initState cA2 gh bl σE2 σ₀ (Sat256.ofUInt256 g) A2 I with
      accountMap := σE2 }
  have hacc : accountMapEquiv evmE2.accountMap evmS2.accountMap := by
    simpa [evmE2, evmS2] using hσ2
  obtain ⟨σS3, hcallS, hσ3⟩ :=
    ammTypedCallTransport (evmS := evmS2) hcallE hacc
      (by simp [evmE2, evmS2, evmS, initState])
      (by simp [evmE2, evmS2, evmS, initState])
      (by simp [evmE2, evmS2, evmS, initState])
      (by simp [evmE2, evmS2, evmS, initState])
      (by simp [evmE2, evmS2, evmS, initState])
      (by simp [evmE2, evmS2, evmS, initState])
  have hslot4 : solcSlotWord σE2 I ⟨4⟩ =
      solcSlotWord σS2 I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ2 I.codeOwner ⟨4⟩ ⟨0⟩
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS2
          I.codeOwner ⟨4⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256 (ammMintToken1Word σE2 I) := by
    change EVM.address (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS2 I ⟨4⟩) solcAddrMask)).val =
      AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σE2 I ⟨4⟩) solcAddrMask)
    rw [hslot4]
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS2 I ⟨4⟩)
        solcAddrMask)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σS2 I ⟨4⟩) solcAddrMask)).isLt
  rw [htarget]
  exact ⟨σS3, by simpa [evmS2, evmS] using hcallS, hσ3⟩


end Benchmarks.ActAmm

