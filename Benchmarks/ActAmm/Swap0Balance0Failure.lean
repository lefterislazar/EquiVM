import Benchmarks.ActAmm.Swap0Balance0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0Balance0CallFailureBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA1 cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σS1 σE2 : AccountMap} {A1 A2 : Substate}
    {ret : ByteArray} {b : Bool}
    (hcode : I.code = ammBytecode)
    (hsel : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        { initState cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σS1, substate := A1,
          createdAccounts := cA1 }))
    (hσ1 : accountMapEquiv σE1 σS1)
    (hcallE : typedCallViaEVM config
      { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
        accountMap := σE1 }
      (AccountAddress.ofUInt256 (ammMintToken0Word σE1 I))
      "balanceOf" 0 [.address I.codeOwner]
      (false, { initState cA1 gh bl σE1 σ₀
          (Sat256.ofUInt256 g) A1 I with
          accountMap := σE2, substate := A2, createdAccounts := cA2 }, ret)
      false)
    (hrev : RDrev ammBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evmS1 : EVM.State := { evmS with
    accountMap := σS1, substate := A1, createdAccounts := cA1 }
  let evmE1 : EVM.State :=
    { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
      accountMap := σE1 }
  have hacc : accountMapEquiv evmE1.accountMap evmS1.accountMap := by
    simpa [evmE1, evmS1] using hσ1
  obtain ⟨σS2, hcallS, hσ2⟩ :=
    ammTypedCallTransport (evmS := evmS1) hcallE hacc
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
  have hslot3 : solcSlotWord σE1 I ⟨3⟩ =
      solcSlotWord σS1 I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ1 I.codeOwner ⟨3⟩ ⟨0⟩
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS1
          evmS1.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256 (ammMintToken0Word σE1 I) := by
    change EVM.address (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS1 I ⟨3⟩) solcAddrMask)).val =
      AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σE1 I ⟨3⟩) solcAddrMask)
    rw [hslot3]
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS1 I ⟨3⟩)
        solcAddrMask)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σS1 I ⟨3⟩) solcAddrMask)).isLt
  let evmS2 : EVM.State := { evmS1 with
    accountMap := σS2, substate := A2, createdAccounts := cA2 }
  have hcallS' : typedCallViaEVM config evmS1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS1
          evmS1.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evmS1.executionEnv.codeOwner]
      (false, evmS2, ret) false := by
    rw [htarget]
    simpa [evmS2, evmS1, evmS] using hcallS
  have hbody := ammSwap0SourceBalance0CallFailed I b ret
    (by simpa [evmS1, evmS] using hprefix) hcallS'
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap0 hsel)
    (ammDecode_swap0_ok hsz68 hbig hcanon) hbody

theorem ammSwap0TransportBalance0Call
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    {cA1 cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σS1 σE2 : AccountMap} {A1 A2 : Substate}
    {ret : ByteArray} {z : Bool}
    (hσ1 : accountMapEquiv σE1 σS1)
    (hcallE : typedCallViaEVM config
      { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
        accountMap := σE1 }
      (AccountAddress.ofUInt256 (ammMintToken0Word σE1 I))
      "balanceOf" 0 [.address I.codeOwner]
      (z, { initState cA1 gh bl σE1 σ₀
          (Sat256.ofUInt256 g) A1 I with
          accountMap := σE2, substate := A2, createdAccounts := cA2 }, ret)
      false) :
    ∃ σS2 : AccountMap,
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σS1, substate := A1, createdAccounts := cA1 }
        (EVM.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad
            { initState cA gh bl σ_solm σ₀
              (Sat256.ofUInt256 g) A I with
              accountMap := σS1, substate := A1,
              createdAccounts := cA1 }
            I.codeOwner ⟨3⟩) solcAddrMask)).val)
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σS2, substate := A2, createdAccounts := cA2 }, ret)
        false ∧ accountMapEquiv σE2 σS2 := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evmS1 : EVM.State := { evmS with
    accountMap := σS1, substate := A1, createdAccounts := cA1 }
  let evmE1 : EVM.State :=
    { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
      accountMap := σE1 }
  have hacc : accountMapEquiv evmE1.accountMap evmS1.accountMap := by
    simpa [evmE1, evmS1] using hσ1
  obtain ⟨σS2, hcallS, hσ2⟩ :=
    ammTypedCallTransport (evmS := evmS1) hcallE hacc
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
      (by simp [evmE1, evmS1, evmS, initState])
  have hslot3 : solcSlotWord σE1 I ⟨3⟩ =
      solcSlotWord σS1 I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hσ1 I.codeOwner ⟨3⟩ ⟨0⟩
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS1
          I.codeOwner ⟨3⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256 (ammMintToken0Word σE1 I) := by
    change EVM.address (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS1 I ⟨3⟩) solcAddrMask)).val =
      AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σE1 I ⟨3⟩) solcAddrMask)
    rw [hslot3]
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σS1 I ⟨3⟩)
        solcAddrMask)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256 (UInt256.land
        (solcSlotWord σS1 I ⟨3⟩) solcAddrMask)).isLt
  rw [htarget]
  exact ⟨σS2, by simpa [evmS1, evmS] using hcallS, hσ2⟩

theorem ammSwap0SourceBalance0Prefix
    {cA gh bl σ_solm σ₀ A I} {g : UInt256}
    {cA1 cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σS1 σE2 : AccountMap} {A1 A2 : Substate}
    {ret : ByteArray} {b : Bool}
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        { initState cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σS1, substate := A1,
          createdAccounts := cA1 }))
    (hσ1 : accountMapEquiv σE1 σS1)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hcallE : typedCallViaEVM config
      { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
        accountMap := σE1 }
      (AccountAddress.ofUInt256 (ammMintToken0Word σE1 I))
      "balanceOf" 0 [.address I.codeOwner]
      (true, { initState cA1 gh bl σE1 σ₀
          (Sat256.ofUInt256 g) A1 I with
          accountMap := σE2, substate := A2, createdAccounts := cA2 }, ret)
      false) :
    ∃ σS2 : AccountMap, accountMapEquiv σE2 σS2 ∧
      ExecBlock config
        { contract := contract, locals := ammSwap0Store I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ammSwap0SourcePrefixBalance0
        (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
          { initState cA gh bl σ_solm σ₀
            (Sat256.ofUInt256 g) A I with
            accountMap := σS2, substate := A2,
            createdAccounts := cA2 }) := by
  obtain ⟨σS2, hcallS, hσ2⟩ :=
    ammSwap0TransportBalance0Call (cA := cA) (σ_solm := σ_solm)
      (A := A) hσ1 hcallE
  have hprefix' := ammSwap0SourceBalance0CallOk I b ret
    hprefix hretLo hretBound hcallS
  exact ⟨σS2, hσ2, hprefix'⟩

end Benchmarks.ActAmm
