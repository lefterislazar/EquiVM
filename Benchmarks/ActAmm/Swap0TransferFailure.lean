import Benchmarks.ActAmm.Swap0TransferCall
import Benchmarks.ActAmm.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0TransferCallFailureBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {A' : Substate} {out : ByteArray}
    (hcode : I.code = ammBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hne0 : ammSwap0ToWord I ≠ ammMintToken0Word σ_evm I)
    (hne1 : ammSwap0ToWord I ≠ ammMintToken1Word σ_evm I)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_evm }
      (AccountAddress.ofUInt256 (ammMintToken1Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (false, { initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, out)
      true)
    (hrev : RDrev ammBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evmEcall : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σ_evm }
  have haccCall : accountMapEquiv evmEcall.accountMap
      evmS.accountMap := by
    simpa [evmEcall, evmS, initState] using hAccounts
  obtain ⟨σS', hcallS, hσ'⟩ :=
    ammTypedCallTransport (evmS := evmS) hcallE
      haccCall
      (by simp [evmEcall, evmS, initState])
      (by simp [evmEcall, evmS, initState])
      (by simp [evmEcall, evmS, initState])
      (by simp [evmEcall, evmS, initState])
      (by simp [evmEcall, evmS, initState])
      (by simp [evmEcall, evmS, initState])
  obtain ⟨hliqS, h0S, h1S⟩ :=
    ammSwap0ValidSourceGuards (g := Sat256.ofUInt256 g)
      hAccounts hcanon hliq hne0 hne1
  have hslot4 : solcSlotWord σ_evm I ⟨4⟩ =
      solcSlotWord σ_solm I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hword1 : ammMintToken1Word σ_evm I =
      UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨4⟩) solcAddrMask := by
    change UInt256.land (solcSlotWord σ_evm I ⟨4⟩)
      solcAddrMask = UInt256.land (solcSlotWord σ_solm I ⟨4⟩)
        solcAddrMask
    rw [hslot4]
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256 (ammMintToken1Word σ_evm I) := by
    rw [hword1]
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).isLt
  let evmS' : EVM.State := { evmS with
    accountMap := σS', substate := A', createdAccounts := cA' }
  have hcallS' : typedCallViaEVM config evmS
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (false, evmS', out) true := by
    rw [htarget]
    simpa [evmS'] using hcallS
  have hbody := ammSwap0SourceTransferCallFailed I out
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hcallS'
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap0 hsel)
    (ammDecode_swap0_ok hsz68 hbig hcanon) hbody

theorem ammSwap0TransportTransferCall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {A' : Substate} {out : ByteArray}
    {z : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_evm }
      (AccountAddress.ofUInt256 (ammMintToken1Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (z, { initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, out)
      true) :
    ∃ σS', typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (ammMintToken1Word σ_evm I))
        "transfer" 0
        [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
          .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
        (z, { initState cA gh bl σ_solm σ₀
            (Sat256.ofUInt256 g) A I with
            accountMap := σS', substate := A', createdAccounts := cA' }, out)
        true ∧ accountMapEquiv σ' σS' := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hacc : accountMapEquiv σ_evm evmS.accountMap := by
    simpa [evmS, initState] using hAccounts
  obtain ⟨σS', hcallS, hσ'⟩ :=
    ammTypedCallTransport (evmS := evmS) hcallE
      (by simpa [initState] using hacc)
      (by simp [evmS, initState])
      (by simp [evmS, initState])
      (by simp [evmS, initState])
      (by simp [evmS, initState])
      (by simp [evmS, initState])
      (by simp [evmS, initState])
  exact ⟨σS', by simpa [evmS] using hcallS, hσ'⟩

theorem ammSwap0SourceTargetEq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evmS := initState cA gh bl σ_solm σ₀
      (Sat256.ofUInt256 g) A I
    EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val =
      AccountAddress.ofUInt256 (ammMintToken1Word σ_evm I) := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot4 : solcSlotWord σ_evm I ⟨4⟩ =
      solcSlotWord σ_solm I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  change EVM.address (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σ_solm I ⟨4⟩)
        solcAddrMask)).val =
    AccountAddress.ofUInt256 (UInt256.land
      (solcSlotWord σ_evm I ⟨4⟩) solcAddrMask)
  rw [hslot4]
  apply Fin.ext
  change (AccountAddress.ofUInt256 (UInt256.land
    (solcSlotWord σ_solm I ⟨4⟩) solcAddrMask)).val %
      EVM.twoPow 160 = _
  exact Nat.mod_eq_of_lt
    (AccountAddress.ofUInt256 (UInt256.land
      (solcSlotWord σ_solm I ⟨4⟩) solcAddrMask)).isLt

end Benchmarks.ActAmm
