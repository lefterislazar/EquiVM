import Benchmarks.ActAmm.Swap1TransferCall
import Benchmarks.ActAmm.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1TransferCallFailureBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {A' : Substate} {out : ByteArray}
    (hcode : I.code = ammBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hne0 : ammSwap1ToWord I ≠ ammMintToken0Word σ_evm I)
    (hne1 : ammSwap1ToWord I ≠ ammMintToken1Word σ_evm I)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_evm }
      (AccountAddress.ofUInt256 (ammMintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
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
    ammSwap1ValidSourceGuards (g := Sat256.ofUInt256 g)
      hAccounts hcanon hliq hne0 hne1
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hword0 : ammMintToken0Word σ_evm I =
      UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask := by
    change UInt256.land (solcSlotWord σ_evm I ⟨3⟩)
      solcAddrMask = UInt256.land (solcSlotWord σ_solm I ⟨3⟩)
        solcAddrMask
    rw [hslot3]
  have htarget :
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) =
      AccountAddress.ofUInt256 (ammMintToken0Word σ_evm I) := by
    rw [hword0]
    apply Fin.ext
    change (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)).val % EVM.twoPow 160 = _
    exact Nat.mod_eq_of_lt
      (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).isLt
  let evmS' : EVM.State := { evmS with
    accountMap := σS', substate := A', createdAccounts := cA' }
  have hcallS' : typedCallViaEVM config evmS
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (false, evmS', out) true := by
    rw [htarget]
    simpa [evmS'] using hcallS
  have hbody := ammSwap1SourceTransferCallFailed I out
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hcallS'
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

theorem ammSwap1TransportTransferCall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {A' : Substate} {out : ByteArray}
    {z : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcallE : typedCallViaEVM config
      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
        accountMap := σ_evm }
      (AccountAddress.ofUInt256 (ammMintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (z, { initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, out)
      true) :
    ∃ σS', typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (ammMintToken0Word σ_evm I))
        "transfer" 0
        [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
          .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
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

theorem ammSwap1SourceTargetEq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evmS := initState cA gh bl σ_solm σ₀
      (Sat256.ofUInt256 g) A I
    EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val =
      AccountAddress.ofUInt256 (ammMintToken0Word σ_evm I) := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  change EVM.address (AccountAddress.ofUInt256
      (UInt256.land (solcSlotWord σ_solm I ⟨3⟩)
        solcAddrMask)).val =
    AccountAddress.ofUInt256 (UInt256.land
      (solcSlotWord σ_evm I ⟨3⟩) solcAddrMask)
  rw [hslot3]
  apply Fin.ext
  change (AccountAddress.ofUInt256 (UInt256.land
    (solcSlotWord σ_solm I ⟨3⟩) solcAddrMask)).val %
      EVM.twoPow 160 = _
  exact Nat.mod_eq_of_lt
    (AccountAddress.ofUInt256 (UInt256.land
      (solcSlotWord σ_solm I ⟨3⟩) solcAddrMask)).isLt

end Benchmarks.ActAmm
