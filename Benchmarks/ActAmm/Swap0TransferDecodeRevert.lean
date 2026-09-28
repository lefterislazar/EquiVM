import Benchmarks.ActAmm.Swap0TransferDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0TransferDecodeRevertBody
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
      (true, { initState cA gh bl σ_evm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, out)
      true)
    (hdec : config.externalABI.decode? "transfer" out = none)
    (hrev : RDrev ammBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  obtain ⟨hliqS, h0S, h1S⟩ :=
    ammSwap0ValidSourceGuards (cA := cA) (gh := gh) (bl := bl)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      hAccounts hcanon hliq hne0 hne1
  obtain ⟨σS', hcallS, hσ'⟩ :=
    ammSwap0TransportTransferCall hAccounts hcallE
  have htarget := ammSwap0SourceTargetEq
    (g := g) (cA := cA) (gh := gh) (bl := bl)
    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (A := A) (I := I) hAccounts
  let evmS' : EVM.State := { evmS with
    accountMap := σS', substate := A', createdAccounts := cA' }
  have hcallS' : typedCallViaEVM config evmS
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (true, evmS', out) true := by
    rw [htarget]
    simpa [evmS', evmS] using hcallS
  have hbody := ammSwap0SourceTransferDecodeRevert I out
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hcallS' hdec
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap0 hsel)
    (ammDecode_swap0_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
