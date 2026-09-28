import Benchmarks.ActAmm.Swap1TransferDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1TransferDecodeRevertBody
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
    ammSwap1ValidSourceGuards (cA := cA) (gh := gh) (bl := bl)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      hAccounts hcanon hliq hne0 hne1
  obtain ⟨σS', hcallS, hσ'⟩ :=
    ammSwap1TransportTransferCall hAccounts hcallE
  have htarget := ammSwap1SourceTargetEq
    (g := g) (cA := cA) (gh := gh) (bl := bl)
    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (A := A) (I := I) hAccounts
  let evmS' : EVM.State := { evmS with
    accountMap := σS', substate := A', createdAccounts := cA' }
  have hcallS' : typedCallViaEVM config evmS
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evmS
          evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (true, evmS', out) true := by
    rw [htarget]
    simpa [evmS', evmS] using hcallS
  have hbody := ammSwap1SourceTransferDecodeRevert I out
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hcallS' hdec
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
