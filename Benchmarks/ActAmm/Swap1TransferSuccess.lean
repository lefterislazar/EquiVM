import Benchmarks.ActAmm.Swap1TransferDecodeRevert
import Benchmarks.ActAmm.Swap1SourceCall
import Benchmarks.ActAmm.BurnSourceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1DecodeTransferCanonical {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 138)
    (hcanon : UInt256.ofNat
      (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
      (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    ∃ b : Bool, config.externalABI.decode? "transfer" out =
      some [.bool b] := by
  rw [ammBurnDecodeTransfer_word hlo (by omega : out.size < 2 ^ 255)]
  rcases hcanon with hzero | hone
  · exact ⟨false, by simp [hzero]⟩
  · exact ⟨true, by simp [hone, UInt256.size]⟩

theorem ammSwap1SourceTransferPrefix
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {A' : Substate} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
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
    (hdec : ∃ b : Bool, config.externalABI.decode? "transfer" out =
      some [.bool b]) :
    ∃ (σS' : AccountMap) (b : Bool),
      accountMapEquiv σ' σS' ∧
      ExecBlock config
        { contract := contract, locals := ammSwap1Store I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        ammSwap1SourcePrefixTransfer
        (.ok { contract := contract, locals := ammSwap1AfterTransferStore I b }
          { initState cA gh bl σ_solm σ₀
            (Sat256.ofUInt256 g) A I with
            accountMap := σS', substate := A',
            createdAccounts := cA' }) := by
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
  obtain ⟨b, hdecode⟩ := hdec
  have hprefix := ammSwap1SourceTransferCallOk I out b
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hcallS' hdecode
  exact ⟨σS', b, hσ', by simpa [evmS, evmS'] using hprefix⟩

end Benchmarks.ActAmm
