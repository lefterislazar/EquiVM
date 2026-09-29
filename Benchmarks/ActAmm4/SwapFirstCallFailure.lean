import Benchmarks.ActAmm4.SwapFirstCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapFirstCallFailedEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA1 : Batteries.RBSet AccountAddress compare}
    {σE1 : AccountMap} {A1 : Substate}
    {ret0 : ByteArray} {k C : Nat}
    (hcode : I.code = amm4Bytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ_evm I)
    (hne1 : amm4SwapToWord I ≠ amm4MintToken1Word σ_evm I)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcallE : typedCallViaEVM config
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (false, { initState cA gh bl σ_evm σ₀
        (Sat256.ofUInt256 g) A I with
        accountMap := σE1, substate := A1,
        createdAccounts := cA1 }, ret0) true)
    (hsize : ret0.size < UInt256.size)
    (rd : RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨2607⟩
      [⟨0⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ_evm I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, amm4SelWord I]
      (amm4SwapTransfer0PostCallMem I ret0)
      (UInt256.ofNat 7) ret0 (cA1, σE1) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hguards := amm4SwapValidSourceGuards
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g)
    hAccounts hcanon hliq0 hliq1 hne0 hne1
  obtain ⟨σS1, _, hcallS⟩ :=
    amm4SwapFirstCallRawTransport hAccounts hcallE
  have hbody := amm4SwapSourceTransfer0CallFailed I ret0
    (by simpa [evmS, initState] using hwv)
    hpos hguards.1 hguards.2.1
    hguards.2.2.1 hguards.2.2.2
    (by simpa [evmS, initState] using hcallS)
  have hrev := amm4SwapX_transfer0CallFailed rd hsize
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact hrev.reEquivExecutionRevert hcode
    (amm4Dispatch_swap hsel)
    (amm4Decode_swap_ok hsz100 hbig hcanon) hbody

theorem amm4SwapFirstCallDecodeFailedEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA1 : Batteries.RBSet AccountAddress compare}
    {σE1 : AccountMap} {A1 : Substate}
    {ret0 : ByteArray}
    (hcode : I.code = amm4Bytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ_evm I)
    (hne1 : amm4SwapToWord I ≠ amm4MintToken1Word σ_evm I)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcallE : typedCallViaEVM config
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256
        (amm4MintToken0Word σ_evm I))
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, { initState cA gh bl σ_evm σ₀
        (Sat256.ofUInt256 g) A I with
        accountMap := σE1, substate := A1,
        createdAccounts := cA1 }, ret0) true)
    (hdec : config.externalABI.decode? "transfer" ret0 = none)
    (hrev : RDrev amm4Bytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀
        (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hguards := amm4SwapValidSourceGuards
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g)
    hAccounts hcanon hliq0 hliq1 hne0 hne1
  obtain ⟨σS1, _, hcallS⟩ :=
    amm4SwapFirstCallRawTransport hAccounts hcallE
  have hbody := amm4SwapSourceTransfer0DecodeRevert I ret0
    (by simpa [evmS, initState] using hwv)
    hpos hguards.1 hguards.2.1
    hguards.2.2.1 hguards.2.2.2
    (by simpa [evmS, initState] using hcallS) hdec
  exact hrev.reEquivExecutionRevert hcode
    (amm4Dispatch_swap hsel)
    (amm4Decode_swap_ok hsz100 hbig hcanon) hbody

end Benchmarks.ActAmm4
