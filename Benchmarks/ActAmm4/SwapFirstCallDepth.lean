import Benchmarks.ActAmm4.SwapEarlyBridge
import Benchmarks.ActAmm4.SwapSourceCallReverts
import Benchmarks.ActAmm4.SwapEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapFirstCallDepthEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode)
    (hsize : I.calldata.size < UInt256.size)
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
    (hdepth : I.depth = 1024)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨323⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let tgt : EVM.Address := EVM.address
    (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val
  have hguards := amm4SwapValidSourceGuards
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g)
    hAccounts hcanon hliq0 hliq1 hne0 hne1
  have hcall : typedCallViaEVM config evmS tgt "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (false,
        { evmS with
          substate := (evmS.addAccessedAccount tgt).substate },
        ByteArray.empty) true := by
    apply callNotMade_depthLimit
      (calldata := (amm4SwapTransfer0CalldataMem I).readWithPadding
        128 68)
    · exact amm4SwapTransfer0CalldataMem_encode I hcanon
    · simpa [evmS, initState] using hdepth
  have hbody := amm4SwapSourceTransfer0CallFailed I
    ByteArray.empty
    (by simpa [evmS, initState] using hwv)
    hpos hguards.1 hguards.2.1
    hguards.2.2.1 hguards.2.2.2 hcall
  obtain ⟨_, _, _, rd2606⟩ :=
    amm4SwapX_transfer0FrameFromEntry hsz100 hsize hbig
      hcanon hpos hliq0 hliq1 hne0 hne1 hreach
  have hrev := amm4SwapX_transfer0DepthRevert
    hdepth rd2606
  exact hrev.reEquivExecutionRevert hcode
    (amm4Dispatch_swap hsel)
    (amm4Decode_swap_ok hsz100 hbig hcanon) hbody

end Benchmarks.ActAmm4
