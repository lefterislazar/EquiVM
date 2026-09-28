import Benchmarks.ActAmm.Swap1Proof

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

/-- The swap1 wrapper, entered at PC 314, refines its Solm transition. -/
theorem ammSwap1BodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I :=
  ammSwap1BodyCoreProof hcode hsize hperm hwv hsel hreach hAccounts

end Benchmarks.ActAmm
