import Benchmarks.ActAmm.MintErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammMintX_liquidityZero {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 fp : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4046⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    RDrev ammBytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd4053⟩ := ammMintX_liquidityZeroStart h
  obtain ⟨_, _, rd4056⟩ := ammMintX_errorFreePtr rd4053 hmem hread haw hbelow
  obtain ⟨_, _, rd4091⟩ := ammMintX_errorSelectorStored rd4056 (by simp)
  obtain ⟨_, _, rd6135⟩ := ammMintX_errorEnterEncoder rd4091 (by simp)
  obtain ⟨_, _, rd4102⟩ := ammMintErrorStringEncode rd6135
    (by jump_dest) (by simp)
  exact ammMintErrorRevertTail rd4102 (by simp)

end Benchmarks.ActAmm
