import Benchmarks.ActAmm4.MintErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintX_liquidityZero {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 fp : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd1922⟩ := amm4MintX_liquidityZeroStart h
  obtain ⟨_, _, rd1925⟩ := amm4MintX_errorFreePtr rd1922 hmem hread haw hbelow
  obtain ⟨_, _, rd1960⟩ := amm4MintX_errorSelectorStored rd1925 (by simp)
  obtain ⟨_, _, rd5706⟩ := amm4MintX_errorEnterEncoder rd1960 (by simp)
  obtain ⟨_, _, rd1971⟩ := amm4MintErrorStringEncode rd5706
    (by jump_dest) (by simp)
  exact amm4MintErrorRevertTail rd1971 (by simp)

end Benchmarks.ActAmm4
