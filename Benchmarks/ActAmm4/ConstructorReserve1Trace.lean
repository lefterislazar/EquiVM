import Benchmarks.ActAmm4.ConstructorFourthCallDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000

def amm4CtorReserve1Map (I : ExecutionEnv) (σ : AccountMap)
    (reserve1 : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨6⟩ reserve1

theorem amm4CtorReserve1Stored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity reserve1 : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1242⟩ [reserve1, liquidity, EVM.word t1, EVM.word t0]
      mem aw ret (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1252⟩ [] mem aw ret
      (cA, amm4CtorReserve1Map I σ reserve1) k' C' := by
  have rd1247 := amm4_ctor_run rd with [jumpdest, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd1248⟩ := rd1247.sstore hperm
    (by amm4_ctor_decode) (by evm_ov)
  exact ⟨_, _, by simpa only [amm4CtorReserve1Map] using
    (amm4_ctor_run rd1248 with [pop, pop, pop, pop])⟩

end Benchmarks.ActAmm4
