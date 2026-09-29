import Benchmarks.ActAmm4.ConstructorReserve1Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorReturnMem
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (mem : ByteArray) : ByteArray :=
  (amm4CtorCode t0 t1 liquidity).write 1858 mem 0 6330

theorem amm4CtorReturnMem_read
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (mem : ByteArray) :
    (amm4CtorReturnMem t0 t1 liquidity mem).readWithPadding 0 6330 =
      amm4Bytecode := by
  unfold amm4CtorReturnMem
  rw [write0_read_back_from_gen (amm4CtorCode t0 t1 liquidity) mem 1858 6330
    (by decide) (by rw [amm4CtorCode_size]; omega) (by decide)]
  exact amm4CtorCode_runtime_window t0 t1 liquidity

theorem amm4CtorReturnRuntime
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem ret : ByteArray} {aw : UInt256} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1252⟩ [] mem aw ret (cA, σ) k C) :
    RDret (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      (cA, σ) amm4Bytecode := by
  have rd1845 := amm4_ctor_run rd with [
    push2 ⟨1845⟩, jump (by amm4_ctor_jd)]
  have rd1853 := amm4_ctor_run rd1845 with [
    jumpdest, push2 ⟨6330⟩, dup1, push2 ⟨1858⟩, push0]
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 6330)
  have rd1854 := rd1853.codecopy
    (Cₘ awout - Cₘ aw)
    (amm4CtorReturnMem t0 t1 liquidity mem)
    awout
    (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awout, show (⟨6330⟩ : UInt256).toNat = 6330 from by decide])
    (by rfl)
    (by simp [awout, show (⟨6330⟩ : UInt256).toNat = 6330 from by decide])
    (by evm_ov)
  have rd1856 := amm4_ctor_run rd1854 with [push0]
  exact rd1856.ret
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 6330)) - Cₘ awout)
    amm4Bytecode (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awout, show (⟨6330⟩ : UInt256).toNat = 6330 from by decide])
    (amm4CtorReturnMem_read t0 t1 liquidity mem) (by evm_ov)

end Benchmarks.ActAmm4
