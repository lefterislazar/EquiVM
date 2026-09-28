import Benchmarks.ActAmm.ConstructorReserve1Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorReturnMem
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (mem : ByteArray) : ByteArray :=
  (ammCtorCode t0 t1 liquidity).write 1858 mem 0 7063

theorem ammCtorReturnMem_read
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (mem : ByteArray) :
    (ammCtorReturnMem t0 t1 liquidity mem).readWithPadding 0 7063 =
      ammBytecode := by
  unfold ammCtorReturnMem
  rw [write0_read_back_from_gen (ammCtorCode t0 t1 liquidity) mem 1858 7063
    (by decide) (by rw [ammCtorCode_size]; omega) (by decide)]
  exact ammCtorCode_runtime_window t0 t1 liquidity

theorem ammCtorReturnRuntime
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem ret : ByteArray} {aw : UInt256} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1252⟩ [] mem aw ret (cA, σ) k C) :
    RDret (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      (cA, σ) ammBytecode := by
  have rd1845 := amm_ctor_run rd with [
    push2 ⟨1845⟩, jump (by amm_ctor_jd)]
  have rd1853 := amm_ctor_run rd1845 with [
    jumpdest, push2 ⟨7063⟩, dup1, push2 ⟨1858⟩, push0]
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 7063)
  have rd1854 := rd1853.codecopy
    (Cₘ awout - Cₘ aw)
    (ammCtorReturnMem t0 t1 liquidity mem)
    awout
    (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awout, show (⟨7063⟩ : UInt256).toNat = 7063 from by decide])
    (by rfl)
    (by simp [awout, show (⟨7063⟩ : UInt256).toNat = 7063 from by decide])
    (by evm_ov)
  have rd1856 := amm_ctor_run rd1854 with [push0]
  exact rd1856.ret
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 7063)) - Cₘ awout)
    ammBytecode (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awout, show (⟨7063⟩ : UInt256).toNat = 7063 from by decide])
    (ammCtorReturnMem_read t0 t1 liquidity mem) (by evm_ov)

end Benchmarks.ActAmm
