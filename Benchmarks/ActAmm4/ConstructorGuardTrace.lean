import Benchmarks.ActAmm4.ConstructorErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

def amm4CtorErrorSelectorWord : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

theorem amm4CtorProductEqualityMismatchReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity product square : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨647⟩ [square, product, liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hne : square ≠ product) :
    RDrev (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd650 := amm4_ctor_run rd with [jumpdest, eq]
  rw [u256_eq_of_ne hne] at rd650
  have rd653 := amm4_ctor_run rd650 with [push2 ⟨711⟩, jumpiNT (by decide)]
  let off : UInt256 := ⟨64⟩
  let fp : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost1 := Cₘ aw1 - Cₘ aw
  have rd656 := amm4_ctor_run rd653 with [push1 ⟨64⟩]
  have rd657 := RD.mload mcost1 fp aw1 rd656
    (by amm4_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd689 := rd657.pushConst amm4CtorErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by amm4_ctor_decode) (by evm_ov)
  let mem2 := (UInt256.toByteArray amm4CtorErrorSelectorWord).write 0 mem fp.toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mcost2 := Cₘ aw2 - Cₘ aw1
  have rd691 := amm4_ctor_run rd689 with [dup2]
  have rd692 := rd691.mstore mcost2 mem2 aw2
    (by amm4_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by evm_ov)
  have rd1815 := amm4_ctor_run rd692 with [
    push1 ⟨4⟩, add, push2 ⟨702⟩, swap1,
    push2 ⟨1815⟩, jump (by amm4_ctor_jd)]
  obtain ⟨_, _, rd702⟩ := RD.amm4CtorErrorEncode rd1815
    (by amm4_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.amm4CtorErrorRevertTail rd702
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.ActAmm4
