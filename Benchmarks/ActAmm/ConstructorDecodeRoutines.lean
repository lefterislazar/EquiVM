import Benchmarks.ActAmm.ConstructorFirstCallDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorDecodeShortReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity base e pcReturn : UInt256}
    {R : List UInt256}
    {mem ret : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcheck : UInt256.slt (UInt256.sub e base) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 14 ≤ 1024)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ (base :: e :: pcReturn :: R) mem aw ret acc k C) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd1626 := amm_ctor_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  rw [hcheck] at rd1626
  have rd1630 := amm_ctor_run rd1626 with [
    push2 ⟨1638⟩, jumpiNT (by decide)]
  have rd1256 := amm_ctor_run rd1630 with [
    push2 ⟨1637⟩, push2 ⟨1256⟩, jump (by amm_ctor_jd)]
  have rd1257 := amm_ctor_run rd1256 with [jumpdest]
  exact rd1257.revertStub (by amm_ctor_decode)
    (by amm_ctor_decode) (by amm_ctor_decode)
    (by simp only [List.length_cons]; omega)

theorem ammCtorDecodeWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity base e pcReturn v : UInt256}
    {R : List UInt256}
    {mem ret : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcheck : UInt256.slt (UInt256.sub e base) ⟨32⟩ = ⟨0⟩)
    (hvalue :
      (if base.toNat ≥ mem.size ∨ base ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding base.toNat 32))) = v)
    (hsame : UInt256.ofNat (MachineState.M aw.toNat base.toNat 32) = aw)
    (hreturn : (D_J (ammCtorCode t0 t1 liquidity) 0).contains pcReturn = true)
    (hov : R.length + 16 ≤ 1024)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ (base :: e :: pcReturn :: R) mem aw ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      pcReturn (v :: R) mem aw ret acc k' C' := by
  have rd1638 := amm_ctor_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨1638⟩, jumpiT (by rw [hcheck]; decide) (by amm_ctor_jd)]
  have rd1381 := amm_ctor_run rd1638 with [
    jumpdest, push0, push2 ⟨1651⟩, dup5, dup3, dup6, add,
    push2 ⟨1381⟩, jump (by amm_ctor_jd)]
  have hzero : base + ⟨0⟩ = base := by rw [u256_add_comm, u256_zero_add]
  rw [hzero] at rd1381
  have rd1384 := amm_ctor_run rd1381 with [jumpdest, push0, dup2]
  have rd1385 := RD.mload 0 v aw rd1384
    (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [hsame]
      omega)
    hvalue hsame
    (by simp only [List.length_cons]; omega)
  have rd1359 := amm_ctor_run rd1385 with [
    swap1, pop, push2 ⟨1395⟩, dup2, push2 ⟨1359⟩,
    jump (by amm_ctor_jd)]
  have rd1350 := amm_ctor_run rd1359 with [
    jumpdest, push2 ⟨1368⟩, dup2, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  have rd1368 := amm_ctor_run rd1350 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by amm_ctor_jd)]
  have rd1378 := amm_ctor_run rd1368 with [
    jumpdest, dup2, eq, push2 ⟨1378⟩,
    jumpiT (by rw [uInt256_eq_self]; decide) (by amm_ctor_jd)]
  have rd1395 := amm_ctor_run rd1378 with [
    jumpdest, pop, jump (by amm_ctor_jd)]
  have rd1651 := amm_ctor_run rd1395 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm_ctor_jd)]
  have rdret := amm_ctor_run rd1651 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump hreturn]
  exact ⟨_, _, by simpa using rdret⟩

end Benchmarks.ActAmm
