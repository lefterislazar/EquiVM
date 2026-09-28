import Benchmarks.ActAmm.ConstructorBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem RD.ammCtorMaskAddress
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {pcReturn w : UInt256}
    {R : List UInt256}
    {mem rdata : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1260⟩ (w :: pcReturn :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains pcReturn = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      pcReturn (UInt256.land solcAddrMask w :: R) mem aw rdata acc k' C' := by
  have rdret := amm_ctor_run rd with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, by simpa only [u256_land_comm] using rdret⟩

theorem RD.ammCtorCleanAddress
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {pcReturn w : UInt256}
    {R : List UInt256}
    {mem rdata : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1291⟩ (w :: pcReturn :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains pcReturn = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      pcReturn (UInt256.land solcAddrMask w :: R) mem aw rdata acc k' C' := by
  have rd1260 := amm_ctor_run rd with [
    jumpdest, push0, push2 ⟨1301⟩, dup3, push2 ⟨1260⟩,
    jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1301⟩ := RD.ammCtorMaskAddress rd1260
    (by amm_ctor_jd) (by simp only [List.length_cons]; omega)
  have rdret := amm_ctor_run rd1301 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, by simpa using rdret⟩

theorem RD.ammCtorEncodeAddressWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {pcReturn addr off : UInt256}
    {R : List UInt256}
    {mem rdata : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1577⟩ (addr :: off :: pcReturn :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains pcReturn = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      pcReturn R
      ((UInt256.toByteArray (UInt256.land solcAddrMask addr)).write 0
        mem off.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32))
      rdata acc k' C' := by
  have rd1291 := amm_ctor_run rd with [
    jumpdest, push2 ⟨1586⟩, dup2, push2 ⟨1291⟩,
    jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1586⟩ := RD.ammCtorCleanAddress rd1291
    (by amm_ctor_jd) (by simp only [List.length_cons]; omega)
  have rd1588 := amm_ctor_run rd1586 with [jumpdest, dup3]
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  let memout := (UInt256.toByteArray (UInt256.land solcAddrMask addr)).write 0
    mem off.toNat 32
  have rd1589 := rd1588.mstore mcost memout awout
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rdret := amm_ctor_run rd1589 with [pop, pop, jump hret]
  exact ⟨_, _, by simpa [awout, memout] using rdret⟩

theorem RD.ammCtorEncodeAddressArg
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {pcReturn addr off : UInt256}
    {R : List UInt256}
    {mem rdata : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1592⟩ (off :: addr :: pcReturn :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains pcReturn = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      pcReturn ((off + ⟨32⟩) :: R)
      ((UInt256.toByteArray (UInt256.land solcAddrMask addr)).write 0
        mem off.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32))
      rdata acc k' C' := by
  have rd1577 := amm_ctor_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨1611⟩, push0, dup4, add, dup5,
    push2 ⟨1577⟩, jump (by amm_ctor_jd)]
  have hzero : off + ⟨0⟩ = off := by rw [u256_add_comm, u256_zero_add]
  rw [hzero] at rd1577
  obtain ⟨_, _, rd1611⟩ := RD.ammCtorEncodeAddressWord rd1577
    (by amm_ctor_jd) (by simp only [List.length_cons]; omega)
  have rdret := amm_ctor_run rd1611 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]
  exact ⟨_, _, by simpa using rdret⟩

end Benchmarks.ActAmm
