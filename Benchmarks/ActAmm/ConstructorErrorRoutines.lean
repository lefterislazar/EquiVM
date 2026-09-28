import Benchmarks.ActAmm.ConstructorArithmeticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

def ammCtorErrorTextWord : UInt256 :=
  ⟨33214008156304899519736510927038612235644837243326969087662075900781811204096⟩

theorem RD.ammCtorErrorWordStore
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {ptr val ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1725⟩ (ptr :: val :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret ((ptr + ⟨32⟩) :: R)
      ((UInt256.toByteArray val).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray val).write 0 mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd := amm_ctor_run h with [
    jumpdest, push0, dup3, dup3,
    raw mstore mcost memout awout (by amm_ctor_decode)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop,
    swap3, swap2, pop, pop, jump hret]
  exact ⟨_, _, rd⟩

theorem RD.ammCtorErrorTextStore
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1741⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret R
      ((UInt256.toByteArray ammCtorErrorTextWord).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammCtorErrorTextWord).write 0 mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd1775 := (amm_ctor_run h with [jumpdest]).pushConst ammCtorErrorTextWord
    (width := 32) (op := .PUSH32) (by decide) (by amm_ctor_decode) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd := amm_ctor_run rd1775 with [
    push0, dup3, add,
    raw mstore mcost memout awout (by amm_ctor_decode)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hptr0])
      (by rw [hptr0]) (by rw [hptr0]) (by evm_ov),
    pop, jump hret]
  exact ⟨_, _, rd⟩

theorem RD.ammCtorErrorPayload
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1781⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray ammCtorErrorTextWord).write 0
        ((UInt256.toByteArray (⟨25⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd1725 := amm_ctor_run h with [
    jumpdest, push0, push2 ⟨1793⟩, push1 ⟨25⟩,
    dup4, push2 ⟨1725⟩, jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1793⟩ := RD.ammCtorErrorWordStore rd1725
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1741 := amm_ctor_run rd1793 with [
    jumpdest, swap2, pop, push2 ⟨1804⟩, dup3,
    push2 ⟨1741⟩, jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1804⟩ := RD.ammCtorErrorTextStore rd1741
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, amm_ctor_run rd1804 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]⟩

def ammCtorErrorHeaderMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0 mem ptr.toNat 32

def ammCtorErrorPayloadMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
    (ammCtorErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def ammCtorErrorFinalMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammCtorErrorTextWord).write 0
    (ammCtorErrorPayloadMem ptr mem) ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

def ammCtorErrorHeaderAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def ammCtorErrorPayloadAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammCtorErrorHeaderAw ptr aw).toNat
    (ptr + ⟨32⟩).toNat 32)

def ammCtorErrorFinalAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammCtorErrorPayloadAw ptr aw).toNat
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32)

theorem RD.ammCtorErrorEncode
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1815⟩ (ptr :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J (ammCtorCode t0 t1 liquidity) 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ret (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (ammCtorErrorFinalMem ptr mem) (ammCtorErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := ammCtorErrorHeaderMem ptr mem
  let aw1 := ammCtorErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd1829 := amm_ctor_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd1829
  have rd1830 := amm_ctor_run rd1829 with [
    raw mstore mcost mem1 aw1 (by amm_ctor_decode)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd1781 := amm_ctor_run rd1830 with [
    push2 ⟨1838⟩, dup2, push2 ⟨1781⟩, jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1838⟩ := RD.ammCtorErrorPayload rd1781
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, amm_ctor_run rd1838 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]⟩

theorem RD.ammCtorErrorRevertTail
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {k C : Nat} {endPtr : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨702⟩ (endPtr :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd705 := amm_ctor_run h with [jumpdest, push1 ⟨64⟩]
  have rd706 := RD.mload mcost loadval awout rd705
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp only [List.length_cons]; omega)
  have rd710 := amm_ctor_run rd706 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd710 (by amm_ctor_decode)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

end Benchmarks.ActAmm
