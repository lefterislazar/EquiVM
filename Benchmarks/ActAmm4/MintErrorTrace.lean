import Benchmarks.ActAmm4.MintSourceReserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintX_liquidityZeroStart {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1922⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1918 := evm_run h with [push0, dup8, sub]
  have hz : UInt256.sub (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by decide
  rw [hz] at rd1918
  exact ⟨_, _, evm_run rd1918 with [push2 ⟨1980⟩,
    jumpiNT (by decide)]⟩

theorem amm4MintX_errorFreePtr {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 fp : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1922⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1925⟩ [fp, q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1924 := evm_run h with [push1 ⟨64⟩]
  exact amm4Mload64Wide rd1924 (by native_decide) hmem hread haw hbelow
    (by simp)

def amm4MintErrorSelectorWord : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

theorem amm4MintX_errorSelectorStored {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {fp : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨1925⟩ (fp :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨1960⟩ (fp :: R)
      ((UInt256.toByteArray amm4MintErrorSelectorWord).write 0 mem fp.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray amm4MintErrorSelectorWord).write 0 mem fp.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd1958 := RD.pushConst h amm4MintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd := evm_run rd1958 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, rd⟩

theorem amm4MintX_errorEnterEncoder {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {fp : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨1960⟩ (fp :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨5706⟩
      ((fp + ⟨4⟩) :: ⟨1971⟩ :: R) mem aw rdata acc k' C' := by
  have rd := evm_run h with [
    push1 ⟨4⟩, add, push2 ⟨1971⟩, swap1,
    push2 ⟨5706⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) fp] at rd
  exact ⟨_, _, rd⟩

end Benchmarks.ActAmm4
