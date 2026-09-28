import Benchmarks.ActAmm.MintSourceReserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammMintX_liquidityZeroStart {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4046⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      mem aw rdata (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4053⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd4049 := evm_run h with [push0, dup8, sub]
  have hz : UInt256.sub (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ := by decide
  rw [hz] at rd4049
  exact ⟨_, _, evm_run rd4049 with [push2 ⟨4111⟩,
    jumpiNT (by decide)]⟩

theorem ammMintX_errorFreePtr {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 fp : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4053⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    ∃ k' C', RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4056⟩ [fp, q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd4055 := evm_run h with [push1 ⟨64⟩]
  exact ammMload64Wide rd4055 (by native_decide) hmem hread haw hbelow
    (by simp)

def ammMintErrorSelectorWord : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

theorem ammMintX_errorSelectorStored {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {fp : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨4056⟩ (fp :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨4091⟩ (fp :: R)
      ((UInt256.toByteArray ammMintErrorSelectorWord).write 0 mem fp.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammMintErrorSelectorWord).write 0 mem fp.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd4089 := RD.pushConst h ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd := evm_run rd4089 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  exact ⟨_, _, rd⟩

theorem ammMintX_errorEnterEncoder {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {fp : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨4091⟩ (fp :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨6135⟩
      ((fp + ⟨4⟩) :: ⟨4102⟩ :: R) mem aw rdata acc k' C' := by
  have rd := evm_run h with [
    push1 ⟨4⟩, add, push2 ⟨4102⟩, swap1,
    push2 ⟨6135⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) fp] at rd
  exact ⟨_, _, rd⟩

end Benchmarks.ActAmm
