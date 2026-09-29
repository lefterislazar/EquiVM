import Benchmarks.ActAmm4.SwapKErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapErrorRevertTail3397 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨3397⟩ (endPtr :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd3400 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd3401 := RD.mload mcost loadval awout rd3400
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd3405 := evm_run rd3401 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd3405 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem amm4SwapX_kErrorFrom3348
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare ×
      AccountMap} {k C : Nat}
    (rd : RD amm4Bytecode ee g s0 ⟨3348⟩ R
      mem aw rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let ptr : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding off.toNat 32))
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let cost1 := Cₘ aw1 - Cₘ aw
  have rd3350 := evm_run rd with [push1 ⟨64⟩]
  have rd3351 := RD.mload cost1 ptr aw1 rd3350
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  let mem2 := (UInt256.toByteArray amm4MintErrorSelectorWord).write 0
    mem ptr.toNat 32
  let aw2 := UInt256.ofNat
    (MachineState.M aw1.toNat ptr.toNat 32)
  let cost2 := Cₘ aw2 - Cₘ aw1
  have rd3384 := RD.pushConst rd3351 amm4MintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd3386 := evm_run rd3384 with [dup2,
    raw mstore cost2 mem2 aw2 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs,
          hst, List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6246 := evm_run rd3386 with [
    push1 ⟨4⟩, add, push2 ⟨3397⟩, swap1,
    push2 ⟨6246⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) ptr] at rd6246
  obtain ⟨_, _, rd3397⟩ :=
    amm4SwapKErrorStringEncode rd6246
      (by jump_dest) (by simp; omega)
  exact amm4SwapErrorRevertTail3397 rd3397 (by simp; omega)

theorem amm4SwapX_kGuardRevert
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 a0 a1 oldProduct newProduct : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3341⟩
      [newProduct, oldProduct, a1, a0,
        v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hunder : newProduct.toNat < oldProduct.toNat) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hlt : UInt256.lt newProduct oldProduct = ⟨1⟩ :=
    ult_one hunder
  have rd3348 := evm_run rd with [
    jumpdest, lt, iszero, push2 ⟨3406⟩,
    jumpiNT (by rw [hlt]; decide)]
  exact amm4SwapX_kErrorFrom3348 rd3348
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.ActAmm4
