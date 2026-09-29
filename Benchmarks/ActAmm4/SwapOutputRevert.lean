import Benchmarks.ActAmm4.SwapOutputErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapErrorRevertTail2178 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨2178⟩ (endPtr :: R)
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
  have rd2181 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd2182 := RD.mload mcost loadval awout rd2181
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd2186 := evm_run rd2182 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd2186 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem amm4SwapX_outputErrorFrom2129
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2129⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd2131 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd2132⟩ := amm4Mload64Wide rd2131
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  let memout := (UInt256.toByteArray amm4MintErrorSelectorWord).write 0
    solcFreePtrMem 128 32
  let awout := UInt256.ofNat
    (MachineState.M (UInt256.ofNat 3).toNat 128 32)
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd2165 := RD.pushConst rd2132 amm4MintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd2167 := evm_run rd2165 with [dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5810 := evm_run rd2167 with [
    push1 ⟨4⟩, add, push2 ⟨2178⟩, swap1,
    push2 ⟨5810⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) ⟨128⟩] at rd5810
  obtain ⟨_, _, rd2178⟩ := amm4SwapOutputErrorStringEncode rd5810
    (by jump_dest) (by simp)
  exact amm4SwapErrorRevertTail2178 rd2178 (by simp)

theorem amm4SwapX_zeroOutputRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2111⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hzero0 : (amm4SwapAmount0Word I).toNat = 0)
    (hzero1 : (amm4SwapAmount1Word I).toNat = 0) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have hgt0 : UInt256.gt (amm4SwapAmount0Word I) ⟨0⟩ = ⟨0⟩ :=
    ugt_zero (by simpa using hzero0)
  have hgt1 : UInt256.gt (amm4SwapAmount1Word I) ⟨0⟩ = ⟨0⟩ :=
    ugt_zero (by simpa using hzero1)
  have rd2124 := evm_run rd with [
    jumpdest, push0, dup4, gt, dup1, push2 ⟨2124⟩,
    jumpiNT (by rw [hgt0]), pop, push0, dup3, gt]
  have rd2124' := rd2124
  rw [hgt1] at rd2124'
  have rd2129 := evm_run rd2124' with [
    jumpdest, push2 ⟨2187⟩, jumpiNT (by decide)]
  exact amm4SwapX_outputErrorFrom2129 rd2129

end Benchmarks.ActAmm4
