import Benchmarks.ActAmm4.SwapGuardTrace
import Benchmarks.ActAmm4.MintErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapErrorRevertTail2259 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨2259⟩ (endPtr :: R)
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
  have rd2262 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd2263 := RD.mload mcost loadval awout rd2262
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd2267 := evm_run rd2263 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd2267 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem amm4SwapX_liquidityErrorFrom2210
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2210⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd2212 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd2213⟩ := amm4Mload64Wide rd2212
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  let memout := (UInt256.toByteArray amm4MintErrorSelectorWord).write 0
    solcFreePtrMem 128 32
  let awout := UInt256.ofNat
    (MachineState.M (UInt256.ofNat 3).toNat 128 32)
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd2246 := RD.pushConst rd2213 amm4MintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd2248 := evm_run rd2246 with [dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5706 := evm_run rd2248 with [
    push1 ⟨4⟩, add, push2 ⟨2259⟩, swap1,
    push2 ⟨5706⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) ⟨128⟩] at rd5706
  obtain ⟨_, _, rd2259⟩ := amm4MintErrorStringEncode rd5706
    (by jump_dest) (by simp)
  exact amm4SwapErrorRevertTail2259 rd2259 (by simp)

theorem amm4SwapX_liquidity0Revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2187⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq : (solcSlotWord σ I ⟨5⟩).toNat ≤
      (amm4SwapAmount0Word I).toNat) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd2190 := evm_run rd with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd2191⟩ := rd2190.sload
    (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (amm4SwapAmount0Word I)
      (solcSlotWord σ I ⟨5⟩) = ⟨0⟩ := ult_zero hliq
  have rd2205 := evm_run rd2191 with [
    dup4, lt, dup1, iszero, push2 ⟨2205⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest)]
  have rd2205' := rd2205
  rw [hlt] at rd2205'
  have rd2210 := evm_run rd2205' with [
    jumpdest, push2 ⟨2268⟩, jumpiNT (by decide)]
  exact amm4SwapX_liquidityErrorFrom2210 rd2210

theorem amm4SwapX_liquidity1Revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2187⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (solcSlotWord σ I ⟨5⟩).toNat)
    (hliq1 : (solcSlotWord σ I ⟨6⟩).toNat ≤
      (amm4SwapAmount1Word I).toNat) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd2190 := evm_run rd with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd2191⟩ := rd2190.sload
    (by native_decide) (by evm_ov)
  have hlt0 : UInt256.lt (amm4SwapAmount0Word I)
      (solcSlotWord σ I ⟨5⟩) = ⟨1⟩ := ult_one hliq0
  have rd2200 := evm_run rd2191 with [
    dup4, lt, dup1, iszero, push2 ⟨2205⟩,
    jumpiNT (by rw [hlt0]; decide), pop, push1 ⟨6⟩]
  obtain ⟨_, _, rd2203⟩ := rd2200.sload
    (by native_decide) (by evm_ov)
  have hlt1 : UInt256.lt (amm4SwapAmount1Word I)
      (solcSlotWord σ I ⟨6⟩) = ⟨0⟩ := ult_zero hliq1
  have rd2205 := evm_run rd2203 with [dup3, lt]
  rw [hlt1] at rd2205
  have rd2210 := evm_run rd2205 with [
    jumpdest, push2 ⟨2268⟩, jumpiNT (by decide)]
  exact amm4SwapX_liquidityErrorFrom2210 rd2210

end Benchmarks.ActAmm4
