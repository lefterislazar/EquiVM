import Benchmarks.ActAmm4.SwapRecipientErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapErrorRevertTail2492 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨2492⟩ (endPtr :: R)
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
  have rd2495 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd2496 := RD.mload mcost loadval awout rd2495
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd2500 := evm_run rd2496 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd2500 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem amm4SwapX_recipientErrorFrom2443
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2443⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd2445 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd2446⟩ := amm4Mload64Wide rd2445
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  let memout := (UInt256.toByteArray amm4MintErrorSelectorWord).write 0
    solcFreePtrMem 128 32
  let awout := UInt256.ofNat
    (MachineState.M (UInt256.ofNat 3).toNat 128 32)
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd2479 := RD.pushConst rd2446 amm4MintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  have rd2481 := evm_run rd2479 with [dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5914 := evm_run rd2481 with [
    push1 ⟨4⟩, add, push2 ⟨2492⟩, swap1,
    push2 ⟨5914⟩, jump (by jump_dest)]
  rw [u256_add_comm (⟨4⟩ : UInt256) ⟨128⟩] at rd5914
  obtain ⟨_, _, rd2492⟩ := amm4SwapRecipientErrorStringEncode rd5914
    (by jump_dest) (by simp)
  exact amm4SwapErrorRevertTail2492 rd2492 (by simp)

theorem amm4SwapX_recipient0Revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2268⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (heq : amm4SwapToWord I = amm4MintToken0Word σ I) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2325⟩ := amm4SwapX_token0Address rd
  have hclean : UInt256.land (amm4SwapToWord I) solcAddrMask =
      amm4SwapToWord I := solcAddrMask_clean hcanon
  have heqword : UInt256.eq (amm4SwapToWord I)
      (amm4MintToken0Word σ I) = ⟨1⟩ := by
    rw [heq]
    exact u256_eq_refl _
  have rd2348 := evm_run rd2325 with [dup2, push20 solcAddrMask, and]
  have rd2348' := rd2348
  rw [u256_land_comm solcAddrMask (amm4SwapToWord I), hclean]
    at rd2348'
  have rd2350 := evm_run rd2348' with [eq, iszero]
  have rd2350' := rd2350
  rw [heqword] at rd2350'
  have rd2438 := evm_run rd2350' with [
    dup1, iszero, push2 ⟨2438⟩,
    jumpiT (by decide) (by jump_dest)]
  have rd2443 := evm_run rd2438 with [
    jumpdest, push2 ⟨2501⟩, jumpiNT (by decide)]
  exact amm4SwapX_recipientErrorFrom2443 rd2443

theorem amm4SwapX_recipient1Revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2268⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hne0 : amm4SwapToWord I ≠ amm4MintToken0Word σ I)
    (heq1 : amm4SwapToWord I = amm4MintToken1Word σ I) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2325⟩ := amm4SwapX_token0Address rd
  obtain ⟨_, _, rd2357⟩ :=
    amm4SwapX_token0Distinct rd2325 hcanon hne0
  obtain ⟨_, _, rd2413⟩ := amm4SwapX_token1Address rd2357
  have hclean : UInt256.land (amm4SwapToWord I) solcAddrMask =
      amm4SwapToWord I := solcAddrMask_clean hcanon
  have heqword : UInt256.eq (amm4SwapToWord I)
      (amm4MintToken1Word σ I) = ⟨1⟩ := by
    rw [heq1]
    exact u256_eq_refl _
  have rd2436 := evm_run rd2413 with [dup2, push20 solcAddrMask, and]
  have rd2436' := rd2436
  rw [u256_land_comm solcAddrMask (amm4SwapToWord I), hclean]
    at rd2436'
  have rd2438 := evm_run rd2436' with [eq, iszero]
  have rd2438' := rd2438
  rw [heqword] at rd2438'
  have rd2443 := evm_run rd2438' with [
    jumpdest, push2 ⟨2501⟩, jumpiNT (by decide)]
  exact amm4SwapX_recipientErrorFrom2443 rd2443

end Benchmarks.ActAmm4
