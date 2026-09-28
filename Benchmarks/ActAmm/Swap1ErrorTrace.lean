import Benchmarks.ActAmm.Swap0ErrorTrace
import Benchmarks.ActAmm.Swap1SourceGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_recipientErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2872⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6239⟩
      [⟨128⟩ + ⟨4⟩, ⟨2921⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      ammSwap0ErrorSelectorMem ammSwap0ErrorSelectorAw ByteArray.empty
      (cA, σ) k' C' := by
  have rd1061 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd1062⟩ := ammMload64Wide rd1061
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  have rd1095 := RD.pushConst rd1062 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := ammSwap0ErrorSelectorMem
  let awout := ammSwap0ErrorSelectorAw
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd1097 := evm_run rd1095 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6239 := evm_run rd1097 with [
    push1 ⟨4⟩, add, push2 ⟨2921⟩, swap1,
    push2 ⟨6239⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6239⟩

theorem ammSwap1ErrorRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨2921⟩ (endPtr :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd1111 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd1112 := RD.mload mcost loadval awout rd1111
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd1116 := evm_run rd1112 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd1116 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem ammSwap1X_recipientRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2872⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6239⟩ := ammSwap1X_recipientErrorEnter rd
  obtain ⟨_, _, rd1108⟩ := ammSwap0ErrorStringEncode rd6239
    (by jump_dest) (by simp)
  exact ammSwap1ErrorRevertTail rd1108 (by simp)

end Benchmarks.ActAmm
