import Benchmarks.ActAmm.Swap0EarlyRevert
import Benchmarks.ActAmm.Swap1SourceGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1ErrorRevertTail875 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨2688⟩ (endPtr :: R)
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
  have rd878 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd879 := RD.mload mcost loadval awout rd878
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd883 := evm_run rd879 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd883 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem ammSwap1X_liquidityErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2639⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6135⟩
      [⟨128⟩ + ⟨4⟩, ⟨2688⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      ammSwap0ErrorSelectorMem ammSwap0ErrorSelectorAw ByteArray.empty
      (cA, σ) k' C' := by
  have rd828 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd829⟩ := ammMload64Wide rd828
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  have rd862 := RD.pushConst rd829 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := ammSwap0ErrorSelectorMem
  let awout := ammSwap0ErrorSelectorAw
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd864 := evm_run rd862 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6135 := evm_run rd864 with [
    push1 ⟨4⟩, add, push2 ⟨2688⟩, swap1,
    push2 ⟨6135⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6135⟩

theorem ammSwap1X_insufficientLiquidity
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2629⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq : (solcSlotWord σ I ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd819 := evm_run rd with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd820⟩ := rd819.sload
    (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (ammSwap1AmountWord I)
      (solcSlotWord σ I ⟨5⟩) = ⟨0⟩ := ult_zero hliq
  have rd826 := evm_run rd820 with [
    dup3, lt, push2 ⟨2697⟩,
    jumpiNT (by rw [hlt])]
  obtain ⟨_, _, rd6135⟩ := ammSwap1X_liquidityErrorEnter rd826
  obtain ⟨_, _, rd875⟩ := ammMintErrorStringEncode rd6135
    (by jump_dest) (by simp)
  exact ammSwap1ErrorRevertTail875 rd875 (by simp)

theorem ammSwap1ErrorRevertTail807 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨2620⟩ (endPtr :: R)
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
  have rd810 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd811 := RD.mload mcost loadval awout rd810
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd815 := evm_run rd811 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd815 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem ammSwap1X_positiveErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2571⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6031⟩
      [⟨128⟩ + ⟨4⟩, ⟨2620⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      ammSwap0ErrorSelectorMem ammSwap0ErrorSelectorAw ByteArray.empty
      (cA, σ) k' C' := by
  have rd760 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd761⟩ := ammMload64Wide rd760
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  have rd794 := RD.pushConst rd761 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := ammSwap0ErrorSelectorMem
  let awout := ammSwap0ErrorSelectorAw
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd796 := evm_run rd794 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6031 := evm_run rd796 with [
    push1 ⟨4⟩, add, push2 ⟨2620⟩, swap1,
    push2 ⟨6031⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6031⟩

theorem ammSwap1X_zeroOutput
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2563⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hzero : (ammSwap1AmountWord I).toNat = 0) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have hword : ammSwap1AmountWord I = ⟨0⟩ :=
    uint256_toNat_eq_zero hzero
  have rd758 := evm_run rd with [
    jumpdest, push0, dup3, gt, push2 ⟨2629⟩,
    jumpiNT (by rw [hword]; decide)]
  obtain ⟨_, _, rd6031⟩ := ammSwap1X_positiveErrorEnter rd758
  obtain ⟨_, _, rd807⟩ := ammSwap0PositiveErrorStringEncode rd6031
    (by jump_dest) (by simp)
  exact ammSwap1ErrorRevertTail807 rd807 (by simp)

theorem ammSwap1ZeroOutputBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hzero : (ammSwap1AmountWord I).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hbody := ammSwap1SourceZeroOutput evmS I
    (by simpa [evmS, initState] using hwv) hzero
  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
    hsz68 hsize hbig hcanon hreach
  have hrev := ammSwap1X_zeroOutput rd750 hzero
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

theorem ammSwap1InsufficientLiquidityBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (solcSlotWord σ_evm I ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
      solcSlotWord σ_solm I ⟨5⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliqS : (Solm.EVM.storageLoad evmS
      evmS.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat := by
    change (solcSlotWord σ_solm I ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat
    rw [← hslot5]
    exact hliq
  have hbody := ammSwap1SourceInsufficientLiquidity evmS I
    (by simpa [evmS, initState] using hwv) hpos hliqS
  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
    hsz68 hsize hbig hcanon hreach
  obtain ⟨_, _, rd816⟩ := ammSwap1X_amountPositive rd750 hpos
  have hrev := ammSwap1X_insufficientLiquidity rd816 hliq
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
