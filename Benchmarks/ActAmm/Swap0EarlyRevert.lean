import Benchmarks.ActAmm.Swap0RecipientRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0ErrorRevertTail875 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨875⟩ (endPtr :: R)
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

theorem ammSwap0X_liquidityErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨826⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6135⟩
      [⟨128⟩ + ⟨4⟩, ⟨875⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
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
    push1 ⟨4⟩, add, push2 ⟨875⟩, swap1,
    push2 ⟨6135⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6135⟩

theorem ammSwap0X_insufficientLiquidity
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hliq : (solcSlotWord σ I ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have rd819 := evm_run rd with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, rd820⟩ := rd819.sload
    (by native_decide) (by evm_ov)
  have hlt : UInt256.lt (ammSwap0AmountWord I)
      (solcSlotWord σ I ⟨6⟩) = ⟨0⟩ := ult_zero hliq
  have rd826 := evm_run rd820 with [
    dup3, lt, push2 ⟨884⟩,
    jumpiNT (by rw [hlt])]
  obtain ⟨_, _, rd6135⟩ := ammSwap0X_liquidityErrorEnter rd826
  obtain ⟨_, _, rd875⟩ := ammMintErrorStringEncode rd6135
    (by jump_dest) (by simp)
  exact ammSwap0ErrorRevertTail875 rd875 (by simp)

def ammSwap0PositiveErrorTextWord : UInt256 :=
  ⟨33213987989631693067883787898815107056615725171503134575597122139604520009728⟩

theorem ammSwap0PositiveErrorTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5957⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret R
      ((UInt256.toByteArray ammSwap0PositiveErrorTextWord).write 0
        mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammSwap0PositiveErrorTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd5991 := RD.pushConst (evm_run h with [jumpdest])
    ammSwap0PositiveErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  exact ⟨_, _, evm_run rd5991 with [
    push0, dup3, add,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hptr0])
      (by rw [hptr0])
      (by rw [hptr0]) (by evm_ov),
    pop, jump hret]⟩

theorem ammSwap0PositiveErrorPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5997⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray ammSwap0PositiveErrorTextWord).write 0
        ((UInt256.toByteArray (⟨26⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5941 := evm_run h with [
    jumpdest, push0, push2 ⟨6009⟩, push1 ⟨26⟩,
    dup4, push2 ⟨5941⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6009⟩ := ammErrorWordStore rd5941
    (by jump_dest) (by simp; omega)
  have rd5957 := evm_run rd6009 with [
    jumpdest, swap2, pop, push2 ⟨6020⟩, dup3,
    push2 ⟨5957⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6020⟩ := ammSwap0PositiveErrorTextStore rd5957
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, evm_run rd6020 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]⟩

def ammSwap0PositiveErrorHeaderMem
    (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0
    mem ptr.toNat 32

def ammSwap0PositiveErrorPayloadMem
    (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨26⟩ : UInt256)).write 0
    (ammSwap0PositiveErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def ammSwap0PositiveErrorFinalMem
    (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammSwap0PositiveErrorTextWord).write 0
    (ammSwap0PositiveErrorPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

def ammSwap0PositiveErrorHeaderAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def ammSwap0PositiveErrorPayloadAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammSwap0PositiveErrorHeaderAw ptr aw).toNat
    (ptr + ⟨32⟩).toNat 32)

def ammSwap0PositiveErrorFinalAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammSwap0PositiveErrorPayloadAw ptr aw).toNat
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32)

theorem ammSwap0PositiveErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6031⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (ammSwap0PositiveErrorFinalMem ptr mem)
      (ammSwap0PositiveErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := ammSwap0PositiveErrorHeaderMem ptr mem
  let aw1 := ammSwap0PositiveErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6045 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6045
  have rd6046 := evm_run rd6045 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5997 := evm_run rd6046 with [
    push2 ⟨6054⟩, dup2, push2 ⟨5997⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6054⟩ := ammSwap0PositiveErrorPayload rd5997
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, evm_run rd6054 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]⟩

theorem ammSwap0ErrorRevertTail807 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨807⟩ (endPtr :: R)
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

theorem ammSwap0X_positiveErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨758⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6031⟩
      [⟨128⟩ + ⟨4⟩, ⟨807⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
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
    push1 ⟨4⟩, add, push2 ⟨807⟩, swap1,
    push2 ⟨6031⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6031⟩

theorem ammSwap0X_zeroOutput
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨750⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hzero : (ammSwap0AmountWord I).toNat = 0) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have hword : ammSwap0AmountWord I = ⟨0⟩ :=
    uint256_toNat_eq_zero hzero
  have rd758 := evm_run rd with [
    jumpdest, push0, dup3, gt, push2 ⟨816⟩,
    jumpiNT (by rw [hword]; decide)]
  obtain ⟨_, _, rd6031⟩ := ammSwap0X_positiveErrorEnter rd758
  obtain ⟨_, _, rd807⟩ := ammSwap0PositiveErrorStringEncode rd6031
    (by jump_dest) (by simp)
  exact ammSwap0ErrorRevertTail807 rd807 (by simp)

theorem ammSwap0ZeroOutputBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨208⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hzero : (ammSwap0AmountWord I).toNat = 0) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hbody := ammSwap0SourceZeroOutput evmS I
    (by simpa [evmS, initState] using hwv) hzero
  obtain ⟨_, _, rd750⟩ := ammSwap0X_decoded
    hsz68 hsize hbig hcanon hreach
  have hrev := ammSwap0X_zeroOutput rd750 hzero
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap0 hsel)
    (ammDecode_swap0_ok hsz68 hbig hcanon) hbody

theorem ammSwap0InsufficientLiquidityBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨208⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (solcSlotWord σ_evm I ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
      solcSlotWord σ_solm I ⟨6⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hliqS : (Solm.EVM.storageLoad evmS
      evmS.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat := by
    change (solcSlotWord σ_solm I ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat
    rw [← hslot6]
    exact hliq
  have hbody := ammSwap0SourceInsufficientLiquidity evmS I
    (by simpa [evmS, initState] using hwv) hpos hliqS
  obtain ⟨_, _, rd750⟩ := ammSwap0X_decoded
    hsz68 hsize hbig hcanon hreach
  obtain ⟨_, _, rd816⟩ := ammSwap0X_amountPositive rd750 hpos
  have hrev := ammSwap0X_insufficientLiquidity rd816 hliq
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap0 hsel)
    (ammDecode_swap0_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
