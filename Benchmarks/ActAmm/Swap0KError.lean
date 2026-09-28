import Benchmarks.ActAmm.Swap0ArithmeticSource
import Benchmarks.ActAmm.Swap0ErrorTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def ammSwap0KTextWord : UInt256 := ⟨75 * 2 ^ 248⟩

theorem ammSwap0KTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6905⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret R
      ((UInt256.toByteArray ammSwap0KTextWord).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammSwap0KTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd6939 := RD.pushConst (evm_run h with [jumpdest])
    ammSwap0KTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd := evm_run rd6939 with [
    push0, dup3, add,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hptr0])
      (by rw [hptr0])
      (by rw [hptr0]) (by evm_ov),
    pop, jump hret]
  exact ⟨_, _, rd⟩

theorem ammSwap0KStringPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6945⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray ammSwap0KTextWord).write 0
        ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5941 := evm_run h with [
    jumpdest, push0, push2 ⟨6957⟩, push1 ⟨1⟩,
    dup4, push2 ⟨5941⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6957⟩ := ammErrorWordStore rd5941
    (by jump_dest) (by simp; omega)
  have rd6905 := evm_run rd6957 with [
    jumpdest, swap2, pop, push2 ⟨6968⟩, dup3,
    push2 ⟨6905⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6968⟩ := ammSwap0KTextStore rd6905
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, evm_run rd6968 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]⟩

def ammSwap0KPayloadMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (ammSwap0ErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def ammSwap0KFinalMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammSwap0KTextWord).write 0
    (ammSwap0KPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

theorem ammSwap0KStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6979⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (ammSwap0KFinalMem ptr mem) (ammSwap0ErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := ammSwap0ErrorHeaderMem ptr mem
  let aw1 := ammSwap0ErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6993 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6993
  have rd6994 := evm_run rd6993 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6945 := evm_run rd6994 with [
    push2 ⟨7002⟩, dup2, push2 ⟨6945⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd7002⟩ := ammSwap0KStringPayload rd6945
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, by
    simpa only [ammSwap0KFinalMem, ammSwap0KPayloadMem,
      ammSwap0ErrorFinalAw, ammSwap0ErrorPayloadAw,
      ammSwap0ErrorHeaderAw] using
      (evm_run rd7002 with [
        jumpdest, swap1, pop, swap2, swap1, pop, jump hret])⟩

theorem ammSwap0KRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨1766⟩ (endPtr :: R)
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
  have rd1770 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd1771 := RD.mload mcost loadval awout rd1770
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd1775 := evm_run rd1771 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd1775 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem ammSwap0X_kGuardReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn quotient : UInt256}
    {mem ret : ByteArray} {aw fp : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1709⟩
      [quotient, amountIn, q1, q0,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      mem aw ret acc k C)
    (hbad : quotient.toNat < (ammSwap0AmountWord I).toNat)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding 64 32))) = fp) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hgt : UInt256.gt (ammSwap0AmountWord I) quotient = ⟨1⟩ :=
    ugt_one hbad
  have rd1717 := evm_run rd with [
    jumpdest, dup6, gt, iszero, push2 ⟨1775⟩,
    jumpiNT (by rw [hgt]; decide)]
  have rd1719 := evm_run rd1717 with [push1 ⟨64⟩]
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  let mcost := Cₘ aw1 - Cₘ aw
  have rd1720 := RD.mload mcost fp aw1 rd1719
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by simpa using hfp) (by rfl) (by simp)
  have rd1753 := RD.pushConst rd1720 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := (UInt256.toByteArray ammMintErrorSelectorWord).write 0
    mem fp.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mcost2 := Cₘ awout - Cₘ aw1
  have rd1755 := evm_run rd1753 with [
    dup2,
    raw mstore mcost2 memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6979 := evm_run rd1755 with [
    push1 ⟨4⟩, add, push2 ⟨1766⟩, swap1,
    push2 ⟨6979⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1766⟩ := ammSwap0KStringEncode rd6979
    (by jump_dest) (by simp)
  exact ammSwap0KRevertTail rd1766 (by simp)

theorem ammSwap0Balance1DecodeMem_read64 (I : ExecutionEnv)
    (out ret ret1 : ByteArray) :
    (ammSwap0Balance1DecodeMem I out ret ret1).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.add
        (ammSwap0Balance1FreePtr out ret)
        (ammMintReturndataRounded ret1)) := by
  unfold ammSwap0Balance1DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

theorem ammSwap0X_kGuardRevertsDecoded
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 amountIn quotient : UInt256}
    {out ret ret1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1709⟩
      [quotient, amountIn, q1, q0,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1DecodeMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k C)
    (hbad : quotient.toNat < (ammSwap0AmountWord I).toNat) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  let aw := ammSwap0Balance1CalldataWords out ret
  let fp := UInt256.add (ammSwap0Balance1FreePtr out ret)
    (ammMintReturndataRounded ret1)
  have haw : aw.toNat = 6 + (out.size + 31) / 32 +
      (ret.size + 31) / 32 := by
    simpa only [aw] using
      ammSwap0Balance1CalldataWords_toNat out ret hlo hbound hretLo hretBound
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle : (out.size + 31) / 32 ≤ out.size + 31 := Nat.div_le_self _ _
    have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
        UInt256.size := by norm_num [UInt256.size]
    omega
  have hmem : 64 < (ammSwap0Balance1DecodeMem I out ret ret1).size := by
    have hsz := ammSwap0Balance1DecodeMem_size_ge I
      hlo hbound hretBound hretSize
    have hptr := (ammSwap0Balance1FreePtr_bounds out ret
      hlo hbound hretBound).1
    change 160 ≤ (ammSwap0Balance1FreePtr out ret).toNat at hptr
    omega
  have hfp := mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
    (by simpa using hmem)
    (ammActiveWords64 aw hawlo hawfit)
    (by simpa only [fp] using
      ammSwap0Balance1DecodeMem_read64 I out ret ret1)
  exact ammSwap0X_kGuardReverts rd hbad hfp

end Benchmarks.ActAmm
