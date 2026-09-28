import Benchmarks.ActAmm.Swap0InputError
import Benchmarks.ActAmm.Swap1KError

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1InputRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨3458⟩ (endPtr :: R)
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


theorem ammSwap1X_inputGuardReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256}
    {mem ret : ByteArray} {aw fp : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3400⟩
      [q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw ret acc k C)
    (hbad : q1.toNat ≤ (solcSlotWord acc.2 I ⟨6⟩).toNat)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding 64 32))) = fp) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1589 := evm_run rd with [push1 ⟨6⟩]
  obtain ⟨_, _, rd1590⟩ := rd1589.sload
    (by native_decide) (by evm_ov)
  have hgt : UInt256.gt q1 (solcSlotWord acc.2 I ⟨6⟩) = ⟨0⟩ :=
    ugt_zero hbad
  have rd1596 := evm_run rd1590 with [
    dup2, gt, push2 ⟨3467⟩, jumpiNT (by rw [hgt])]
  have rd1598 := evm_run rd1596 with [push1 ⟨64⟩]
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  let mcost := Cₘ aw1 - Cₘ aw
  have rd1599 := RD.mload mcost fp aw1 rd1598
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by simpa using hfp) (by rfl) (by simp)
  have rd1632 := RD.pushConst rd1599 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := (UInt256.toByteArray ammMintErrorSelectorWord).write 0
    mem fp.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mcost2 := Cₘ awout - Cₘ aw1
  have rd1634 := evm_run rd1632 with [
    dup2,
    raw mstore mcost2 memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6570 := evm_run rd1634 with [
    push1 ⟨4⟩, add, push2 ⟨3458⟩, swap1,
    push2 ⟨6570⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1645⟩ := ammSwap0InputStringEncode rd6570
    (by jump_dest) (by simp)
  exact ammSwap1InputRevertTail rd1645 (by simp)

theorem ammSwap1X_inputGuardRevertsDecoded
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256}
    {out ret ret1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3400⟩
      [q1, q0, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1DecodeMem I out ret ret1)
      (ammSwap1Balance1CalldataWords out ret) ret1 acc k C)
    (hbad : q1.toNat ≤ (solcSlotWord acc.2 I ⟨6⟩).toNat) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  let aw := ammSwap1Balance1CalldataWords out ret
  let fp := UInt256.add (ammSwap1Balance1FreePtr out ret)
    (ammMintReturndataRounded ret1)
  have haw : aw.toNat = 6 + (out.size + 31) / 32 +
      (ret.size + 31) / 32 := by
    simpa only [aw] using
      ammSwap1Balance1CalldataWords_toNat out ret hlo hbound hretLo hretBound
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle : (out.size + 31) / 32 ≤ out.size + 31 := Nat.div_le_self _ _
    have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
        UInt256.size := by norm_num [UInt256.size]
    omega
  have hmem : 64 < (ammSwap1Balance1DecodeMem I out ret ret1).size := by
    have hsz := ammSwap1Balance1DecodeMem_size_ge I
      hlo hbound hretBound hretSize
    have hptr := (ammSwap1Balance1FreePtr_bounds out ret
      hlo hbound hretBound).1
    change 160 ≤ (ammSwap1Balance1FreePtr out ret).toNat at hptr
    omega
  have hfp := mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
    (by simpa using hmem)
    (ammActiveWords64 aw hawlo hawfit)
    (by simpa only [fp] using
      ammSwap1Balance1DecodeMem_read64 I out ret ret1)
  exact ammSwap1X_inputGuardReverts rd hbad hfp

end Benchmarks.ActAmm
