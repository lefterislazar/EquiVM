import Benchmarks.ActAmm4.MintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintX_amount0Ok {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1804⟩ [v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hle : (solcSlotWord σ I ⟨5⟩).toNat ≤ v0.toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1821⟩ [UInt256.sub v0 (solcSlotWord σ I ⟨5⟩), v1, v0,
        ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1807 := evm_run h with [push0, push1 ⟨5⟩]
  obtain ⟨_, _, rd1808⟩ := rd1807.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd1808 with [
    dup4, push2 ⟨1818⟩,
    swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1818⟩ := RD.amm4CheckedSubOk rd5253 hle
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd1818 with [jumpdest, swap1, pop]⟩

theorem amm4MintX_amount0Underflow {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1804⟩ [v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hunder : v0.toNat < (solcSlotWord σ I ⟨5⟩).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1807 := evm_run h with [push0, push1 ⟨5⟩]
  obtain ⟨_, _, rd1808⟩ := rd1807.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd1808 with [
    dup4, push2 ⟨1818⟩,
    swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide (a := v0) (b := solcSlotWord σ I ⟨5⟩)
    (ret := ⟨1818⟩)
    (R := [⟨0⟩, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel])
    rd5253 hunder haw (by evm_ov)

theorem amm4MintX_amount1Ok {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1821⟩ [a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hle : (solcSlotWord σ I ⟨6⟩).toNat ≤ v1.toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1838⟩ [UInt256.sub v1 (solcSlotWord σ I ⟨6⟩), a0, v1, v0,
        ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1824 := evm_run h with [push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1825⟩ := rd1824.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd1825 with [
    dup4, push2 ⟨1835⟩,
    swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1835⟩ := RD.amm4CheckedSubOk rd5253 hle
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd1835 with [jumpdest, swap1, pop]⟩

theorem amm4MintX_amount1Underflow {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 : UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1821⟩ [a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hunder : v1.toNat < (solcSlotWord σ I ⟨6⟩).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1824 := evm_run h with [push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1825⟩ := rd1824.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd1825 with [
    dup4, push2 ⟨1835⟩,
    swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide (a := v1) (b := solcSlotWord σ I ⟨6⟩)
    (ret := ⟨1835⟩)
    (R := [⟨0⟩, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel])
    rd5253 hunder haw (by evm_ov)

theorem amm4MintX_liq0NumeratorOk {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1838⟩ [a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfit : a0.toNat * (solcSlotWord σ I ⟨0⟩).toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1854⟩ [UInt256.mul a0 (solcSlotWord σ I ⟨0⟩),
        solcSlotWord σ I ⟨5⟩, ⟨0⟩, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1841 := evm_run h with [push0, push1 ⟨5⟩]
  obtain ⟨_, _, rd1842⟩ := rd1841.sload (by native_decide) (by evm_ov)
  have rd1843 := evm_run rd1842 with [push0]
  obtain ⟨_, _, rd1844⟩ := rd1843.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd1844 with [
    dup5, push2 ⟨1854⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOk rd5458 hfit (by jump_dest) (by evm_ov)

theorem amm4MintX_liq0NumeratorOverflow {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1838⟩ [a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hover : UInt256.size ≤ a0.toNat * (solcSlotWord σ I ⟨0⟩).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1841 := evm_run h with [push0, push1 ⟨5⟩]
  obtain ⟨_, _, rd1842⟩ := rd1841.sload (by native_decide) (by evm_ov)
  have rd1843 := evm_run rd1842 with [push0]
  obtain ⟨_, _, rd1844⟩ := rd1843.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd1844 with [
    dup5, push2 ⟨1854⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide
    (a := a0) (b := solcSlotWord σ I ⟨0⟩) (ret := ⟨1854⟩)
    (R := [solcSlotWord σ I ⟨5⟩, ⟨0⟩, a1, a0, v1, v0, ⟨0⟩,
      amm4MintToWord I, ⟨301⟩, sel]) rd5458 hover haw (by evm_ov)

theorem amm4MintX_liq0Ok {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 n0 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1854⟩ [n0, solcSlotWord σ I ⟨5⟩, ⟨0⟩, a1, a0, v1, v0,
        ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hreserve : solcSlotWord σ I ⟨5⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1867⟩ [UInt256.div n0 (solcSlotWord σ I ⟨5⟩),
        a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd5568 := evm_run h with [
    jumpdest, push2 ⟨1864⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1864⟩ := RD.amm4CheckedDivOk rd5568 hreserve
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd1864 with [jumpdest, swap1, pop]⟩

theorem amm4MintX_liq0ReserveZero {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 n0 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1854⟩ [n0, solcSlotWord σ I ⟨5⟩, ⟨0⟩, a1, a0, v1, v0,
        ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hreserve : solcSlotWord σ I ⟨5⟩ = ⟨0⟩)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd5568 := evm_run h with [
    jumpdest, push2 ⟨1864⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  exact RD.amm4CheckedDivZeroWide
    (a := n0) (b := solcSlotWord σ I ⟨5⟩) (ret := ⟨1864⟩)
    (R := [⟨0⟩, a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel])
    rd5568 hreserve haw (by evm_ov)

theorem amm4MintX_liq1NumeratorOk {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1867⟩ [q0, a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfit : a1.toNat * (solcSlotWord σ I ⟨0⟩).toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1883⟩ [UInt256.mul a1 (solcSlotWord σ I ⟨0⟩),
        solcSlotWord σ I ⟨6⟩, ⟨0⟩, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1870 := evm_run h with [push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1871⟩ := rd1870.sload (by native_decide) (by evm_ov)
  have rd1872 := evm_run rd1871 with [push0]
  obtain ⟨_, _, rd1873⟩ := rd1872.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd1873 with [
    dup5, push2 ⟨1883⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOk rd5458 hfit (by jump_dest) (by evm_ov)

theorem amm4MintX_liq1NumeratorOverflow {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1867⟩ [q0, a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hover : UInt256.size ≤ a1.toNat * (solcSlotWord σ I ⟨0⟩).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1870 := evm_run h with [push0, push1 ⟨6⟩]
  obtain ⟨_, _, rd1871⟩ := rd1870.sload (by native_decide) (by evm_ov)
  have rd1872 := evm_run rd1871 with [push0]
  obtain ⟨_, _, rd1873⟩ := rd1872.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd1873 with [
    dup5, push2 ⟨1883⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide
    (a := a1) (b := solcSlotWord σ I ⟨0⟩) (ret := ⟨1883⟩)
    (R := [solcSlotWord σ I ⟨6⟩, ⟨0⟩, q0, a1, a0, v1, v0, ⟨0⟩,
      amm4MintToWord I, ⟨301⟩, sel]) rd5458 hover haw (by evm_ov)

theorem amm4MintX_liq1Ok {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 n1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1883⟩ [n1, solcSlotWord σ I ⟨6⟩, ⟨0⟩, q0, a1, a0, v1,
        v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hreserve : solcSlotWord σ I ⟨6⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1896⟩ [UInt256.div n1 (solcSlotWord σ I ⟨6⟩),
        q0, a1, a0, v1, v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd5568 := evm_run h with [
    jumpdest, push2 ⟨1893⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1893⟩ := RD.amm4CheckedDivOk rd5568 hreserve
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd1893 with [jumpdest, swap1, pop]⟩

theorem amm4MintX_liq1ReserveZero {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 n1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1883⟩ [n1, solcSlotWord σ I ⟨6⟩, ⟨0⟩, q0, a1, a0, v1,
        v0, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hreserve : solcSlotWord σ I ⟨6⟩ = ⟨0⟩)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd5568 := evm_run h with [
    jumpdest, push2 ⟨1893⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  exact RD.amm4CheckedDivZeroWide
    (a := n1) (b := solcSlotWord σ I ⟨6⟩) (ret := ⟨1893⟩)
    (R := [⟨0⟩, q0, a1, a0, v1, v0, ⟨0⟩,
      amm4MintToWord I, ⟨301⟩, sel])
    rd5568 hreserve haw (by evm_ov)

theorem amm4MintX_selectLiq0 {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1896⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hle : q0.toNat ≤ q1.toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, q0,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1899 := evm_run h with [dup1, dup3, gt]
  rw [ugt_zero hle] at rd1899
  exact ⟨_, _, evm_run rd1899 with [
    push2 ⟨1910⟩, jumpiNT (by decide),
    dup2, swap7, pop, push2 ⟨1914⟩, jump (by jump_dest), jumpdest]⟩

theorem amm4MintX_selectLiq1 {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1896⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hgt : q1.toNat < q0.toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, q1,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have rd1899 := evm_run h with [dup1, dup3, gt]
  rw [ugt_one hgt] at rd1899
  exact ⟨_, _, evm_run rd1899 with [
    push2 ⟨1910⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, dup1, swap7, pop, jumpdest]⟩

theorem amm4MintX_liquidityNonzero {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hliq : liq ≠ ⟨0⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1981⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
  have hsub : UInt256.sub liq ⟨0⟩ = liq := by
    apply u256_inj
    rw [usub_toNat (by simp : (⟨0⟩ : UInt256).toNat ≤ liq.toNat)]
    simp
  have rd1918 := evm_run h with [push0, dup8, sub]
  rw [hsub] at rd1918
  exact ⟨_, _, evm_run rd1918 with [
    push2 ⟨1980⟩, jumpiT hliq (by jump_dest), jumpdest]⟩

theorem amm4MintX_supplyAdded {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1981⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true)
    (hfit : (solcSlotWord σ I ⟨0⟩).toNat + liq.toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨2004⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ (solcSlotWord σ I ⟨0⟩ + liq))
      k' C' := by
  have rd1985 := evm_run h with [dup7, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd1986⟩ := rd1985.sload (by native_decide) (by evm_ov)
  have rd5304 := evm_run rd1986 with [
    push2 ⟨1996⟩, swap2, swap1, push2 ⟨5304⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd1996⟩ := RD.amm4CheckedAddOk rd5304 hfit
    (by jump_dest) (by evm_ov)
  have rd2002 := evm_run rd1996 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd2003⟩ := rd2002.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2003 with [pop]⟩

theorem amm4MintX_supplyOverflow {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1981⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hover : UInt256.size ≤ (solcSlotWord σ I ⟨0⟩).toNat + liq.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1985 := evm_run h with [dup7, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd1986⟩ := rd1985.sload (by native_decide) (by evm_ov)
  have rd5304 := evm_run rd1986 with [
    push2 ⟨1996⟩, swap2, swap1, push2 ⟨5304⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedAddOverflowWide
    (a := solcSlotWord σ I ⟨0⟩) (b := liq) (ret := ⟨1996⟩)
    (R := [⟨0⟩, ⟨0⟩, liq, q1, q0, a1, a0, v1, v0, liq,
      amm4MintToWord I, ⟨301⟩, sel]) rd5304 hover haw (by evm_ov)

theorem amm4TwoWordHashMem_read0_64 (key slot : UInt256) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hkeySize : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le mem key 0 mem.size mem.size
      rfl (by omega) (by omega)
  have hhashSize : (twoWordHashMem key slot mem).size = mem.size := by
    unfold twoWordHashMem wordAt32Mem
    exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32
      mem.size mem.size hkeySize (by omega) (by omega)
  have hleftRead :
      (twoWordHashMem key slot mem).readWithPadding 0 32 =
        UInt256.toByteArray key := by
    unfold twoWordHashMem wordAt32Mem
    rw [toByteArray_write_read_below_no_gap slot (wordAt0Mem key mem) 32 0
      (by rw [hkeySize]; omega) (by omega)]
    unfold wordAt0Mem
    rw [toByteArray_write_read_window_no_gap key mem 0 0 32
      (by omega) (by omega) (by norm_num)]
    exact toByteArray_extract_all key
  have hrightRead :
      (twoWordHashMem key slot mem).readWithPadding 32 32 =
        UInt256.toByteArray slot := by
    unfold twoWordHashMem wordAt32Mem
    rw [toByteArray_write_read_window_no_gap slot (wordAt0Mem key mem) 32 0 32
      (by omega) (by omega) (by norm_num)]
    exact toByteArray_extract_all slot
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hhashSize]; omega)]
  have hleft : (twoWordHashMem key slot mem).extract 0 32 =
      UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hhashSize]; omega)]
    exact hleftRead
  have hright : (twoWordHashMem key slot mem).extract 32 64 =
      UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hhashSize]; omega)]
    exact hrightRead
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]; norm_num]
  rw [hleft, hright]

theorem amm4TwoWordHashMem_solcMappingSlot (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key := by
  rw [amm4TwoWordHashMem_read0_64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem amm4MappingHashSuffixWide {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc key baseSlot slot : UInt256} {R : List UInt256}
    {mem memKey memHash rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 pc (key :: ⟨0⟩ :: baseSlot :: R)
      mem aw rdata acc k C)
    (hwf : amm4MappingHashSuffixWf pc)
    (hkey : (UInt256.toByteArray key).write 0 mem 0 32 = memKey)
    (hbase : (UInt256.toByteArray baseSlot).write 0 memKey 32 32 = memHash)
    (hslot : UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0 64))) = slot)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 (amm4MappingHashSuffixEndPc pc)
      (slot :: R) memHash aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd1 := h.dup2 hd0 (by evm_ov)
  have rd2 := rd1.mstore 0 memKey aw hd1
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
    hkey hM0 (by evm_ov)
  have rd3 := rd2.push1 ⟨32⟩ hd2 (by evm_ov)
  have rd4 := rd3.add hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.mstore 0 memHash aw hd6
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show ((⟨32⟩ : UInt256) + ⟨0⟩).toNat = 32 from by decide,
        hM32, Nat.sub_self])
    (by simpa using hbase) hM32 (by evm_ov)
  have rd8 := rd7.push1 ⟨32⟩ hd7 (by evm_ov)
  have rd9 := rd8.add hd8 (by evm_ov)
  have rd10 := rd9.push0 hd9 (by evm_ov)
  exact ⟨_, _, rd10.keccak256 0 slot aw hd10
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show ((⟨32⟩ : UInt256) + (⟨32⟩ + ⟨0⟩)).toNat = 64 from by decide,
        hM64, Nat.sub_self])
    (by simpa only [show ((⟨32⟩ : UInt256) + (⟨32⟩ + ⟨0⟩)).toNat = 64
        from by decide] using hslot)
    (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show ((⟨32⟩ : UInt256) + (⟨32⟩ + ⟨0⟩)).toNat = 64
          from by decide] using hM64)
    (by evm_ov)⟩

theorem amm4MintX_recipientLoad {cAstart cA gh bl σ₀ σI σ₀' A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σ₀ σ₀' g A I)
      ⟨2004⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σI) k C)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hmem : 64 ≤ mem.size) (haw : 3 ≤ aw.toNat) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σ₀ σ₀' g A I)
      ⟨2070⟩ [solcSlotWord σI I (solcMappingSlot ⟨1⟩ (amm4MintToWord I)),
        liq, ⟨0⟩, solcMappingSlot ⟨1⟩ (amm4MintToWord I), liq,
        q1, q0, a1, a0, v1, v0, liq, amm4MintToWord I, ⟨301⟩, sel]
      (twoWordHashMem (amm4MintToWord I) ⟨1⟩ mem) aw rdata
      (cA, σI) k' C' := by
  have hclean : UInt256.land solcAddrMask (amm4MintToWord I) =
      amm4MintToWord I := solcAddrMask_clean_left hcanon
  have rd2053₀ := evm_run h with [
    dup7, push1 ⟨1⟩, push0, dup11,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd2053 := rd2053₀
  rw [hclean, hclean] at rd2053
  obtain ⟨_, _, rd2066⟩ := amm4MappingHashSuffixWide rd2053
    amm4_mapping_hash_wf (by rfl) (by rfl)
    (by simpa using (amm4TwoWordHashMem_solcMappingSlot ⟨1⟩
      (amm4MintToWord I) hmem))
    haw (by evm_ov)
  have rd2069 := evm_run rd2066 with [push0, dup3, dup3]
  obtain ⟨_, _, rd2070⟩ := rd2069.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2070⟩

theorem amm4MintX_recipientAdded {cAstart cA gh bl σ σI σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2070⟩ [solcSlotWord σI I (solcMappingSlot ⟨1⟩ (amm4MintToWord I)),
        liq, ⟨0⟩, solcMappingSlot ⟨1⟩ (amm4MintToWord I), liq,
        q1, q0, a1, a0, v1, v0, liq, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σI) k C)
    (hperm : I.perm = true)
    (hfit : (solcSlotWord σI I (solcMappingSlot ⟨1⟩
      (amm4MintToWord I))).toNat + liq.toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2087⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σI
        (solcMappingSlot ⟨1⟩ (amm4MintToWord I))
        (solcSlotWord σI I (solcMappingSlot ⟨1⟩ (amm4MintToWord I)) + liq))
      k' C' := by
  have rd5304 := evm_run h with [
    push2 ⟨2079⟩, swap2, swap1, push2 ⟨5304⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd2079⟩ := RD.amm4CheckedAddOk rd5304 hfit
    (by jump_dest) (by evm_ov)
  have rd2085 := evm_run rd2079 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd2086⟩ := rd2085.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2086 with [pop]⟩

theorem amm4MintX_recipientOverflow {cAstart cA gh bl σ σI σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2070⟩ [solcSlotWord σI I (solcMappingSlot ⟨1⟩ (amm4MintToWord I)),
        liq, ⟨0⟩, solcMappingSlot ⟨1⟩ (amm4MintToWord I), liq,
        q1, q0, a1, a0, v1, v0, liq, amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σI) k C)
    (hover : UInt256.size ≤ (solcSlotWord σI I
      (solcMappingSlot ⟨1⟩ (amm4MintToWord I))).toNat + liq.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σ σ₀ g A I) := by
  have rd5304 := evm_run h with [
    push2 ⟨2079⟩, swap2, swap1, push2 ⟨5304⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedAddOverflowWide
    (a := solcSlotWord σI I (solcMappingSlot ⟨1⟩ (amm4MintToWord I)))
    (b := liq) (ret := ⟨2079⟩)
    (R := [⟨0⟩, solcMappingSlot ⟨1⟩ (amm4MintToWord I), liq,
      q1, q0, a1, a0, v1, v0, liq, amm4MintToWord I, ⟨301⟩, sel])
    rd5304 hover haw (by evm_ov)

theorem amm4MintX_reservesStored {cAstart cA gh bl σ σI σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2087⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      mem aw rdata (cA, σI) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2110⟩ [⟨301⟩, liq, sel] mem aw rdata
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σI ⟨5⟩ v0) ⟨6⟩ v1) k' C' := by
  have rd2092 := evm_run h with [dup6, push1 ⟨5⟩, dup2, swap1]
  obtain ⟨_, _, rd2093⟩ := rd2092.sstore hperm (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2093 with [pop, dup5, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd2100⟩ := rd2099.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd2100 with [
    pop, pop, pop, pop, pop, pop, pop,
    swap2, swap1, pop]⟩


theorem amm4RoutineEncodeUint256Wide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {fp val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4856⟩ (fp :: val :: ret :: R)
      mem aw rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem fp.toNat 32 = memout)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret ((fp + ⟨32⟩) :: R)
      memout (UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32))
      rdata acc k' C' := by
  let awout := UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have hfp0 : fp + ⟨0⟩ = fp := by rw [u256_add_comm, u256_zero_add]
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨4875⟩, push0, dup4, add, dup5, push2 ⟨4841⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨4850⟩, dup2, push2 ⟨4677⟩,
    jump (by jump_dest),
    raw amm4RoutineCleanupUint256 (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hfp0])
      (by simpa only [hfp0] using hmemout)
      (by rw [hfp0])
      (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩


theorem amm4Mload64Wide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {fp pc : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 pc (⟨64⟩ :: R)
      mem aw rdata acc k C)
    (hdec : decode amm4Bytecode pc = some (.MLOAD, .none))
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hov : R.length + 1 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 (pc + ⟨1⟩) (fp :: R)
      mem aw rdata acc k' C' := by
  have hM : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    change UInt256.ofNat (max aw.toNat 3) = aw
    rw [max_eq_left haw]
    exact u256_ofNat_toNat aw
  have hval := mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
    (by simpa using hmem) hbelow (by simpa using hread)
  exact ⟨_, _, RD.mload 0 fp aw h hdec
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM, Nat.sub_self])
    hval hM hov⟩


theorem amm4MintX_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel val fp : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2110⟩ [⟨301⟩, val, sel] mem aw rdata acc k C)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hfp : 96 ≤ fp.toNat)
    (hfpfit : fp.toNat + 32 < UInt256.size)
    (haw : 3 ≤ aw.toNat)
    (hbelow : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawout : 3 ≤ (UInt256.ofNat
      (MachineState.M aw.toNat fp.toNat 32)).toNat)
    (hbelowout : ¬ (⟨64⟩ : UInt256) ≥
      UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) * ⟨32⟩) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I)
      acc (UInt256.toByteArray val) := by
  let memout := (UInt256.toByteArray val).write 0 mem fp.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32)
  have rd301 := evm_run h with [jump (by jump_dest)]
  have rd304 := evm_run rd301 with [jumpdest, push1 ⟨64⟩]
  obtain ⟨_, _, rd305⟩ := amm4Mload64Wide rd304 (by native_decide)
    (by omega) hread haw hbelow (by evm_ov)
  have rd4856 := evm_run rd305 with [
    push2 ⟨314⟩, swap2, swap1, push2 ⟨4856⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd314⟩ := amm4RoutineEncodeUint256Wide rd4856
    (by rfl) (by jump_dest) (by evm_ov)
  have hmemoutSize : 96 ≤ memout.size := by
    have hsz : fp.toNat + 32 ≤ memout.size := by
      simpa only [memout] using
        toByteArray_write_size_ge_off_add32_no_gap val mem fp.toNat
    omega
  have hreadOut : memout.readWithPadding 64 32 = UInt256.toByteArray fp := by
    simpa only [memout] using
      (show ((UInt256.toByteArray val).write 0 mem fp.toNat 32).readWithPadding
        64 32 = UInt256.toByteArray fp by
        rw [toByteArray_write_read_below_no_gap val mem fp.toNat 64
          hmem (by omega)]
        exact hread)
  have rd317 := evm_run rd314 with [jumpdest, push1 ⟨64⟩]
  obtain ⟨_, _, rd318⟩ := amm4Mload64Wide rd317 (by native_decide)
    (by change 64 < memout.size; omega) hreadOut hawout hbelowout (by evm_ov)
  have hsum : (fp + ⟨32⟩).toNat = fp.toNat + 32 := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    · rfl
    · simpa using hfpfit
  have hsub : UInt256.sub (fp + ⟨32⟩) fp = ⟨32⟩ := by
    apply u256_inj
    rw [usub_toNat (by rw [hsum]; omega), hsum]
    change fp.toNat + 32 - fp.toNat = 32
    omega
  have rd322₀ := evm_run rd318 with [dup1, swap2, sub, swap1]
  have rd322 := rd322₀
  rw [hsub] at rd322
  have hretRead : memout.readWithPadding fp.toNat 32 =
      UInt256.toByteArray val := by
    have hr := toByteArray_write_read_window_no_gap val mem fp.toNat 0 32
      (by omega) (by omega) (by norm_num)
    simpa only [memout, Nat.add_zero, Nat.zero_add,
      toByteArray_extract_all] using hr
  exact rd322.ret
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat fp.toNat 32)) - Cₘ awout)
    (UInt256.toByteArray val)
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      rfl)
    hretRead (by evm_ov)


theorem amm4TwoWordHashMem_size (key slot : UInt256) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  have hkeySize : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le mem key 0 mem.size mem.size
      rfl (by omega) (by omega)
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32
    mem.size mem.size hkeySize (by omega) (by omega)

theorem amm4TwoWordHashMem_read64 (key slot : UInt256) {mem : ByteArray}
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  have hkeySize : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le mem key 0 mem.size mem.size
      rfl (by omega) (by omega)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [hkeySize]; omega) (by omega) (by rw [hkeySize]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]

theorem amm4MintToken1DecodeMem_read64 (I : ExecutionEnv)
    (o1 o2 : ByteArray) :
    (amm4MintToken1DecodeMem I o1 o2).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)) := by
  unfold amm4MintToken1DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _


theorem amm4ActiveWords64 (aw : UInt256)
    (haw : 3 ≤ aw.toNat)
    (hfit : aw.toNat * 32 < UInt256.size) :
    ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
  have hmul : (aw * ⟨32⟩).toNat = aw.toNat * 32 := by
    rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      Nat.mod_eq_of_lt hfit]
  intro h
  have hle : (aw * ⟨32⟩).toNat ≤ 64 := h
  rw [hmul] at hle
  omega

theorem amm4MintFinalFreePtr_bounds (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    let fp := UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)
    160 ≤ fp.toNat ∧ fp.toNat + 32 < UInt256.size ∧ fp.toNat < 2 ^ 140 := by
  let n := (o2.size + 31) / 32
  obtain ⟨hfp0lo, hfp0hi⟩ := amm4MintToken0FreePtr_bounds o1 hlo1 hbound1
  have hptrlo : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
    simpa only [amm4MintToken0FreePtr] using hfp0lo
  have hptrhi : (amm4MintToken0FreePtr o1).toNat ≤ o1.size + 159 := by
    simpa only [amm4MintToken0FreePtr] using hfp0hi
  have hround : (amm4MintReturndataRounded o2).toNat = 32 * n := by
    simpa only [n] using amm4MintReturndataRounded_toNat o2 hbound2
  have hn : 32 * n ≤ o2.size + 31 := by
    simpa only [n] using Nat.mul_div_le (o2.size + 31) 32
  have hfit : (amm4MintToken0FreePtr o1).toNat +
      (amm4MintReturndataRounded o2).toNat < UInt256.size := by
    rw [hround]
    norm_num [UInt256.size] at *
    omega
  have hsum : (UInt256.add (amm4MintToken0FreePtr o1)
      (amm4MintReturndataRounded o2)).toNat =
      (amm4MintToken0FreePtr o1).toNat +
        (amm4MintReturndataRounded o2).toNat := by
    change (amm4MintToken0FreePtr o1 + amm4MintReturndataRounded o2).toNat = _
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  dsimp
  rw [hsum, hround]
  constructor
  · omega
  constructor
  · norm_num [UInt256.size] at *
    omega
  · omega


theorem amm4MintToken1ActiveWords_bounds (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    let aw := amm4MintToken1CalldataWords o
    3 ≤ aw.toNat ∧ aw.toNat * 32 < UInt256.size ∧ aw.toNat < 2 ^ 140 := by
  let n := (o.size + 31) / 32
  have hn : n ≤ o.size + 31 := Nat.div_le_self _ _
  have hnlo : 1 ≤ n := by dsimp [n]; omega
  have haw : (amm4MintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using amm4MintToken1CalldataWords_toNat o hlo hbound
  dsimp
  rw [haw]
  constructor
  · omega
  constructor
  · norm_num [UInt256.size] at *
    omega
  · omega

theorem amm4MintReturnActiveWords_bounds (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    let aw := amm4MintToken1CalldataWords o1
    let fp := UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)
    let awout := UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32)
    3 ≤ awout.toNat ∧ awout.toNat * 32 < UInt256.size := by
  let aw := amm4MintToken1CalldataWords o1
  let fp := UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)
  let m := MachineState.M aw.toNat fp.toNat 32
  have ⟨hawlo, _hawfit, hawhi⟩ := amm4MintToken1ActiveWords_bounds o1 hlo1 hbound1
  have ⟨_hfplo, _hfpfit, hfphi⟩ := amm4MintFinalFreePtr_bounds o1 o2
    hlo1 hbound1 hbound2
  have hawlo' : 3 ≤ aw.toNat := by simpa only [aw] using hawlo
  have hawhi' : aw.toNat < 2 ^ 140 := by simpa only [aw] using hawhi
  have hfphi' : fp.toNat < 2 ^ 140 := by simpa only [fp] using hfphi
  have hdiv : (fp.toNat + 32 + 31) / 32 ≤ fp.toNat + 63 := by
    have h := Nat.div_le_self (fp.toNat + 32 + 31) 32
    omega
  have hmlo : 3 ≤ m := by
    change 3 ≤ max aw.toNat ((fp.toNat + 32 + 31) / 32)
    exact le_trans hawlo' (le_max_left _ _)
  have hmhi : m < 2 ^ 141 := by
    change max aw.toNat ((fp.toNat + 32 + 31) / 32) < 2 ^ 141
    rw [max_lt_iff]
    constructor <;> omega
  have hmfit : m * 32 < UInt256.size := by
    norm_num [UInt256.size] at *
    omega
  have hmt : (UInt256.ofNat m).toNat = m :=
    UInt256.toNat_ofNat_of_lt (by omega)
  change 3 ≤ (UInt256.ofNat m).toNat ∧
    (UInt256.ofNat m).toNat * 32 < UInt256.size
  rw [hmt]
  exact ⟨hmlo, hmfit⟩

theorem amm4MintX_returnAfterStores {cAstart gh bl σ σ₀ A I} {g : Sat256}
    {sel val : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (h : RD amm4Bytecode I g (initState cAstart gh bl σ σ₀ g A I)
      ⟨2110⟩ [⟨301⟩, val, sel]
      (twoWordHashMem (amm4MintToWord I) ⟨1⟩
        (amm4MintToken1DecodeMem I o1 o2))
      (amm4MintToken1CalldataWords o1) o2 acc k C)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    RDret amm4Bytecode g (initState cAstart gh bl σ σ₀ g A I)
      acc (UInt256.toByteArray val) := by
  let mem := amm4MintToken1DecodeMem I o1 o2
  let memHash := twoWordHashMem (amm4MintToWord I) ⟨1⟩ mem
  let aw := amm4MintToken1CalldataWords o1
  let fp := UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)
  have hsize2 : o2.size < UInt256.size := by
    norm_num [UInt256.size] at *
    omega
  have hbase : 96 ≤ mem.size := by
    have hsz := amm4MintToken1DecodeMem_size_ge I hlo1 hbound1 hsize2
    have hptr := (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
    change 96 ≤ (amm4MintToken1DecodeMem I o1 o2).size
    have hptr' : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
      simpa only [amm4MintToken0FreePtr] using hptr
    omega
  have hmemHash : 96 ≤ memHash.size := by
    rw [amm4TwoWordHashMem_size (amm4MintToWord I) ⟨1⟩ (by omega : 64 ≤ mem.size)]
    exact hbase
  have hreadHash : memHash.readWithPadding 64 32 = UInt256.toByteArray fp := by
    rw [amm4TwoWordHashMem_read64 (amm4MintToWord I) ⟨1⟩ hbase]
    exact amm4MintToken1DecodeMem_read64 I o1 o2
  have ⟨hfplo, hfpfit, _⟩ := amm4MintFinalFreePtr_bounds o1 o2
    hlo1 hbound1 hbound2
  have ⟨hawlo, hawfit, _⟩ := amm4MintToken1ActiveWords_bounds o1 hlo1 hbound1
  have ⟨hawoutlo, hawoutfit⟩ := amm4MintReturnActiveWords_bounds o1 o2
    hlo1 hbound1 hbound2
  have hfp96 : 96 ≤ fp.toNat := by
    exact le_trans (by decide : 96 ≤ 160) hfplo
  exact amm4MintX_return h hmemHash hreadHash hfp96 hfpfit hawlo
    (amm4ActiveWords64 aw hawlo hawfit)
    hawoutlo (amm4ActiveWords64 _ hawoutlo hawoutfit)


end Benchmarks.ActAmm4
