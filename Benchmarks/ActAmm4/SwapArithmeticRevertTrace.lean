import Benchmarks.ActAmm4.SwapArithmeticSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_reserve0Underflow
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3128⟩
      [v1, v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hunder : (solcSlotWord acc.2 I ⟨5⟩).toNat < q0.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd3132 := evm_run rd with [push0, dup6, push1 ⟨5⟩]
  obtain ⟨_, _, rd3133⟩ := rd3132.sload
    (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3133 with [
    push2 ⟨3142⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hunder)
    haw (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4SwapX_reserve1Underflow
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 amount0In : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3183⟩
      [amount0In, v1, v0, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw ret acc k C)
    (hunder : (solcSlotWord acc.2 I ⟨6⟩).toNat < q1.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd3187 := evm_run rd with [push0, dup6, push1 ⟨6⟩]
  obtain ⟨_, _, rd3188⟩ := rd3187.sload
    (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3188 with [
    push2 ⟨3197⟩, swap2, swap1,
    push2 ⟨5253⟩, jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide rd5253
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hunder)
    haw (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4SwapX_oldProductOverflow
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 a0 a1 : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3313⟩
      [a1, a0, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hover : UInt256.size ≤
      (solcSlotWord acc.2 I ⟨5⟩).toNat *
        (solcSlotWord acc.2 I ⟨6⟩).toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd3316 := evm_run rd with [jumpdest, push1 ⟨6⟩]
  obtain ⟨_, _, rd3317⟩ := rd3316.sload
    (by native_decide) (by evm_ov)
  have rd3319 := evm_run rd3317 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd3320⟩ := rd3319.sload
    (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3320 with [
    push2 ⟨3329⟩, swap2, swap1,
    push2 ⟨5458⟩, jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide rd5458
    (by simpa [solcSlotWord, codeOwnerStorageWord] using hover)
    haw (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4SwapX_newProductOverflow
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 v1 a0 a1 oldProduct : UInt256}
    {mem ret : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3329⟩
      [oldProduct, a1, a0, v1, v0, amm4SwapToWord I,
        q1, q0, ⟨349⟩, sel]
      mem aw ret acc k C)
    (hover : UInt256.size ≤ v0.toNat * v1.toNat)
    (haw : 3 ≤ aw.toNat) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd5458 := evm_run rd with [
    jumpdest, dup4, dup6, push2 ⟨3341⟩, swap2, swap1,
    push2 ⟨5458⟩, jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide rd5458 hover haw
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.ActAmm4
