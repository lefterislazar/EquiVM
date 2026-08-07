import Tools.SymCheck.Fixtures.SymCheckGeneratedSmoke

/-!
# Generated RDx simplification smoke tests

These examples exercise `evm_simp` on an actual inferred generated theorem and on the conservative
memory rewrites that are useful when composed paths expose `MSTORE`/`MLOAD` relationships.
-/

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Reach Reasoning.Theory

example
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc (((k + 1) + 1) + 1)
      (((C + 3) + 3) + 3)) :
    RDx code ee g s0 pc stk mem aw rdata acc (k + 3) (C + 9) := by
  evm_simp

/-- The five-op generated CtorStore body gets compact step and gas indices without changing its
opaque source theorem. -/
example
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    (hdepth : tail.length ≤ 1022)
    (h : RDx ctorStoreRuntimeBytecode ee g s0 ⟨0⟩ tail mem aw rdata acc k C) :
    RDx ctorStoreRuntimeBytecode ee g s0 ⟨7⟩ (⟨0⟩ :: ⟨0⟩ :: tail)
      ((⟨128⟩ : UInt256).toByteArray.write 0 mem (⟨64⟩ : UInt256).toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)) rdata acc
      (k + 5)
      (C + (Cₘ (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)) -
        Cₘ aw) + 13) := by
  have hraw := CtorStore.SymCheckSmoke.block_0_body hdepth h
  evm_simp

example (mem : ByteArray) (word : UInt256)
    (hgap : 64 - mem.size < USize.size) :
    (writeWord mem 64 word).readWithPadding 64 32 = UInt256.toByteArray word := by
  evm_simp

example (mem : ByteArray) (word : UInt256)
    (hgap : 64 - mem.size < USize.size)
    (hsize : 32 ≤ mem.size) :
    (writeWord mem 64 word).readWithPadding 0 32 = mem.readWithPadding 0 32 := by
  evm_simp

example (mem : ByteArray) (first later : UInt256)
    (hgap : 64 - mem.size < USize.size)
    (hlater : WindowDisjointFromWrites (max mem.size (64 + 32)) 64 32 [(96, later)]) :
    (writeCascade mem [(64, first), (96, later)]).readWithPadding 64 32 =
      UInt256.toByteArray first := by
  evm_simp

example (mem : ByteArray) (aw word : UInt256)
    (hgap : 64 - mem.size < USize.size)
    (hmem : (⟨64⟩ : UInt256).toNat < (writeWord mem 64 word).size)
    (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (writeWord mem 64 word).size ∨
        (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((writeWord mem 64 word).readWithPadding 64 32))) = word := by
  evm_simp
