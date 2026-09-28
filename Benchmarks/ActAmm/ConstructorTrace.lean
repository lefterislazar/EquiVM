import Benchmarks.ActAmm.ConstructorBase
import Reasoning.Reach
import Reasoning.Solc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

macro "amm_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [ammCreation_decode_append _ _ (by decide)]
      | (unfold ammCtorCode; rw [ammCreation_decode_append _ _ (by decide)]);
     native_decide))

macro "amm_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold ammCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "amm_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by amm_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by amm_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by amm_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by amm_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem ammCtorNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = ammCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (ammCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 : RD (ammCreationBytecode ++ tail) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
      (createdAccounts, σ) 0 0 := RD.initState hcode
  have rd4 := amm_ctor_run rd0 with [push1 ⟨128⟩, push1 ⟨64⟩]
  have rd5 := rd4.mstore 9 solcFreePtrMem (UInt256.ofNat 3)
    (by amm_ctor_decode) mem_cost (by native_decide) (by native_decide) (by simp)
  have rd12 := amm_ctor_run rd5 with [
    callvalue, dup1, iszero,
    push2 ⟨15⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd12.revertStub (by amm_ctor_decode) (by amm_ctor_decode)
    (by amm_ctor_decode) (by simp)

theorem ammCtorReachSetup
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = ammCreationBytecode ++ tail)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (ammCreationBytecode ++ tail) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨17⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd0 : RD (ammCreationBytecode ++ tail) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
      (createdAccounts, σ) 0 0 := RD.initState hcode
  have rd4 := amm_ctor_run rd0 with [push1 ⟨128⟩, push1 ⟨64⟩]
  have rd5 := rd4.mstore 9 solcFreePtrMem (UInt256.ofNat 3)
    (by amm_ctor_decode) mem_cost (by native_decide) (by native_decide) (by simp)
  have rd17 := amm_ctor_run rd5 with [
    callvalue, dup1, iszero, push2 ⟨15⟩,
    jumpiT (by rw [hwv]; decide) (by amm_ctor_jd),
    jumpdest, pop]
  exact ⟨_, _, rd17⟩

end Benchmarks.ActAmm
