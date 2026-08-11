import Examples.Precompiles.Modexp.GeneratedTraces
import Examples.Precompiles.Modexp.WordBridge
import Reasoning.Bytecode

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Inputs rejected by the deployed EIP-7823 length guard. -/
def invalidLengthAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ¬ validOsaka ctx.executionEnv.calldata

/-- Exact bytecode cost of entry setup, all three length checks, and `revert(0, 0)`. -/
def invalidLengthGasCost : Nat := 108

def invalidLengthEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactRevertPost ctx ByteArray.empty invalidLengthGasCost result

private theorem gt1024_eq (w : UInt256) :
    UInt256.gt w ⟨1024⟩ =
      if w.toNat ≤ 1024 then ⟨0⟩ else ⟨1⟩ := by
  split
  · apply ugt_zero
    simpa using ‹w.toNat ≤ 1024›
  · apply ugt_one
    have : 1024 < w.toNat := by omega
    simpa using this

private theorem invalidLengthGuard_nonzero (I : ExecutionEnv)
    (hinvalid : ¬ validOsaka I.calldata) :
    (UInt256.gt (baseSizeWord I) ⟨1024⟩).lor
        ((UInt256.gt (exponentSizeWord I) ⟨1024⟩).lor
          (UInt256.gt (modulusSizeWord I) ⟨1024⟩)) ≠ ⟨0⟩ := by
  have hnot : ¬ ((baseSizeWord I).toNat ≤ 1024 ∧
      (exponentSizeWord I).toNat ≤ 1024 ∧
      (modulusSizeWord I).toNat ≤ 1024) := by
    simpa [validOsaka] using hinvalid
  rw [gt1024_eq, gt1024_eq, gt1024_eq]
  by_cases hb : (baseSizeWord I).toNat ≤ 1024 <;>
    by_cases he : (exponentSizeWord I).toNat ≤ 1024 <;>
      by_cases hm : (modulusSizeWord I).toNat ≤ 1024 <;>
        simp only [hb, he, hm, if_pos]
  · exact (hnot ⟨hb, he, hm⟩).elim
  all_goals native_decide

/-- The generated entry and length-check traces close every invalid length input with the
deployed empty revert at its exact OOG threshold. -/
theorem invalidLengthExactRevert
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hinvalid : ¬ validOsaka I.calldata) :
    RDxRevOutput runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      ByteArray.empty invalidLengthGasCost := by
  have rd0 := RDx.initState
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hcode
  have rd10 := GeneratedTraces.trace_0_notTaken (by decide) rd0
    (by native_decide) hvalue
  have hguard :
      ((uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)).gt ⟨1024⟩).lor
          (((uInt256OfByteArray (I.calldata.readBytes (⟨32⟩ : UInt256).toNat 32)).gt
              ⟨1024⟩).lor
            ((uInt256OfByteArray (I.calldata.readBytes (⟨64⟩ : UInt256).toNat 32)).gt
              ⟨1024⟩)) ≠ ⟨0⟩ := by
    simpa [baseSizeWord, exponentSizeWord, modulusSizeWord, calldataWord] using
      invalidLengthGuard_nonzero I hinvalid
  have rd436 := GeneratedTraces.trace_10_taken (by decide) rd10
    (by native_decide) hguard (by native_decide)
  have rd439 := GeneratedTraces.trace_436_body (by simp) rd436
  have hrev := RDx.revOutputExact 0 ByteArray.empty rd439 (by native_decide)
    (fun s _ hstk => memExpRevert0 s hstk)
    (Reasoning.Theory.byteArray_readWithPadding_zero _ _) (by simp)
  simpa [invalidLengthGasCost, MachineState.M, Cₘ] using hrev

theorem invalidLengthBytecodeSpec :
    BytecodeSpec runtimeBytecode invalidLengthAccepts invalidLengthEnsures := by
  simpa [invalidLengthEnsures] using
    (ExactRevertSpec.ofRDxRevOutput (code := runtimeBytecode)
      (accepts := invalidLengthAccepts)
      (output := fun _ => ByteArray.empty)
      (gasCost := fun _ => invalidLengthGasCost)
      (fun ctx hcode haccepts => by
        exact invalidLengthExactRevert
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode haccepts.1 haccepts.2))

end Modexp
