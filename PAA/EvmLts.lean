import PAA.PAA
import Ethereum.Semantics

/-! Adapters from the executable EVM semantics semantics to the
    mathematical transition systems used by the PAA theory. -/

namespace PAA.Evm

open Ethereum

/-- Orderable PAA labels corresponding one-to-one with EVM execution
    exceptions. -/
inductive EVMExceptionLabel where
  | outOfFuel
  | invalidInstruction
  | outOfGas
  | badJumpDestination
  | stackOverflow
  | stackUnderflow
  | invalidMemoryAccess
  | staticModeViolation
deriving DecidableEq, Ord

def executionExceptionLabel :
    Ethereum.EVM.ExecutionException → EVMExceptionLabel
  | .OutOfFuel => .outOfFuel
  | .InvalidInstruction => .invalidInstruction
  | .OutOfGass => .outOfGas
  | .BadJumpDestination => .badJumpDestination
  | .StackOverflow => .stackOverflow
  | .StackUnderflow => .stackUnderflow
  | .InvalidMemoryAccess => .invalidMemoryAccess
  | .StaticModeViolation => .staticModeViolation

/-- Control labels exposed to a PAA.  Running EVM configurations are labelled
    by their program counter; every kind of terminal outcome has a distinct
    label. -/
inductive EVMLabel where
  | pc (pc : Ethereum.UInt256)
  | success
  | revert
  | exception (exception : EVMExceptionLabel)
deriving DecidableEq, Ord

/-- `Xstep` outcomes made into explicit states.  This ensures that a transition
    into success, revert, or an exception is visible to the PAA; only a further
    attempt to step such a terminal state returns `none`. -/
inductive EVMConfig where
  | running (state : Ethereum.State)
  | success (state : Ethereum.State) (output : ByteArray)
  | revert (state : Ethereum.State) (output : ByteArray)
  | exception (state : Ethereum.State)
      (exception : Ethereum.EVM.ExecutionException)

def EVMConfig.state : EVMConfig → Ethereum.State
  | .running state | .success state _ | .revert state _ | .exception state _ => state

def EVMConfig.ofXstep (source : Ethereum.State) :
    Except Ethereum.EVM.ExecutionException
      (Ethereum.State × Option (Ethereum.EVM.HaltCause × ByteArray)) →
    EVMConfig
  | .error error => .exception source error
  | .ok (state, .none) => .running state
  | .ok (state, .some (.success, output)) => .success state output
  | .ok (state, .some (.revert, output)) => .revert state output

def evmLabel : EVMConfig → EVMLabel
  | .running state => .pc state.machineState.pc
  | .success _ _ => .success
  | .revert _ _ => .revert
  | .exception _ exception => .exception (executionExceptionLabel exception)

def evmStep (validJumps : Array Ethereum.UInt256) :
    EVMConfig → Option EVMConfig
  | .running state =>
      .some (EVMConfig.ofXstep state (Ethereum.EVM.Xstep validJumps state))
  | .success _ _ => .none
  | .revert _ _ => .none
  | .exception _ _ => .none

def evmIsFinal : EVMLabel → Prop
  | .pc _ => False
  | .success | .revert | .exception _ => True

lemma evmIsFinal_iff_step_none (validJumps : Array Ethereum.UInt256) :
    ∀ config, evmIsFinal (evmLabel config) ↔ evmStep validJumps config = .none := by
  intro config
  cases config <;> simp [evmIsFinal, evmLabel, evmStep]

/-- The deterministic PAA transition system backed by the real EVM
    instruction stepper `Ethereum.EVM.Xstep`. -/
def evmLts (validJumps : Array Ethereum.UInt256) :
    Lts_det EVMConfig EVMLabel where
  label := evmLabel
  step := evmStep validJumps
  isFinal := evmIsFinal
  hfinal := evmIsFinal_iff_step_none validJumps

/-- EVM PAA transition system for a concrete bytecode image. -/
def evmLtsForCode (code : ByteArray) : Lts_det EVMConfig EVMLabel :=
  evmLts (Ethereum.EVM.D_J code 0)

/-- Hypothetical nondeterministic one-step relation for the future small-step
    Solm semantics. -/
abbrev SolmStep (State : Type*) := State → State → Prop

/-- Package a relational Solm semantics directly as the nondeterministic LTS
    used on the B side of the PAA. -/
def hypotheticalSolmLts
    (label : State → Label)
    (step : SolmStep State)
    (isFinal : Label → Prop)
    (final_no_step : ∀ source target,
      isFinal (label source) → ¬ step source target) :
    Lts_ndet State Label where
  label := label
  step := step
  isFinal := isFinal
  hfinal := final_no_step

abbrev EVMSolmPAA (SolmState : Type*) (SolmLabel : Type*) :=
  PAA EVMConfig EVMLabel SolmState SolmLabel

/-- The general PAA refinement theorem specialized to actual `Xstep` execution
    on the A side and a hypothetical relational Solm semantics on the B side. -/
theorem evm_to_solm_refinement
    (validJumps : Array Ethereum.UInt256)
    (solmLts : Lts_ndet SolmState SolmLabel)
    (paa : EVMSolmPAA SolmState SolmLabel)
    (hpaa : validPAA (evmLts validJumps) solmLts paa) :
    ∀ (source : paa.Node) evm evmFinal solm,
      terminate_at (evmLts validJumps) evm evmFinal →
      paa.atNode (evmLts validJumps) solmLts source evm solm →
      ∃ solmFinal,
        steps_ndet solmLts solm solmFinal ∧
        solmLts.isFinal (solmLts.label solmFinal) ∧
        paa.goal evmFinal solmFinal := by
  exact paa_refinement (evmLts validJumps) solmLts paa hpaa

abbrev EVMLoweredSolmPAA :=
  EVMSolmPAA Solm.SmallStep.MachineState Solm.SmallStep.Label

/-- Refinement instantiated with the lowered, interprocedural Solm machine. -/
theorem evm_to_lowered_solm_refinement
    (validJumps : Array Ethereum.UInt256)
    (cfg : Solm.Config)
    (contract : Solm.SmallStep.LoweredContract)
    (paa : EVMLoweredSolmPAA)
    (hpaa : validPAA (evmLts validJumps)
      (Solm.SmallStep.lts cfg contract) paa) :
    ∀ (source : paa.Node) evm evmFinal solm,
      terminate_at (evmLts validJumps) evm evmFinal →
      paa.atNode (evmLts validJumps) (Solm.SmallStep.lts cfg contract)
        source evm solm →
      ∃ solmFinal,
        steps_ndet (Solm.SmallStep.lts cfg contract) solm solmFinal ∧
        (Solm.SmallStep.lts cfg contract).isFinal
          ((Solm.SmallStep.lts cfg contract).label solmFinal) ∧
        paa.goal evmFinal solmFinal := by
  exact evm_to_solm_refinement validJumps
    (Solm.SmallStep.lts cfg contract) paa hpaa

/-- End-to-end transaction adapter.  A PAA goal may rule out lowered fault
    states and decode the intended Solm result; the certified lowering then
    reflects the PAA-produced path back into the existing `solmExec`
    semantics used by refinement proofs. -/
theorem evm_to_solmExec_refinement
    (validJumps : Array Ethereum.UInt256)
    (cfg : Solm.Config) (source : Solm.ContractDecl)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (gas : Ethereum.UInt256)
    (substate : Ethereum.Substate) (environment : Ethereum.ExecutionEnv)
    (invocation : Solm.SmallStep.Invocation source)
    (returnConvention : Solm.ReturnConvention)
    (dispatched : Solm.SmallStep.Dispatches cfg source createdAccounts
      genesisBlockHeader blocks σ σ₀ gas substate environment invocation
      returnConvention)
    (paa : EVMLoweredSolmPAA)
    (hpaa : validPAA (evmLts validJumps)
      (Solm.SmallStep.lts cfg (Solm.SmallStep.lowerContract source)) paa)
    (goalResult : ∀ evmFinal solmFinal,
      paa.goal evmFinal solmFinal →
      ∃ result, solmFinal.execResult? = some result)
    (node : paa.Node)
    (termination : terminate_at (evmLts validJumps) evm evmFinal)
    (atNode : paa.atNode (evmLts validJumps)
      (Solm.SmallStep.lts cfg (Solm.SmallStep.lowerContract source))
      node evm invocation.initial) :
    ∃ solmFinal result,
      Solm.solmExec cfg source createdAccounts genesisBlockHeader blocks
        σ σ₀ gas substate environment result returnConvention ∧
      paa.goal evmFinal solmFinal := by
  obtain ⟨solmFinal, hsteps, hfinal, hgoal⟩ :=
    evm_to_lowered_solm_refinement validJumps cfg
      (Solm.SmallStep.lowerContract source) paa hpaa node evm evmFinal
      invocation.initial termination atNode
  obtain ⟨result, hdecoded⟩ := goalResult evmFinal solmFinal hgoal
  have hinvocation : Solm.SmallStep.InvocationTerminates cfg source invocation result :=
    ⟨solmFinal, ⟨hsteps, hfinal⟩, hdecoded⟩
  have hexecution :=
    (Solm.SmallStep.solmExec_iff_lowered_lts
      (cfg := cfg) (source := source) (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
      (σ := σ) (σ₀ := σ₀) (gas := gas) (substate := substate)
      (environment := environment) (result := result)
      (returnConvention := returnConvention)).mpr
      ⟨invocation, dispatched, hinvocation⟩
  exact ⟨solmFinal, result, hexecution, hgoal⟩

/-- Constructor analogue of `evm_to_solmExec_refinement`. -/
theorem evm_to_solmCtorExec_refinement
    (validJumps : Array Ethereum.UInt256)
    (cfg : Solm.Config) (source : Solm.ContractDecl) (args : List Solm.Value)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (gas : Ethereum.UInt256)
    (substate : Ethereum.Substate) (environment : Ethereum.ExecutionEnv)
    (invocation : Solm.SmallStep.ConstructorInvocation source args createdAccounts
      genesisBlockHeader blocks σ σ₀ gas substate environment)
    (paa : EVMLoweredSolmPAA)
    (hpaa : validPAA (evmLts validJumps)
      (Solm.SmallStep.lts cfg (Solm.SmallStep.lowerContract source)) paa)
    (goalResult : ∀ evmFinal solmFinal,
      paa.goal evmFinal solmFinal →
      ∃ result, solmFinal.execResult? = some result)
    (node : paa.Node)
    (termination : terminate_at (evmLts validJumps) evm evmFinal)
    (atNode : paa.atNode (evmLts validJumps)
      (Solm.SmallStep.lts cfg (Solm.SmallStep.lowerContract source))
      node evm invocation.initial) :
    ∃ solmFinal result,
      Solm.solmCtorExec cfg source args createdAccounts genesisBlockHeader blocks
        σ σ₀ gas substate environment result ∧
      paa.goal evmFinal solmFinal := by
  obtain ⟨solmFinal, hsteps, hfinal, hgoal⟩ :=
    evm_to_lowered_solm_refinement validJumps cfg
      (Solm.SmallStep.lowerContract source) paa hpaa node evm evmFinal
      invocation.initial termination atNode
  obtain ⟨result, hdecoded⟩ := goalResult evmFinal solmFinal hgoal
  have hinvocation : Solm.SmallStep.ConstructorInvocationTerminates cfg
      invocation result :=
    ⟨solmFinal, ⟨hsteps, hfinal⟩, hdecoded⟩
  have hexecution :=
    (Solm.SmallStep.solmCtorExec_iff_lowered_lts
      (cfg := cfg) (source := source) (args := args)
      (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
      (σ := σ) (σ₀ := σ₀) (gas := gas) (substate := substate)
      (environment := environment) (result := result)).mpr
      ⟨invocation, hinvocation⟩
  exact ⟨solmFinal, result, hexecution, hgoal⟩

end PAA.EvmSolm
