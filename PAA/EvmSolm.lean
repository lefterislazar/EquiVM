import PAA.PAA

/-! Adapters from the executable EVM semantics and a future executable Solm
    semantics to the mathematical transition systems used by the PAA theory. -/

namespace PAA.EvmSolm

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
  hfinal_exists :=
    ⟨.success default ByteArray.empty, by simp [evmLabel, evmIsFinal]⟩

/-- EVM PAA transition system for a concrete bytecode image. -/
def evmLtsForCode (code : ByteArray) : Lts_det EVMConfig EVMLabel :=
  evmLts (Ethereum.EVM.D_J code 0)

/-- Hypothetical nondeterministic one-step relation for the future small-step
    Solm semantics. -/
abbrev SolmStep (State : Type*) := State → State → Prop

/-- Package a relational Solm semantics directly as the nondeterministic LTS
    used on the B side of the PAA. -/
def hypotheticalSolmLts [Ord Label]
    (label : State → Label)
    (step : SolmStep State)
    (isFinal : Label → Prop)
    (final_no_step : ∀ source target,
      isFinal (label source) → ¬ step source target)
    (final_exists : ∃ state, isFinal (label state)) :
    Lts_ndet State Label where
  label := label
  step := step
  isFinal := isFinal
  hfinal := final_no_step
  hfinal_exists := final_exists

abbrev EVMSolmPAA [Ord SolmLabel]
    (validJumps : Array Ethereum.UInt256)
    (solmLts : Lts_ndet SolmState SolmLabel) :=
  PAA (evmLts validJumps) solmLts

/-- The general PAA refinement theorem specialized to actual `Xstep` execution
    on the A side and a hypothetical relational Solm semantics on the B side. -/
theorem evm_to_solm_refinement [Ord SolmLabel]
    (validJumps : Array Ethereum.UInt256)
    (solmLts : Lts_ndet SolmState SolmLabel)
    (paa : EVMSolmPAA validJumps solmLts)
    (hpaa : validPAA (evmLts validJumps) solmLts paa) :
    ∀ (source : paa.Node) evm evmFinal solm,
      terminate_at (evmLts validJumps) evm evmFinal →
      paa.atNode (evmLts validJumps) solmLts source evm solm →
      ∃ solmFinal,
        steps_ndet solmLts solm solmFinal ∧
        solmLts.isFinal (solmLts.label solmFinal) ∧
        paa.goal evmFinal solmFinal := by
  exact paa_refinement (evmLts validJumps) solmLts paa hpaa

end PAA.EvmSolm
