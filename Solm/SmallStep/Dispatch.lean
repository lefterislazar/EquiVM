import Solm.SmallStep.Reflection

/-! Transaction-dispatch correspondence for the lowered Solm machine. -/

namespace Solm.SmallStep

open ABI

theorem CompilesTransitionEntries.of_mem {code transitions entries transition}
    (compiled : CompilesTransitionEntries code transitions entries)
    (member : transition ∈ transitions) :
    ∃ entry, entry ∈ entries ∧ entry.name = transition.name ∧
      CompilesCallable code transition.toCallable entry := by
  induction transitions generalizing entries with
  | nil => simp at member
  | cons head tail ih =>
      cases entries with
      | nil => simp [CompilesTransitionEntries] at compiled
      | cons entry entries =>
          rcases compiled with ⟨hname, hentry, hrest⟩
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨entry, by simp, hname, hentry⟩
          · obtain ⟨found, hfound, hnameFound, hcompiled⟩ := ih hrest member
            exact ⟨found, by simp [hfound], hnameFound, hcompiled⟩

theorem selectorDispatchMsg_mem
    (found : Solm.selectorDispatchMsg contract calldata = some transition) :
    transition ∈ contract.transitions := by
  unfold Solm.selectorDispatchMsg at found
  let sigs := contract.transitions.map (fun t => (t, Solm.transitionSigStr t))
  let hashes := sigs.map (Prod.map id (ffi.KEC ∘ String.toByteArray))
  let selectors := hashes.map (Prod.map id (fun b => b.extract 0 4))
  let current := calldata.extract 0 4
  change (match selectors.find? (fun (_, selector) => selector == current) with
    | some (foundTransition, _) => some foundTransition
    | none => none) = some transition at found
  cases hfind : selectors.find? (fun (_, selector) => selector == current) with
  | none => simp [hfind] at found
  | some pair =>
      have hpair : pair.1 = transition := by simpa [hfind] using found
      have hmem : pair ∈ selectors := List.mem_of_find?_eq_some hfind
      rcases (List.mem_map.mp hmem) with ⟨hashed, hhashed, hpushed⟩
      rcases (List.mem_map.mp hhashed) with ⟨signature, hsignature, hhashedEq⟩
      rcases (List.mem_map.mp hsignature) with ⟨sourceTransition, hsource, hsignatureEq⟩
      have hfirst : pair.1 = sourceTransition := by
        subst pair
        subst hashed
        subst signature
        rfl
      rw [hpair] at hfirst
      simpa [hfirst] using hsource

structure Invocation (source : Solm.ContractDecl) where
  decl : Solm.CallableDecl
  entry : CallableEntry
  locals : Solm.Store
  evm : EVM.State
  returnConvention : Solm.ReturnConvention
  compiled : CompilesCallable (lowerContract source).code decl entry

def Invocation.initial (invocation : Invocation source) : MachineState :=
  (lowerContract source).initialState invocation.entry invocation.evm invocation.locals

/-- The transaction-dispatch prefix separated from execution of the selected
    body.  This is the precise initial-state relation needed at the PAA
    boundary; it does not hide selector decoding or EVM-state construction. -/
inductive Dispatches
    (cfg : Solm.Config) (source : Solm.ContractDecl)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (gas : Ethereum.UInt256)
    (substate : Ethereum.Substate) (environment : Ethereum.ExecutionEnv) :
    Invocation source → Solm.ReturnConvention → Prop where
  | transition
      (hdispatch : Solm.selectorDispatchMsg source environment.calldata = some transition)
      (hsignature : signature = Solm.transitionSignature transition)
      (hdecode : decodeCalldataWithMode cfg.abiDecodeMode
        (transition.params.map Solm.Param.name) signature.paramTypes
        environment.calldata = some callargs)
      (hevm : evmState =
        { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := environment
          substate
          createdAccounts
          machineState.gasAvailable := .ofUInt256 gas
          blocks
          genesisBlockHeader })
      (compiled : CompilesCallable (lowerContract source).code
        transition.toCallable entry) :
      Dispatches cfg source createdAccounts genesisBlockHeader blocks σ σ₀ gas
        substate environment
        { decl := transition.toCallable
          entry
          locals := callargs
          evm := evmState
          returnConvention := .abi transition.returnType
          compiled }
        (.abi transition.returnType)
  | fallback
      (hselector : Solm.selectorDispatchMsg source environment.calldata = none)
      (hreceive : Solm.receiveDispatchMsg source environment.calldata = none)
      (hfallback : source.fallback = some transition)
      (hargs : Solm.fallbackCallargs environment.calldata transition.params = some callargs)
      (hreturn : Solm.fallbackReturnConvention transition = some returnConvention)
      (hevm : evmState =
        { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := environment
          substate
          createdAccounts
          machineState.gasAvailable := .ofUInt256 gas
          blocks
          genesisBlockHeader })
      (compiled : CompilesCallable (lowerContract source).code
        transition.toCallable entry) :
      Dispatches cfg source createdAccounts genesisBlockHeader blocks σ σ₀ gas
        substate environment
        { decl := transition.toCallable
          entry
          locals := callargs
          evm := evmState
          returnConvention
          compiled }
        returnConvention
  | receive
      (hreceive : Solm.receiveDispatchMsg source environment.calldata = some transition)
      (hparams : transition.params = [])
      (hreturns : transition.returnType = [])
      (hevm : evmState =
        { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := environment
          substate
          createdAccounts
          machineState.gasAvailable := .ofUInt256 gas
          blocks
          genesisBlockHeader })
      (compiled : CompilesCallable (lowerContract source).code
        transition.toCallable entry) :
      Dispatches cfg source createdAccounts genesisBlockHeader blocks σ σ₀ gas
        substate environment
        { decl := transition.toCallable
          entry
          locals := ∅
          evm := evmState
          returnConvention := .abi []
          compiled }
        (.abi [])

def InvocationTerminates (cfg : Solm.Config) (source : Solm.ContractDecl)
    (invocation : Invocation source) (result : Solm.ExecResult) : Prop :=
  ∃ final,
    terminate_at_ndet (lts cfg (lowerContract source)) invocation.initial final ∧
    final.execResult? = some result

structure ConstructorInvocation
    (source : Solm.ContractDecl) (args : List Solm.Value)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (gas : Ethereum.UInt256)
    (substate : Ethereum.Substate) (environment : Ethereum.ExecutionEnv) where
  locals : Solm.Store
  evm : EVM.State
  evm_eq : evm =
    { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := environment
      substate
      createdAccounts
      machineState.gasAvailable := .ofUInt256 gas
      blocks
      genesisBlockHeader }
  args_length : args.length = source.ctor.params.length
  locals_eq : locals = Std.HashMap.ofList
    (List.zip (source.ctor.params.map Solm.Param.name) args)

def ConstructorInvocation.initial
    (invocation : ConstructorInvocation source args createdAccounts
      genesisBlockHeader blocks σ σ₀ gas substate environment) : MachineState :=
  (lowerContract source).initialState (lowerContract source).constructorEntry
    invocation.evm invocation.locals

def ConstructorInvocationTerminates
    (cfg : Solm.Config)
    (invocation : ConstructorInvocation source args createdAccounts
      genesisBlockHeader blocks σ σ₀ gas substate environment)
    (result : Solm.ExecResult) : Prop :=
  ∃ final,
    terminate_at_ndet (lts cfg (lowerContract source)) invocation.initial final ∧
    final.execResult? = some result

/-- Full transaction-level correspondence: source dispatch plus big-step body
    execution is equivalent to the same certified dispatch followed by a
    terminating lowered-LTS run with the same decoded result. -/
theorem solmExec_iff_lowered_lts :
    Solm.solmExec cfg source createdAccounts genesisBlockHeader blocks
      σ σ₀ gas substate environment result returnConvention ↔
    ∃ invocation : Invocation source,
      Dispatches cfg source createdAccounts genesisBlockHeader blocks σ σ₀ gas
        substate environment invocation returnConvention ∧
      InvocationTerminates cfg source invocation result := by
  constructor
  · intro execution
    cases execution with
    | intro hdispatch hsignature hdecode hevm hbody =>
        rename_i transition signature callargs evmState
        have hmem := selectorDispatchMsg_mem hdispatch
        obtain ⟨entry, _, _, hcompiled⟩ :=
          (lowerContract_compiled source).transitions.of_mem hmem
        let invocation : Invocation source :=
          { decl := transition.toCallable
            entry
            locals := callargs
            evm := evmState
            returnConvention := .abi transition.returnType
            compiled := hcompiled }
        refine ⟨invocation,
          .transition hdispatch hsignature hdecode hevm hcompiled, ?_⟩
        exact (lowered_callable_lts_termination_iff source transition.toCallable
          entry callargs evmState hcompiled).mp hbody
    | fallback hselector hreceive hfallback hargs hreturn hevm hbody =>
        rename_i transition callargs evmState
        have hoptional := (lowerContract_compiled source).fallback
        change CompilesOptionalTransition (lowerContract source).code source.fallback
          (lowerContract source).fallbackEntry at hoptional
        rw [hfallback] at hoptional
        cases hentry : (lowerContract source).fallbackEntry with
        | none => simp [CompilesOptionalTransition, hentry] at hoptional
        | some entry =>
            simp only [CompilesOptionalTransition, hentry] at hoptional
            obtain ⟨hname, hcompiled⟩ := hoptional
            let invocation : Invocation source :=
              { decl := transition.toCallable
                entry
                locals := callargs
                evm := evmState
                returnConvention
                compiled := hcompiled }
            refine ⟨invocation,
              .fallback hselector hreceive hfallback hargs hreturn hevm hcompiled, ?_⟩
            exact (lowered_callable_lts_termination_iff source transition.toCallable
              entry callargs evmState hcompiled).mp hbody
    | receive hreceive hparams hreturns hevm hbody =>
        rename_i transition evmState
        have hsourceReceive : source.receive = some transition := by
          unfold Solm.receiveDispatchMsg at hreceive
          split at hreceive
          · simpa using hreceive
          · simp at hreceive
        have hoptional := (lowerContract_compiled source).receive
        change CompilesOptionalTransition (lowerContract source).code source.receive
          (lowerContract source).receiveEntry at hoptional
        rw [hsourceReceive] at hoptional
        cases hentry : (lowerContract source).receiveEntry with
        | none => simp [CompilesOptionalTransition, hentry] at hoptional
        | some entry =>
            simp only [CompilesOptionalTransition, hentry] at hoptional
            obtain ⟨hname, hcompiled⟩ := hoptional
            let invocation : Invocation source :=
              { decl := transition.toCallable
                entry
                locals := ∅
                evm := evmState
                returnConvention := .abi []
                compiled := hcompiled }
            refine ⟨invocation,
              .receive hreceive hparams hreturns hevm hcompiled, ?_⟩
            exact (lowered_callable_lts_termination_iff source transition.toCallable
              entry ∅ evmState hcompiled).mp hbody
  · rintro ⟨invocation, dispatched, termination⟩
    cases dispatched with
    | transition hdispatch hsignature hdecode hevm hcompiled =>
        exact .intro hdispatch hsignature hdecode hevm
          ((lowered_callable_lts_termination_iff source _ _ _ _ hcompiled).mpr
            termination)
    | fallback hselector hreceive hfallback hargs hreturn hevm hcompiled =>
        exact .fallback hselector hreceive hfallback hargs hreturn hevm
          ((lowered_callable_lts_termination_iff source _ _ _ _ hcompiled).mpr
            termination)
    | receive hreceive hparams hreturns hevm hcompiled =>
        exact .receive hreceive hparams hreturns hevm
          ((lowered_callable_lts_termination_iff source _ _ _ _ hcompiled).mpr
            termination)

/-- Constructor dispatch has the same bidirectional correspondence. -/
theorem solmCtorExec_iff_lowered_lts :
    Solm.solmCtorExec cfg source args createdAccounts genesisBlockHeader
      blocks σ σ₀ gas substate environment result ↔
    ∃ invocation : ConstructorInvocation source args createdAccounts
        genesisBlockHeader blocks σ σ₀ gas substate environment,
      ConstructorInvocationTerminates cfg invocation result := by
  constructor
  · intro execution
    cases execution with
    | intro hevm hlength hstore hbody =>
        rename_i evmState argsStore
        let invocation : ConstructorInvocation source args createdAccounts
            genesisBlockHeader blocks σ σ₀ gas substate environment :=
          { locals := argsStore
            evm := evmState
            evm_eq := hevm
            args_length := hlength
            locals_eq := hstore }
        refine ⟨invocation, ?_⟩
        exact (lowered_callable_lts_termination_iff source
          { params := source.ctor.params, body := source.ctor.body }
          (lowerContract source).constructorEntry argsStore evmState
          (lowerContract_compiled source).constructor).mp hbody
  · rintro ⟨invocation, termination⟩
    exact .intro invocation.evm_eq invocation.args_length invocation.locals_eq
      ((lowered_callable_lts_termination_iff source
        { params := source.ctor.params, body := source.ctor.body }
        (lowerContract source).constructorEntry invocation.locals invocation.evm
        (lowerContract_compiled source).constructor).mpr termination)

/-- Every source-level transaction dispatch selects a certified lowered entry
    and its big-step execution is reproduced by the lowered LTS. -/
theorem solmExec_to_lowered
    (execution : Solm.solmExec cfg source createdAccounts genesisBlockHeader blocks
      σ σ₀ gas substate environment result returnConvention) :
    ∃ invocation : Invocation source,
      invocation.returnConvention = returnConvention ∧
      Steps cfg (lowerContract source) invocation.initial (functionTarget [] result) := by
  cases execution with
  | intro hdispatch hsignature hdecode hevm hbody =>
      rename_i transition signature callargs evmState
      have hmem := selectorDispatchMsg_mem hdispatch
      obtain ⟨entry, _, _, hcompiled⟩ :=
        (lowerContract_compiled source).transitions.of_mem hmem
      let invocation : Invocation source :=
        { decl := transition.toCallable
          entry
          locals := callargs
          evm := evmState
          returnConvention := .abi transition.returnType
          compiled := hcompiled }
      refine ⟨invocation, rfl, ?_⟩
      exact lowerContract_callable_preservation source transition.toCallable entry
        callargs evmState hcompiled hbody
  | fallback hselector hreceive hfallback hargs hreturn hevm hbody =>
      rename_i transition callargs evmState
      have hoptional := (lowerContract_compiled source).fallback
      change CompilesOptionalTransition (lowerContract source).code source.fallback
        (lowerContract source).fallbackEntry at hoptional
      rw [hfallback] at hoptional
      cases hentry : (lowerContract source).fallbackEntry with
      | none => simp [CompilesOptionalTransition, hentry] at hoptional
      | some entry =>
        simp only [CompilesOptionalTransition, hentry] at hoptional
        obtain ⟨hname, hcompiled⟩ := hoptional
        let invocation : Invocation source :=
          { decl := transition.toCallable
            entry
            locals := callargs
            evm := evmState
            returnConvention
            compiled := hcompiled }
        refine ⟨invocation, rfl, ?_⟩
        exact lowerContract_callable_preservation source transition.toCallable entry
          callargs evmState hcompiled hbody
  | receive hreceive hparams hreturns hevm hbody =>
      rename_i transition evmState
      have hsourceReceive : source.receive = some transition := by
        unfold Solm.receiveDispatchMsg at hreceive
        split at hreceive
        · simpa using hreceive
        · simp at hreceive
      have hoptional := (lowerContract_compiled source).receive
      change CompilesOptionalTransition (lowerContract source).code source.receive
        (lowerContract source).receiveEntry at hoptional
      rw [hsourceReceive] at hoptional
      cases hentry : (lowerContract source).receiveEntry with
      | none => simp [CompilesOptionalTransition, hentry] at hoptional
      | some entry =>
        simp only [CompilesOptionalTransition, hentry] at hoptional
        obtain ⟨hname, hcompiled⟩ := hoptional
        let invocation : Invocation source :=
          { decl := transition.toCallable
            entry
            locals := ∅
            evm := evmState
            returnConvention := .abi []
            compiled := hcompiled }
        refine ⟨invocation, rfl, ?_⟩
        exact lowerContract_callable_preservation source transition.toCallable entry
          ∅ evmState hcompiled hbody

/-- Constructor dispatch has the analogous certified lowered start state. -/
theorem solmCtorExec_to_lowered
    (execution : Solm.solmCtorExec cfg source args createdAccounts genesisBlockHeader
      blocks σ σ₀ gas substate environment result) :
    ∃ locals evm,
      Steps cfg (lowerContract source)
        ((lowerContract source).initialState
          (lowerContract source).constructorEntry evm locals)
        (functionTarget [] result) := by
  cases execution with
  | intro hevm hlength hstore hbody =>
      rename_i evmState argsStore
      exact ⟨argsStore, evmState,
        lowerContract_callable_preservation source
          { params := source.ctor.params, body := source.ctor.body }
          (lowerContract source).constructorEntry argsStore evmState
          (lowerContract_compiled source).constructor hbody⟩

theorem steps_iff_lts_steps {contract : LoweredContract} :
    Steps cfg contract source target ↔
      steps_ndet (lts cfg contract) source target :=
  Iff.rfl

theorem execFuncBody_functionTarget_final
    (execution : Solm.ExecFuncBody cfg frame evm body result) :
    (lts cfg contract).isFinal ((lts cfg contract).label (functionTarget [] result)) := by
  cases execution <;> simp [lts, label, isFinal, functionTarget, finishReturn]

theorem solmExec_to_lts_termination
    (execution : Solm.solmExec cfg source createdAccounts genesisBlockHeader blocks
      σ σ₀ gas substate environment result returnConvention) :
    ∃ invocation : Invocation source,
      invocation.returnConvention = returnConvention ∧
      terminate_at_ndet (lts cfg (lowerContract source)) invocation.initial
        (functionTarget [] result) ∧
      (functionTarget [] result).execResult? = some result := by
  obtain ⟨invocation, hreturn, hsteps⟩ := solmExec_to_lowered execution
  have hfinal :
      (lts cfg (lowerContract source)).isFinal
        ((lts cfg (lowerContract source)).label (functionTarget [] result)) := by
    cases execution with
    | intro hdispatch hsignature hdecode hevm hbody =>
        exact execFuncBody_functionTarget_final hbody
    | fallback hselector hreceive hfallback hargs hreturn hevm hbody =>
        exact execFuncBody_functionTarget_final hbody
    | receive hreceive hparams hreturns hevm hbody =>
        exact execFuncBody_functionTarget_final hbody
  have hresult : (functionTarget [] result).execResult? = some result := by
    cases execution with
    | intro hdispatch hsignature hdecode hevm hbody =>
        exact execFuncBody_target_result hbody
    | fallback hselector hreceive hfallback hargs hreturn hevm hbody =>
        exact execFuncBody_target_result hbody
    | receive hreceive hparams hreturns hevm hbody =>
        exact execFuncBody_target_result hbody
  exact ⟨invocation, hreturn, ⟨steps_iff_lts_steps.mp hsteps, hfinal⟩, hresult⟩

theorem solmCtorExec_to_lts_termination
    (execution : Solm.solmCtorExec cfg source args createdAccounts genesisBlockHeader
      blocks σ σ₀ gas substate environment result) :
    ∃ locals evm,
      terminate_at_ndet (lts cfg (lowerContract source))
        ((lowerContract source).initialState
          (lowerContract source).constructorEntry evm locals)
        (functionTarget [] result) ∧
      (functionTarget [] result).execResult? = some result := by
  obtain ⟨locals, evm, hsteps⟩ := solmCtorExec_to_lowered execution
  cases execution with
  | intro hevm hlength hstore hbody =>
      exact ⟨locals, evm,
        ⟨steps_iff_lts_steps.mp hsteps, execFuncBody_functionTarget_final hbody⟩,
        execFuncBody_target_result hbody⟩

end Solm.SmallStep
