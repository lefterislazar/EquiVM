import PAA.PAA
import Solm.Semantics

/-! A contract-wide lowering of structured Solm statements to a finite,
    interprocedural control-flow machine suitable for use with a PAA. -/

namespace Array

def get? (array : Array α) (index : Nat) : Option α :=
  array[index]?

end Array

namespace Solm.SmallStep

open Solm ABI

abbrev PC := Nat

inductive Fault where
  | invalidPC
  | malformedBreak
  | malformedContinue
  | malformedReturn
  | unknownFunction
  | argumentBinding
  | evaluation (error : Solm.EvalError)
deriving Repr, DecidableEq

/-- A flattened control point.  Structured statements are eliminated by the
    lowering; only primitive statements remain in `atomic`. -/
inductive Command where
  | atomic (stmt : Solm.Stmt) (next : PC)
  | jump (target : PC)
  | branch (condition : Solm.Expr) (ifTrue ifFalse : PC)
  | internalCall (name : Solm.Ident) (args : List Solm.Expr)
      (result : Solm.Ident) (returnTo : PC)
  | checkedCall (receiver : Solm.Expr) (name : Solm.Ident)
      (eth : Solm.Expr) (args : List Solm.Expr)
      (result : Solm.Ident) (onSuccess : PC)
      (errorResult : Solm.Ident) (onFailure : PC) (perm : Bool)
  | return (values : List Solm.Expr)
  | blockedReturn (values : List Solm.Expr)
  | fallthrough
  | fault (reason : Fault)
deriving Repr

structure LoopTargets where
  breakTarget : Option PC := none
  continueTarget : Option PC := none
  /-- Callable bodies interpret an unbound abrupt statement as the
      source-level function fallthrough convention.  Compiler-generated
      `for` initializer and post contexts disable this explicitly. -/
  allowUnboundAbrupt : Bool := true
  /-- `for` post blocks cannot return in the source `ExecForLoop` relation. -/
  allowReturn : Bool := true

def strictPostTargets : LoopTargets :=
  { allowUnboundAbrupt := false, allowReturn := false }

abbrev LowerM := StateM (Array Command)

def emit (command : Command) : LowerM PC := do
  let code ← get
  let pc := code.size
  set (code.push command)
  pure pc

def reserve : LowerM PC :=
  emit (.fault .invalidPC)

def patch (pc : PC) (command : Command) : LowerM Unit :=
  modify fun code => code.set! pc command

mutual

def lowerBlock (statements : List Solm.Stmt) (next : PC)
    (loop : LoopTargets) : LowerM PC := do
  match statements with
  | [] => pure next
  | stmt :: rest =>
      let restEntry ← lowerBlock rest next loop
      lowerStmt stmt restEntry loop

def lowerStmt (stmt : Solm.Stmt) (next : PC)
    (loop : LoopTargets) : LowerM PC := do
  match stmt with
  | .while condition body =>
      let conditionPC ← reserve
      let bodyEntry ← lowerBlock body conditionPC
        { breakTarget := some next, continueTarget := some conditionPC,
          allowReturn := loop.allowReturn }
      patch conditionPC (.branch condition bodyEntry next)
      pure conditionPC
  | .for init condition post body =>
      let conditionPC ← reserve
      let postEntry ← lowerBlock post conditionPC strictPostTargets
      let bodyEntry ← lowerBlock body postEntry
        { breakTarget := some next, continueTarget := some postEntry,
          allowReturn := loop.allowReturn }
      patch conditionPC (.branch condition bodyEntry next)
      let initEntry ← lowerBlock init conditionPC
        { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }
      emit (.jump initEntry)
  | .ite condition ifTrue ifFalse =>
      let trueEntry ← lowerBlock ifTrue next loop
      let falseEntry ← lowerBlock ifFalse next loop
      emit (.branch condition trueEntry falseEntry)
  | .internalCall name args result =>
      emit (.internalCall name args result next)
  | .checkedCall receiver name eth args result onSuccess errorResult onFailure perm =>
      let successEntry ← lowerBlock onSuccess next loop
      let failureEntry ← lowerBlock onFailure next loop
      emit (.checkedCall receiver name eth args result successEntry
        errorResult failureEntry perm)
  | .return values =>
      if loop.allowReturn then emit (.return values)
      else emit (.blockedReturn values)
  | .break =>
      match loop.breakTarget with
      | some target => emit (.jump target)
      | none =>
          if loop.allowUnboundAbrupt then emit .fallthrough
          else emit (.fault .malformedBreak)
  | .continue =>
      match loop.continueTarget with
      | some target => emit (.jump target)
      | none =>
          if loop.allowUnboundAbrupt then emit .fallthrough
          else emit (.fault .malformedContinue)
  | atomic =>
      emit (.atomic atomic next)

end

structure CallableEntry where
  name : Solm.Ident
  params : List Solm.Param
  returnType : List ABI.ABIType
  entry : PC
deriving Repr

structure LoweredContract where
  source : Solm.ContractDecl
  code : Array Command
  constructorEntry : CallableEntry
  functionEntries : List CallableEntry
  transitionEntries : List CallableEntry
  receiveEntry : Option CallableEntry
  fallbackEntry : Option CallableEntry
deriving Repr

def lowerCallable (name : Solm.Ident) (callable : Solm.CallableDecl) :
    LowerM CallableEntry := do
  let done ← emit .fallthrough
  let entry ← lowerBlock callable.body done {}
  pure { name, params := callable.params, returnType := callable.returnType, entry }

def lowerFunctions : List Solm.FunctionDecl → LowerM (List CallableEntry)
  | [] => pure []
  | function :: rest => do
      let entry ← lowerCallable function.name function.toCallable
      let entries ← lowerFunctions rest
      pure (entry :: entries)

def lowerTransitions : List Solm.TransitionDecl → LowerM (List CallableEntry)
  | [] => pure []
  | transition :: rest => do
      let entry ← lowerCallable transition.name transition.toCallable
      let entries ← lowerTransitions rest
      pure (entry :: entries)

def lowerOptionalTransition : Option Solm.TransitionDecl →
    LowerM (Option CallableEntry)
  | none => pure none
  | some transition => do
      let entry ← lowerCallable transition.name transition.toCallable
      pure (some entry)

def lowerContract (contract : Solm.ContractDecl) : LoweredContract :=
  let lowerEntries : LowerM
      (CallableEntry × List CallableEntry × List CallableEntry ×
        Option CallableEntry × Option CallableEntry) := do
    let constructor ← lowerCallable "<constructor>"
      { params := contract.ctor.params, body := contract.ctor.body }
    let functions ← lowerFunctions contract.functions
    let transitions ← lowerTransitions contract.transitions
    let receive ← lowerOptionalTransition contract.receive
    let fallback ← lowerOptionalTransition contract.fallback
    pure (constructor, functions, transitions, receive, fallback)
  let (entries, code) := lowerEntries.run #[]
  { source := contract
    code
    constructorEntry := entries.1
    functionEntries := entries.2.1
    transitionEntries := entries.2.2.1
    receiveEntry := entries.2.2.2.1
    fallbackEntry := entries.2.2.2.2 }

def lookupEntry? : List CallableEntry → Solm.Ident → Option CallableEntry
  | [], _ => none
  | entry :: rest, name =>
      if entry.name = name then some entry else lookupEntry? rest name

/-- Internal lookup follows the same priority as `Solm.lookupCallable?`:
    functions before transitions. -/
def LoweredContract.lookupInternal? (contract : LoweredContract)
    (name : Solm.Ident) : Option CallableEntry :=
  match lookupEntry? contract.functionEntries name with
  | some entry => some entry
  | none => lookupEntry? contract.transitionEntries name

structure ReturnFrame where
  caller : Solm.Frame
  result : Solm.Ident
  returnPC : PC

inductive MachineState where
  | running (pc : PC) (frame : Solm.Frame) (evm : EVM.State)
      (calls : List ReturnFrame)
  | returned (frame : Solm.Frame) (evm : EVM.State)
      (values : Option (List Solm.Value))
  | reverted
  | fault (reason : Fault)

def LoweredContract.initialState (contract : LoweredContract)
    (entry : CallableEntry) (evm : EVM.State) (locals : Solm.Store) :
    MachineState :=
  .running entry.entry { contract := contract.source, locals } evm []

def MachineState.execResult? : MachineState → Option Solm.ExecResult
  | .returned frame evm values => some (.returned frame evm values)
  | .reverted => some .reverted
  | .running _ _ _ _ | .fault _ => none

inductive Label where
  | pc (pc : PC)
  | returned
  | reverted
  | fault
deriving Repr, DecidableEq, Ord

def label : MachineState → Label
  | .running pc _ _ _ => .pc pc
  | .returned _ _ _ => .returned
  | .reverted => .reverted
  | .fault _ => .fault

def finishReturn (frame : Solm.Frame) (evm : EVM.State)
    (values : Option (List Solm.Value)) : List ReturnFrame → MachineState
  | [] => .returned frame evm values
  | continuation :: calls =>
      .running continuation.returnPC
        (Solm.resumeAfterInternalCall continuation.caller continuation.result values)
        evm calls

/-- Interprocedural small-step execution of a lowered contract. -/
inductive Step (cfg : Solm.Config) (contract : LoweredContract) :
    MachineState → MachineState → Prop where
  | invalidPC :
      contract.code.get? pc = none →
      Step cfg contract (.running pc frame evm calls) (.fault .invalidPC)
  | explicitFault :
      contract.code.get? pc = some (.fault reason) →
      Step cfg contract (.running pc frame evm calls) (.fault reason)
  | jump :
      contract.code.get? pc = some (.jump target) →
      Step cfg contract (.running pc frame evm calls)
        (.running target frame evm calls)
  | atomicOK :
      contract.code.get? pc = some (.atomic stmt next) →
      Solm.ExecStmt cfg frame evm stmt (.ok frame' evm') →
      Step cfg contract (.running pc frame evm calls)
        (.running next frame' evm' calls)
  | atomicRevert :
      contract.code.get? pc = some (.atomic stmt next) →
      Solm.ExecStmt cfg frame evm stmt .reverted →
      Step cfg contract (.running pc frame evm calls) .reverted
  | branchTrue :
      contract.code.get? pc = some (.branch condition ifTrue ifFalse) →
      Solm.evalExpr? cfg frame evm condition = .ok (.bool true) →
      Step cfg contract (.running pc frame evm calls)
        (.running ifTrue frame evm calls)
  | branchFalse :
      contract.code.get? pc = some (.branch condition ifTrue ifFalse) →
      Solm.evalExpr? cfg frame evm condition = .ok (.bool false) →
      Step cfg contract (.running pc frame evm calls)
        (.running ifFalse frame evm calls)
  | branchRevert :
      contract.code.get? pc = some (.branch condition ifTrue ifFalse) →
      Solm.evalExpr? cfg frame evm condition = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | branchError :
      contract.code.get? pc = some (.branch condition ifTrue ifFalse) →
      Solm.evalExpr? cfg frame evm condition = .error error →
      Step cfg contract (.running pc frame evm calls) (.fault (.evaluation error))
  | internalCall :
      contract.code.get? pc = some (.internalCall name args result returnTo) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      contract.lookupInternal? name = some callee →
      Solm.bindParams? callee.params values = some locals →
      Step cfg contract (.running pc frame evm calls)
        (.running callee.entry { frame with locals := locals } evm
          ({ caller := frame, result, returnPC := returnTo } :: calls))
  | internalCallArgsRevert :
      contract.code.get? pc = some (.internalCall name args result returnTo) →
      Solm.evalExprs? cfg frame evm args = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | internalCallArgsError :
      contract.code.get? pc = some (.internalCall name args result returnTo) →
      Solm.evalExprs? cfg frame evm args = .error error →
      Step cfg contract (.running pc frame evm calls) (.fault (.evaluation error))
  | internalCallUnknown :
      contract.code.get? pc = some (.internalCall name args result returnTo) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      contract.lookupInternal? name = none →
      Step cfg contract (.running pc frame evm calls) (.fault .unknownFunction)
  | internalCallBindingError :
      contract.code.get? pc = some (.internalCall name args result returnTo) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      contract.lookupInternal? name = some callee →
      Solm.bindParams? callee.params values = none →
      Step cfg contract (.running pc frame evm calls) (.fault .argumentBinding)
  | returnOK :
      contract.code.get? pc = some (.return expressions) →
      Solm.evalExprs? cfg frame evm expressions = .ok values →
      Step cfg contract (.running pc frame evm calls)
        (finishReturn frame evm (some values) calls)
  | returnRevert :
      contract.code.get? pc = some (.return expressions) →
      Solm.evalExprs? cfg frame evm expressions = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | returnError :
      contract.code.get? pc = some (.return expressions) →
      Solm.evalExprs? cfg frame evm expressions = .error error →
      Step cfg contract (.running pc frame evm calls) (.fault (.evaluation error))
  | blockedReturnOK :
      contract.code.get? pc = some (.blockedReturn expressions) →
      Solm.evalExprs? cfg frame evm expressions = .ok values →
      Step cfg contract (.running pc frame evm calls) (.fault .malformedReturn)
  | blockedReturnRevert :
      contract.code.get? pc = some (.blockedReturn expressions) →
      Solm.evalExprs? cfg frame evm expressions = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | blockedReturnError :
      contract.code.get? pc = some (.blockedReturn expressions) →
      Solm.evalExprs? cfg frame evm expressions = .error error →
      Step cfg contract (.running pc frame evm calls) (.fault (.evaluation error))
  | fallthrough :
      contract.code.get? pc = some .fallthrough →
      Step cfg contract (.running pc frame evm calls)
        (finishReturn frame evm none calls)
  | checkedCallSuccess :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .ok (.address target) →
      Solm.evalExpr? cfg frame evm eth = .ok (.int sendValue) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      Solm.typedCallViaEVM cfg evm (EVM.address target) name sendValue values
        (true, evm', output) perm →
      cfg.externalABI.decode? name output = some returns →
      Step cfg contract (.running pc frame evm calls)
        (.running onSuccess
          { frame with
            locals := frame.locals.insert result (Solm.collapseReturns returns) }
          evm' calls)
  | checkedCallFailure :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .ok (.address target) →
      Solm.evalExpr? cfg frame evm eth = .ok (.int sendValue) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      Solm.typedCallViaEVM cfg evm (EVM.address target) name sendValue values
        (false, evm', output) perm →
      Step cfg contract (.running pc frame evm calls)
        (.running onFailure
          { frame with locals := frame.locals.insert errorResult (.bytes output) }
          evm' calls)
  | checkedCallDecodeRevert :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .ok (.address target) →
      Solm.evalExpr? cfg frame evm eth = .ok (.int sendValue) →
      Solm.evalExprs? cfg frame evm args = .ok values →
      Solm.typedCallViaEVM cfg evm (EVM.address target) name sendValue values
        (true, evm', output) perm →
      cfg.externalABI.decode? name output = none →
      Step cfg contract (.running pc frame evm calls) .reverted
  | checkedCallReceiverRevert :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | checkedCallValueRevert :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .ok (.address target) →
      Solm.evalExpr? cfg frame evm eth = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted
  | checkedCallArgsRevert :
      contract.code.get? pc = some
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) →
      Solm.evalExpr? cfg frame evm receiver = .ok (.address target) →
      Solm.evalExpr? cfg frame evm eth = .ok (.int sendValue) →
      Solm.evalExprs? cfg frame evm args = .revert →
      Step cfg contract (.running pc frame evm calls) .reverted

def isFinal : Label → Prop
  | .pc _ => False
  | .returned | .reverted | .fault => True

/-- Relational Solm LTS consumed directly by the B side of a PAA. -/
def lts (cfg : Solm.Config) (contract : LoweredContract) :
    Lts_ndet MachineState Label where
  label := label
  step := Step cfg contract
  isFinal := isFinal
  hfinal := by
    intro source target hfinal hstep
    cases source with
    | running pc frame evm calls => simp [label, isFinal] at hfinal
    | returned frame evm values => cases hstep
    | reverted => cases hstep
    | fault reason => cases hstep

end Solm.SmallStep
