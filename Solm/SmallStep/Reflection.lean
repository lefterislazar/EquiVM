import Solm.SmallStep.Preservation

/-! Semantic reflection for the lowered Solm machine.

The proof uses a length-indexed presentation of finite paths.  Its length is
only a proof device: the public statements remain phrased using `Steps` and
the PAA's `steps_ndet` relation.
-/

namespace Solm.SmallStep

inductive StepsN (cfg : Solm.Config) (contract : LoweredContract) :
    Nat → MachineState → MachineState → Prop where
  | refl : StepsN cfg contract 0 state state
  | head : Step cfg contract source middle →
      StepsN cfg contract length middle target →
      StepsN cfg contract (length + 1) source target

namespace StepsN

theorem single (step : Step cfg contract source target) :
    StepsN cfg contract 1 source target :=
  .head step .refl

theorem toSteps (path : StepsN cfg contract length source target) :
    Steps cfg contract source target := by
  induction path with
  | refl => exact .refl
  | head step _ ih => exact Relation.ReflTransGen.head step ih

theorem append (first : StepsN cfg contract firstLength source middle)
    (second : StepsN cfg contract secondLength middle target) :
    StepsN cfg contract (firstLength + secondLength) source target := by
  induction first with
  | refl => simpa using second
  | head step rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StepsN.head step (ih second)

theorem final_eq {final : MachineState}
    (hfinal : (lts cfg contract).isFinal ((lts cfg contract).label final))
    (path : StepsN cfg contract length final target) : target = final := by
  cases path with
  | refl => rfl
  | head step _ =>
      exact False.elim ((lts cfg contract).hfinal final _ hfinal step)

end StepsN

theorem steps_iff_exists_stepsN :
    Steps cfg contract source target ↔
      ∃ length, StepsN cfg contract length source target := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨0, .refl⟩
    | tail path step ih =>
        obtain ⟨length, pathN⟩ := ih
        exact ⟨length + 1, pathN.append (.single step)⟩
  · rintro ⟨_, path⟩
    exact path.toSteps

theorem execResult_isFinal
    (decoded : state.execResult? = some result) :
    (lts cfg contract).isFinal ((lts cfg contract).label state) := by
  cases state <;> simp_all [MachineState.execResult?, lts, label, isFinal]

theorem stepsN_from_final_eq
    (decoded : source.execResult? = some result)
    (path : StepsN cfg contract length source target) : target = source :=
  path.final_eq (execResult_isFinal decoded)

def ReflectedStmt (cfg : Solm.Config) (contract : LoweredContract)
    (frame : Solm.Frame) (evm : EVM.State) (stmt : Solm.Stmt)
    (next : PC) (loop : LoopTargets) (calls : List ReturnFrame)
    (length : Nat) (final : MachineState) : Prop :=
  ∃ (result : Solm.ExecResult) (remaining : Nat),
    remaining < length ∧
    Solm.ExecStmt cfg frame evm stmt result ∧
    ResultContract frame.contract result ∧
    StepsN cfg contract remaining (resultTarget next loop calls result) final

def ReflectedBlock (cfg : Solm.Config) (contract : LoweredContract)
    (frame : Solm.Frame) (evm : EVM.State) (statements : List Solm.Stmt)
    (next : PC) (loop : LoopTargets) (calls : List ReturnFrame)
    (length : Nat) (final : MachineState) : Prop :=
  ∃ (result : Solm.ExecResult) (remaining : Nat),
    remaining ≤ length ∧
    Solm.ExecBlock cfg frame evm statements result ∧
    ResultContract frame.contract result ∧
    StepsN cfg contract remaining (resultTarget next loop calls result) final

def ReflectedFor (cfg : Solm.Config) (contract : LoweredContract)
    (frame : Solm.Frame) (evm : EVM.State) (condition : Solm.Expr)
    (post body : List Solm.Stmt) (next : PC) (outerLoop : LoopTargets)
    (calls : List ReturnFrame) (length : Nat) (final : MachineState) : Prop :=
  ∃ (result : Solm.ExecResult) (remaining : Nat),
    remaining < length ∧
    Solm.ExecForLoop cfg frame evm condition post body result ∧
    ResultContract frame.contract result ∧
    StepsN cfg contract remaining (resultTarget next outerLoop calls result) final

def ReflectedFunc (cfg : Solm.Config) (contract : LoweredContract)
    (frame : Solm.Frame) (evm : EVM.State) (body : List Solm.Stmt)
    (calls : List ReturnFrame) (length : Nat) (final : MachineState) : Prop :=
  ∃ (result : Solm.ExecResult) (remaining : Nat),
    remaining ≤ length ∧
    Solm.ExecFuncBody cfg frame evm body result ∧
    ResultContract frame.contract result ∧
    StepsN cfg contract remaining (functionTarget calls result) final

structure ReflectionAt (cfg : Solm.Config) (contract : LoweredContract)
    (final : MachineState) (length : Nat) : Prop where
  stmt : ∀ {frame evm stmt next loop calls entry},
    frame.contract = contract.source →
    CompilesStmt contract.code stmt next loop entry →
    StepsN cfg contract length (.running entry frame evm calls) final →
    ReflectedStmt cfg contract frame evm stmt next loop calls length final
  block : ∀ {frame evm statements next loop calls entry},
    frame.contract = contract.source →
    CompilesBlock contract.code statements next loop entry →
    StepsN cfg contract length (.running entry frame evm calls) final →
    ReflectedBlock cfg contract frame evm statements next loop calls length final
  forLoop : ∀ {frame evm condition post body next outerLoop calls
      conditionPC postEntry bodyEntry},
    frame.contract = contract.source →
    contract.code.get? conditionPC = some (.branch condition bodyEntry next) →
    CompilesBlock contract.code post conditionPC strictPostTargets postEntry →
    CompilesBlock contract.code body postEntry
      { breakTarget := some next, continueTarget := some postEntry,
        allowReturn := outerLoop.allowReturn } bodyEntry →
    StepsN cfg contract length (.running conditionPC frame evm calls) final →
    ReflectedFor cfg contract frame evm condition post body next outerLoop calls length final
  func : ∀ {frame evm body calls entry params returnType},
    frame.contract = contract.source →
    CompilesCallable contract.code { params, returnType, body } entry →
    StepsN cfg contract length (.running entry.entry frame evm calls) final →
    ReflectedFunc cfg contract frame evm body calls length final

theorem stepsN_fault_absurd
    (path : StepsN cfg contract length (.fault reason) final)
    (decoded : final.execResult? = some result) : False := by
  have hfinal : (lts cfg contract).isFinal
      ((lts cfg contract).label (.fault reason)) := by
    simp [lts, label, isFinal]
  have heq := path.final_eq hfinal
  subst final
  simp [MachineState.execResult?] at decoded

theorem reflect_atomic_stmt
    (atomic : AtomicStmt stmt)
    (hcode : contract.code.get? entry = some (.atomic stmt next))
    (decoded : final.execResult? = some observed)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm stmt next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | head first tail =>
      cases first <;> simp_all
      · exact
          ⟨.ok _ _, _, by omega, by assumption,
            atomic_preserves_contract atomic (by assumption), tail⟩
      · exact
          ⟨.reverted, _, by omega, by assumption,
            by simp [ResultContract], tail⟩

theorem reflect_return_stmt
    (hallowed : loop.allowReturn = true)
    (hcode : contract.code.get? entry = some (.return expressions))
    (decoded : final.execResult? = some observed)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.return expressions) next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · exact ⟨.returned _ _ (some _), tailLength, by omega,
          .return (by assumption), by simp [ResultContract], by
            simpa [resultTarget, hallowed] using tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .returnRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_blocked_return_stmt
    (_hstrict : loop.allowReturn = false)
    (hcode : contract.code.get? entry = some (.blockedReturn expressions))
    (decoded : final.execResult? = some observed)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.return expressions) next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · exact False.elim (stepsN_fault_absurd tail decoded)
      · exact ⟨.reverted, tailLength, by omega,
          .returnRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_break_stmt
    (compiled : CompilesStmt contract.code .break next loop entry)
    (decoded : final.execResult? = some observed)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm .break next loop calls length final := by
  cases compiled with
  | breakJump htarget hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact ⟨.break frame evm, tailLength, by omega, .break,
            by simp [ResultContract], by
              simpa [resultTarget, abruptTarget, htarget] using tail⟩
  | breakFallthrough htarget hallowed hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact ⟨.break frame evm, tailLength, by omega, .break,
            by simp [ResultContract], by
              simpa [resultTarget, abruptTarget, htarget, hallowed] using tail⟩
  | breakFault htarget hstrict hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact False.elim (stepsN_fault_absurd tail decoded)
  | atomic hatomic _ => cases hatomic

theorem reflect_continue_stmt
    (compiled : CompilesStmt contract.code .continue next loop entry)
    (decoded : final.execResult? = some observed)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm .continue next loop calls length final := by
  cases compiled with
  | continueJump htarget hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact ⟨.continue frame evm, tailLength, by omega, .continue,
            by simp [ResultContract], by
              simpa [resultTarget, abruptTarget, htarget] using tail⟩
  | continueFallthrough htarget hallowed hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact ⟨.continue frame evm, tailLength, by omega, .continue,
            by simp [ResultContract], by
              simpa [resultTarget, abruptTarget, htarget, hallowed] using tail⟩
  | continueFault htarget hstrict hcode =>
      cases path with
      | refl => simp [MachineState.execResult?] at decoded
      | @head source middle tailLength target first tail =>
          cases first <;> simp_all
          exact False.elim (stepsN_fault_absurd tail decoded)
  | atomic hatomic _ => cases hatomic

theorem reflect_ite_stmt
    (sourceEq : frame.contract = contract.source)
    (hcode : contract.code.get? entry = some (.branch condition trueEntry falseEntry))
    (htrue : CompilesBlock contract.code ifTrue next loop trueEntry)
    (hfalse : CompilesBlock contract.code ifFalse next loop falseEntry)
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.ite condition ifTrue ifFalse)
      next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · obtain ⟨result, remaining, hle, hexec, hcontract, hsuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega)) sourceEq htrue tail
        exact ⟨result, remaining, by omega, .iteTrue (by assumption) hexec,
          hcontract, hsuffix⟩
      · obtain ⟨result, remaining, hle, hexec, hcontract, hsuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega)) sourceEq hfalse tail
        exact ⟨result, remaining, by omega, .iteFalse (by assumption) hexec,
          hcontract, hsuffix⟩
      · exact ⟨.reverted, tailLength, by omega,
          .iteCondRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_while_stmt
    (sourceEq : frame.contract = contract.source)
    (hcode : contract.code.get? conditionPC = some (.branch condition bodyEntry next))
    (hbody : CompilesBlock contract.code body conditionPC
      { breakTarget := some next, continueTarget := some conditionPC,
        allowReturn := outerLoop.allowReturn } bodyEntry)
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running conditionPC frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.while condition body)
      next outerLoop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · obtain ⟨bodyResult, remaining, hle, hbodyExec, hbodyContract, hsuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega)) sourceEq hbody tail
        cases bodyResult with
        | ok bodyFrame bodyEvm =>
            have hbodySource : bodyFrame.contract = contract.source :=
              hbodyContract.trans sourceEq
            obtain ⟨result, rest, hlt, hloopExec, hloopContract, hrest⟩ :=
              ReflectionAt.stmt (smaller remaining (by omega)) hbodySource
                (.while (by assumption) hbody) (by simpa [resultTarget] using hsuffix)
            exact ⟨result, rest, by omega,
              .whileTrue (by assumption) hbodyExec hloopExec,
              ResultContract.change hbodyContract hloopContract, hrest⟩
        | returned bodyFrame bodyEvm values =>
            exact ⟨.returned bodyFrame bodyEvm values, remaining, by omega,
              .whileReturn (by assumption) hbodyExec, hbodyContract, hsuffix⟩
        | reverted =>
            exact ⟨.reverted, remaining, by omega,
              .whileRevert (by assumption) hbodyExec, hbodyContract, hsuffix⟩
        | «break» bodyFrame bodyEvm =>
            exact ⟨.ok bodyFrame bodyEvm, remaining, by omega,
              .whileBreak (by assumption) hbodyExec,
              by simpa [ResultContract] using hbodyContract, by
                simpa [resultTarget, abruptTarget] using hsuffix⟩
        | «continue» bodyFrame bodyEvm =>
            have hbodySource : bodyFrame.contract = contract.source :=
              hbodyContract.trans sourceEq
            obtain ⟨result, rest, hlt, hloopExec, hloopContract, hrest⟩ :=
              ReflectionAt.stmt (smaller remaining (by omega)) hbodySource
                (.while (by assumption) hbody) (by
                  simpa [resultTarget, abruptTarget] using hsuffix)
            exact ⟨result, rest, by omega,
              .whileContinue (by assumption) hbodyExec hloopExec,
              ResultContract.change hbodyContract hloopContract, hrest⟩
      · exact ⟨.ok frame evm, tailLength, by omega,
          .whileFalse (by assumption), by simp [ResultContract], tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .whileCondRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_internal_call_stmt
    (sourceEq : frame.contract = contract.source)
    (hcontract : ContractCompiled contract)
    (hcode : contract.code.get? entry = some (.internalCall name args resultName next))
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.internalCall name args resultName)
      next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · rename_i _ _ _ _ values callee locals hlowerLookup hlowerBind hstepCode hargs
        obtain ⟨decl, hlookup, hcallee⟩ :=
          hcontract.reflectLookupInternal (by assumption)
        have hsourceLookup : Solm.lookupCallable? frame.contract name = some decl := by
          rw [sourceEq]
          exact hlookup
        have hbind : Solm.bindParams? decl.params values = some locals := by
          rw [← hcallee.params]
          assumption
        obtain ⟨calleeResult, remaining, hle, hcalleeExec,
            hcalleeContract, hsuffix⟩ :=
          ReflectionAt.func (smaller tailLength (by omega))
            (by simp) hcallee tail
        cases calleeResult with
        | returned calleeFrame calleeEvm returnValues =>
            have hcalleeExec' : Solm.ExecFuncBody cfg
                { frame with locals := locals } evm decl.body
                (.returned calleeFrame calleeEvm returnValues) := by
              simpa [sourceEq] using hcalleeExec
            exact ⟨.ok (Solm.resumeAfterInternalCall frame resultName returnValues)
                calleeEvm,
              remaining, by omega,
              .internalCallReturn (by assumption) hsourceLookup hbind hcalleeExec',
              by simp [ResultContract, Solm.resumeAfterInternalCall], by
                simpa [functionTarget, resultTarget, finishReturn] using hsuffix⟩
        | reverted =>
            have hcalleeExec' : Solm.ExecFuncBody cfg
                { frame with locals := locals } evm decl.body .reverted := by
              simpa [sourceEq] using hcalleeExec
            exact ⟨.reverted, remaining, by omega,
              .internalCallRevert (by assumption) hsourceLookup hbind hcalleeExec',
              by simp [ResultContract], by
                simpa [functionTarget, resultTarget] using hsuffix⟩
        | ok calleeFrame calleeEvm => cases hcalleeExec
        | «break» calleeFrame calleeEvm => cases hcalleeExec
        | «continue» calleeFrame calleeEvm => cases hcalleeExec
      · exact ⟨.reverted, tailLength, by omega,
          .internalCallArgsRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)
      · exact False.elim (stepsN_fault_absurd tail decoded)
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_checked_call_stmt
    (sourceEq : frame.contract = contract.source)
    (hcode : contract.code.get? entry = some
      (.checkedCall receiver name eth args resultName successEntry
        errorName failureEntry perm))
    (hsuccess : CompilesBlock contract.code onSuccess next loop successEntry)
    (hfailure : CompilesBlock contract.code onFailure next loop failureEntry)
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm
      (.checkedCall receiver name eth args resultName onSuccess
        errorName onFailure perm) next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · obtain ⟨result, remaining, hle, hblock, hresultContract, hsuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega))
            (by simp) hsuccess tail
        have hstmt : Solm.ExecStmt cfg frame evm
            (.checkedCall receiver name eth args resultName onSuccess
              errorName onFailure perm) result := by
          have hblock' := hblock
          rw [← sourceEq] at hblock'
          exact .checkedCallSuccess (by assumption) (by assumption) (by assumption)
            (by assumption) (by assumption) hblock'
        exact ⟨result, remaining, by omega,
          hstmt,
          ResultContract.change sourceEq.symm hresultContract, hsuffix⟩
      · obtain ⟨result, remaining, hle, hblock, hresultContract, hsuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega))
            (by simp) hfailure tail
        have hstmt : Solm.ExecStmt cfg frame evm
            (.checkedCall receiver name eth args resultName onSuccess
              errorName onFailure perm) result := by
          have hblock' := hblock
          rw [← sourceEq] at hblock'
          exact .checkedCallFail (by assumption) (by assumption) (by assumption)
            (by assumption) hblock'
        exact ⟨result, remaining, by omega,
          hstmt,
          ResultContract.change sourceEq.symm hresultContract, hsuffix⟩
      · exact ⟨.reverted, tailLength, by omega,
          .checkedCallReturnDecodeRevert (by assumption) (by assumption)
            (by assumption) (by assumption) (by assumption),
          by simp [ResultContract], tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .checkedCallReceiverRevert (by assumption),
          by simp [ResultContract], tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .checkedCallSendRevert (by assumption) (by assumption),
          by simp [ResultContract], tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .checkedCallArgsRevert (by assumption) (by assumption) (by assumption),
          by simp [ResultContract], tail⟩

theorem reflect_for_loop
    (sourceEq : frame.contract = contract.source)
    (hcode : contract.code.get? conditionPC = some (.branch condition bodyEntry next))
    (hpost : CompilesBlock contract.code post conditionPC strictPostTargets postEntry)
    (hbody : CompilesBlock contract.code body postEntry
      { breakTarget := some next, continueTarget := some postEntry,
        allowReturn := outerLoop.allowReturn } bodyEntry)
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running conditionPC frame evm calls) final) :
    ReflectedFor cfg contract frame evm condition post body next outerLoop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      · obtain ⟨bodyResult, bodyRemaining, hbodyLe, hbodyExec,
            hbodyContract, hbodySuffix⟩ :=
          ReflectionAt.block (smaller tailLength (by omega)) sourceEq hbody tail
        cases bodyResult with
        | returned bodyFrame bodyEvm values =>
            exact ⟨.returned bodyFrame bodyEvm values, bodyRemaining, by omega,
              .bodyReturn (by assumption) hbodyExec, hbodyContract, by
                simpa [resultTarget] using hbodySuffix⟩
        | reverted =>
            exact ⟨.reverted, bodyRemaining, by omega,
              .bodyRevert (by assumption) hbodyExec, hbodyContract, hbodySuffix⟩
        | «break» bodyFrame bodyEvm =>
            exact ⟨.ok bodyFrame bodyEvm, bodyRemaining, by omega,
              .bodyBreak (by assumption) hbodyExec,
              by simpa [ResultContract] using hbodyContract, by
                simpa [resultTarget, abruptTarget] using hbodySuffix⟩
        | ok bodyFrame bodyEvm =>
            have hbodySource : bodyFrame.contract = contract.source :=
              hbodyContract.trans sourceEq
            obtain ⟨postResult, postRemaining, hpostLe, hpostExec,
                hpostContract, hpostSuffix⟩ :=
              ReflectionAt.block (smaller bodyRemaining (by omega))
                hbodySource hpost (by simpa [resultTarget] using hbodySuffix)
            cases postResult with
            | ok postFrame postEvm =>
                have hpostSource : postFrame.contract = contract.source :=
                  hpostContract.trans hbodySource
                obtain ⟨result, remaining, hlt, hloopExec,
                    hloopContract, hsuffix⟩ :=
                  ReflectionAt.forLoop (smaller postRemaining (by omega))
                    hpostSource (by assumption) hpost hbody
                    (by simpa [resultTarget] using hpostSuffix)
                exact ⟨result, remaining, by omega,
                  .iterate (by assumption) hbodyExec hpostExec hloopExec,
                  ResultContract.change hbodyContract
                    (ResultContract.change hpostContract hloopContract), hsuffix⟩
            | reverted =>
                exact ⟨.reverted, postRemaining, by omega,
                  .iteratePostRevert (by assumption) hbodyExec hpostExec,
                  by simp [ResultContract], hpostSuffix⟩
            | returned postFrame postEvm values =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, strictPostTargets] using hpostSuffix) decoded)
            | «break» postFrame postEvm =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, abruptTarget, strictPostTargets]
                    using hpostSuffix) decoded)
            | «continue» postFrame postEvm =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, abruptTarget, strictPostTargets]
                    using hpostSuffix) decoded)
        | «continue» bodyFrame bodyEvm =>
            have hbodySource : bodyFrame.contract = contract.source :=
              hbodyContract.trans sourceEq
            obtain ⟨postResult, postRemaining, hpostLe, hpostExec,
                hpostContract, hpostSuffix⟩ :=
              ReflectionAt.block (smaller bodyRemaining (by omega))
                hbodySource hpost
                (by simpa [resultTarget, abruptTarget] using hbodySuffix)
            cases postResult with
            | ok postFrame postEvm =>
                have hpostSource : postFrame.contract = contract.source :=
                  hpostContract.trans hbodySource
                obtain ⟨result, remaining, hlt, hloopExec,
                    hloopContract, hsuffix⟩ :=
                  ReflectionAt.forLoop (smaller postRemaining (by omega))
                    hpostSource (by assumption) hpost hbody
                    (by simpa [resultTarget] using hpostSuffix)
                exact ⟨result, remaining, by omega,
                  .continueIter (by assumption) hbodyExec hpostExec hloopExec,
                  ResultContract.change hbodyContract
                    (ResultContract.change hpostContract hloopContract), hsuffix⟩
            | reverted =>
                exact ⟨.reverted, postRemaining, by omega,
                  .continuePostRevert (by assumption) hbodyExec hpostExec,
                  by simp [ResultContract], hpostSuffix⟩
            | returned postFrame postEvm values =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, strictPostTargets] using hpostSuffix) decoded)
            | «break» postFrame postEvm =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, abruptTarget, strictPostTargets]
                    using hpostSuffix) decoded)
            | «continue» postFrame postEvm =>
                exact False.elim (stepsN_fault_absurd
                  (by simpa [resultTarget, abruptTarget, strictPostTargets]
                    using hpostSuffix) decoded)
      · exact ⟨.ok frame evm, tailLength, by omega,
          .falseDone (by assumption), by simp [ResultContract], tail⟩
      · exact ⟨.reverted, tailLength, by omega,
          .condRevert (by assumption), by simp [ResultContract], tail⟩
      · exact False.elim (stepsN_fault_absurd tail decoded)

theorem reflect_for_stmt
    (sourceEq : frame.contract = contract.source)
    (hentry : contract.code.get? entry = some (.jump initEntry))
    (hcode : contract.code.get? conditionPC = some (.branch condition bodyEntry next))
    (hpost : CompilesBlock contract.code post conditionPC strictPostTargets postEntry)
    (hbody : CompilesBlock contract.code body postEntry
      { breakTarget := some next, continueTarget := some postEntry,
        allowReturn := loop.allowReturn } bodyEntry)
    (hinit : CompilesBlock contract.code init conditionPC
      { allowUnboundAbrupt := false, allowReturn := loop.allowReturn } initEntry)
    (decoded : final.execResult? = some observed)
    (smaller : ∀ m, m < length → ReflectionAt cfg contract final m)
    (path : StepsN cfg contract length (.running entry frame evm calls) final) :
    ReflectedStmt cfg contract frame evm (.for init condition post body)
      next loop calls length final := by
  cases path with
  | refl => simp [MachineState.execResult?] at decoded
  | @head source middle tailLength target first tail =>
      cases first <;> simp_all
      obtain ⟨initResult, initRemaining, hinitLe, hinitExec,
          hinitContract, hinitSuffix⟩ :=
        ReflectionAt.block (smaller tailLength (by omega)) sourceEq hinit tail
      cases initResult with
      | ok initFrame initEvm =>
          have hinitSource : initFrame.contract = contract.source :=
            hinitContract.trans sourceEq
          obtain ⟨result, remaining, hlt, hloopExec,
              hloopContract, hsuffix⟩ :=
            ReflectionAt.forLoop (smaller initRemaining (by omega))
              hinitSource hcode hpost hbody
              (by simpa [resultTarget] using hinitSuffix)
          exact ⟨result, remaining, by omega, .for hinitExec hloopExec,
            ResultContract.change hinitContract hloopContract, hsuffix⟩
      | returned initFrame initEvm values =>
          exact ⟨.returned initFrame initEvm values, initRemaining, by omega,
            .forInitReturn hinitExec, hinitContract, by
              simpa [resultTarget] using hinitSuffix⟩
      | reverted =>
          exact ⟨.reverted, initRemaining, by omega,
            .forInitRevert hinitExec, hinitContract, hinitSuffix⟩
      | «break» initFrame initEvm =>
          exact False.elim (stepsN_fault_absurd
            (by simpa [resultTarget, abruptTarget] using hinitSuffix) decoded)
      | «continue» initFrame initEvm =>
          exact False.elim (stepsN_fault_absurd
            (by simpa [resultTarget, abruptTarget] using hinitSuffix) decoded)

/-- Simultaneous trace reflection, proved by strong induction on the number
    of lowered small steps.  Every recursive use consumes at least one CFG
    command; empty blocks are handled without recursion. -/
theorem reflectionAt (hcontract : ContractCompiled contract)
    (decoded : final.execResult? = some observed) (length : Nat) :
    ReflectionAt cfg contract final length := by
  induction length using Nat.strong_induction_on with
  | h length smaller =>
      let stmtReflection : ∀ {frame evm stmt next loop calls entry},
          frame.contract = contract.source →
          CompilesStmt contract.code stmt next loop entry →
          StepsN cfg contract length (.running entry frame evm calls) final →
          ReflectedStmt cfg contract frame evm stmt next loop calls length final := by
        intro frame evm stmt next loop calls entry sourceEq compiled path
        cases compiled with
        | «while» hcode hbody =>
            exact reflect_while_stmt sourceEq hcode hbody decoded smaller path
        | «for» hentry hcode hpost hbody hinit =>
            exact reflect_for_stmt sourceEq hentry hcode hpost hbody hinit
              decoded smaller path
        | ite hcode htrue hfalse =>
            exact reflect_ite_stmt sourceEq hcode htrue hfalse decoded smaller path
        | internalCall hcode =>
            exact reflect_internal_call_stmt sourceEq hcontract hcode decoded smaller path
        | checkedCall hcode hsuccess hfailure =>
            exact reflect_checked_call_stmt sourceEq hcode hsuccess hfailure
              decoded smaller path
        | «return» hallowed hcode =>
            exact reflect_return_stmt hallowed hcode decoded path
        | returnFault hstrict hcode =>
            exact reflect_blocked_return_stmt hstrict hcode decoded path
        | breakJump htarget hcode =>
            exact reflect_break_stmt (.breakJump htarget hcode) decoded path
        | breakFallthrough htarget hallowed hcode =>
            exact reflect_break_stmt (.breakFallthrough htarget hallowed hcode) decoded path
        | breakFault htarget hstrict hcode =>
            exact reflect_break_stmt (.breakFault htarget hstrict hcode) decoded path
        | continueJump htarget hcode =>
            exact reflect_continue_stmt (.continueJump htarget hcode) decoded path
        | continueFallthrough htarget hallowed hcode =>
            exact reflect_continue_stmt
              (.continueFallthrough htarget hallowed hcode) decoded path
        | continueFault htarget hstrict hcode =>
            exact reflect_continue_stmt (.continueFault htarget hstrict hcode) decoded path
        | atomic hatomic hcode =>
            exact reflect_atomic_stmt hatomic hcode decoded path
      let blockReflection : ∀ {frame evm statements next loop calls entry},
          frame.contract = contract.source →
          CompilesBlock contract.code statements next loop entry →
          StepsN cfg contract length (.running entry frame evm calls) final →
          ReflectedBlock cfg contract frame evm statements next loop calls length final := by
        intro frame evm statements next loop calls entry sourceEq compiled path
        cases compiled with
        | nil =>
            exact ⟨.ok frame evm, length, by omega, .nil,
              by simp [ResultContract], by simpa [resultTarget] using path⟩
        | cons hrest hstmt =>
            obtain ⟨stmtResult, stmtRemaining, hstmtLt, hstmtExec,
                hstmtContract, hstmtSuffix⟩ :=
              stmtReflection sourceEq hstmt path
            cases stmtResult with
            | ok stmtFrame stmtEvm =>
                have hstmtSource : stmtFrame.contract = contract.source :=
                  hstmtContract.trans sourceEq
                obtain ⟨result, remaining, hle, hrestExec,
                    hrestContract, hsuffix⟩ :=
                  ReflectionAt.block (smaller stmtRemaining hstmtLt)
                    hstmtSource hrest (by simpa [resultTarget] using hstmtSuffix)
                exact ⟨result, remaining, by omega,
                  .consNormal hstmtExec hrestExec,
                  ResultContract.change hstmtContract hrestContract, hsuffix⟩
            | returned stmtFrame stmtEvm values =>
                exact ⟨.returned stmtFrame stmtEvm values, stmtRemaining, by omega,
                  .consReturn hstmtExec, hstmtContract, hstmtSuffix⟩
            | reverted =>
                exact ⟨.reverted, stmtRemaining, by omega,
                  .consRevert hstmtExec, hstmtContract, hstmtSuffix⟩
            | «break» stmtFrame stmtEvm =>
                exact ⟨.break stmtFrame stmtEvm, stmtRemaining, by omega,
                  .consBreak hstmtExec, hstmtContract, hstmtSuffix⟩
            | «continue» stmtFrame stmtEvm =>
                exact ⟨.continue stmtFrame stmtEvm, stmtRemaining, by omega,
                  .consContinue hstmtExec, hstmtContract, hstmtSuffix⟩
      let forReflection : ∀ {frame evm condition post body next outerLoop calls
          conditionPC postEntry bodyEntry},
          frame.contract = contract.source →
          contract.code.get? conditionPC = some (.branch condition bodyEntry next) →
          CompilesBlock contract.code post conditionPC strictPostTargets postEntry →
          CompilesBlock contract.code body postEntry
            { breakTarget := some next, continueTarget := some postEntry,
              allowReturn := outerLoop.allowReturn } bodyEntry →
          StepsN cfg contract length (.running conditionPC frame evm calls) final →
          ReflectedFor cfg contract frame evm condition post body next outerLoop calls
            length final := by
        intro frame evm condition post body next outerLoop calls conditionPC
          postEntry bodyEntry sourceEq hcode hpost hbody path
        exact reflect_for_loop sourceEq hcode hpost hbody decoded smaller path
      let funcReflection : ∀ {frame evm body calls entry params returnType},
          frame.contract = contract.source →
          CompilesCallable contract.code { params, returnType, body } entry →
          StepsN cfg contract length (.running entry.entry frame evm calls) final →
          ReflectedFunc cfg contract frame evm body calls length final := by
        intro frame evm body calls entry params returnType sourceEq compiled path
        obtain ⟨done, hdone, hbody⟩ := compiled.body
        obtain ⟨bodyResult, remaining, hle, hbodyExec,
            hbodyContract, hsuffix⟩ :=
          blockReflection sourceEq hbody path
        cases bodyResult with
        | returned bodyFrame bodyEvm values =>
            exact ⟨.returned bodyFrame bodyEvm values, remaining, hle,
              .execBlockRet hbodyExec, hbodyContract, by
                simpa [resultTarget, functionTarget] using hsuffix⟩
        | reverted =>
            exact ⟨.reverted, remaining, hle,
              .execBlockRevert hbodyExec, hbodyContract, hsuffix⟩
        | «break» bodyFrame bodyEvm =>
            exact ⟨.returned bodyFrame bodyEvm none, remaining, hle,
              .execBlockBreak hbodyExec,
              by simpa [ResultContract] using hbodyContract, by
                simpa [resultTarget, functionTarget, abruptTarget] using hsuffix⟩
        | «continue» bodyFrame bodyEvm =>
            exact ⟨.returned bodyFrame bodyEvm none, remaining, hle,
              .execBlockContinue hbodyExec,
              by simpa [ResultContract] using hbodyContract, by
                simpa [resultTarget, functionTarget, abruptTarget] using hsuffix⟩
        | ok bodyFrame bodyEvm =>
            cases hsuffix with
            | refl => simp [resultTarget, MachineState.execResult?] at decoded
            | @head source middle tailLength target first tail =>
                cases first <;> simp_all
                exact ⟨.returned bodyFrame bodyEvm none, tailLength, by omega,
                  .execBlockOK hbodyExec,
                  ResultContract.change sourceEq.symm hbodyContract, by
                    simpa [functionTarget] using tail⟩
      exact
        { stmt := stmtReflection
          block := blockReflection
          forLoop := forReflection
          func := funcReflection }

theorem compiled_callable_reflection
    (hcontract : ContractCompiled contract)
    (sourceEq : frame.contract = contract.source)
    (compiled : CompilesCallable contract.code { params, returnType, body } entry)
    (path : Steps cfg contract (.running entry.entry frame evm []) final)
    (decoded : final.execResult? = some result) :
    Solm.ExecFuncBody cfg frame evm body result := by
  obtain ⟨length, pathN⟩ := steps_iff_exists_stepsN.mp path
  obtain ⟨sourceResult, remaining, hle, execution, hresultContract, suffix⟩ :=
    ReflectionAt.func (reflectionAt hcontract decoded length)
      sourceEq compiled pathN
  have htargetFinal : (lts cfg contract).isFinal
      ((lts cfg contract).label (functionTarget [] sourceResult)) := by
    cases execution <;> simp [lts, label, isFinal, functionTarget, finishReturn]
  have hfinalEq : final = functionTarget [] sourceResult :=
    suffix.final_eq htargetFinal
  subst final
  have hdecodedSource := execFuncBody_target_result execution
  rw [hdecodedSource] at decoded
  have heq : sourceResult = result := Option.some.inj decoded
  subst sourceResult
  exact execution

/-- A terminating returned/reverted run of a certified lowered callable is a
    genuine execution of the original structured Solm body. -/
theorem lowerContract_callable_reflection
    (source : Solm.ContractDecl) (decl : Solm.CallableDecl)
    (entry : CallableEntry) (locals : Solm.Store) (evm : EVM.State)
    (compiledEntry : CompilesCallable (lowerContract source).code decl entry)
    (path : Steps cfg (lowerContract source)
      ((lowerContract source).initialState entry evm locals) final)
    (decoded : final.execResult? = some result) :
    Solm.ExecFuncBody cfg { contract := source, locals } evm decl.body result := by
  exact compiled_callable_reflection (lowerContract_compiled source) rfl
    compiledEntry path decoded

theorem lowered_callable_result_iff
    (source : Solm.ContractDecl) (decl : Solm.CallableDecl)
    (entry : CallableEntry) (locals : Solm.Store) (evm : EVM.State)
    (compiledEntry : CompilesCallable (lowerContract source).code decl entry) :
    Solm.ExecFuncBody cfg { contract := source, locals } evm decl.body result ↔
      ∃ final,
        Steps cfg (lowerContract source)
          ((lowerContract source).initialState entry evm locals) final ∧
        final.execResult? = some result := by
  constructor
  · exact lowerContract_callable_result_preservation source decl entry locals evm
      compiledEntry
  · rintro ⟨final, path, decoded⟩
    exact lowerContract_callable_reflection source decl entry locals evm
      compiledEntry path decoded

theorem lowered_callable_lts_termination_iff
    (source : Solm.ContractDecl) (decl : Solm.CallableDecl)
    (entry : CallableEntry) (locals : Solm.Store) (evm : EVM.State)
    (compiledEntry : CompilesCallable (lowerContract source).code decl entry) :
    Solm.ExecFuncBody cfg { contract := source, locals } evm decl.body result ↔
      ∃ final,
        terminate_at_ndet (lts cfg (lowerContract source))
          ((lowerContract source).initialState entry evm locals) final ∧
        final.execResult? = some result := by
  constructor
  · intro execution
    refine ⟨functionTarget [] result, ?_, execFuncBody_target_result execution⟩
    refine ⟨lowerContract_callable_preservation source decl entry locals evm
      compiledEntry execution, ?_⟩
    cases execution <;> simp [lts, label, isFinal, functionTarget, finishReturn]
  · rintro ⟨final, termination, decoded⟩
    exact lowerContract_callable_reflection source decl entry locals evm
      compiledEntry termination.1 decoded

end Solm.SmallStep
