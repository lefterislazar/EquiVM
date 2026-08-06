import Solm.SmallStep

/-! Correctness of the structured-statement lowering.

The central simulation is continuation-sensitive.  This is important for
loops: the same source result (`ok`, `break`, or `continue`) denotes a
different target control point depending on the enclosing statement.
-/

namespace Solm.SmallStep

def CodeExtends (before after : Array Command) : Prop :=
  ∀ pc command, before.get? pc = some command → after.get? pc = some command

namespace CodeExtends

theorem refl (code : Array Command) : CodeExtends code code :=
  fun _ _ h => h

theorem trans {a b c : Array Command} (hab : CodeExtends a b)
    (hbc : CodeExtends b c) : CodeExtends a c :=
  fun pc command h => hbc pc command (hab pc command h)

theorem push (code : Array Command) (command : Command) :
    CodeExtends code (code.push command) := by
  intro pc old h
  rw [Array.get?, Array.getElem?_push]
  split
  · rename_i heq
    subst pc
    have := (Array.getElem?_eq_none_iff (xs := code) (i := code.size)).2 (by omega)
    change code[code.size]? = some old at h
    rw [this] at h
    contradiction
  · exact h

end CodeExtends

/-- Exactly the source statements deliberately kept as one CFG command. -/
inductive AtomicStmt : Solm.Stmt → Prop where
  | letDecl : AtomicStmt (.letDecl name ty expr)
  | letStorage : AtomicStmt (.letStorage name ref)
  | letGas : AtomicStmt (.letGas name)
  | assign : AtomicStmt (.assign origin slot expr)
  | require : AtomicStmt (.require condition)
  | new : AtomicStmt (.new name value args result salt)
  | externalCall : AtomicStmt (.externalCall receiver name eth args result perm)
  | lowLevelCall : AtomicStmt (.lowLevelCall receiver eth calldata okResult dataResult perm)
  | delegateCall : AtomicStmt (.delegateCall receiver calldata okResult dataResult)
  | push : AtomicStmt (.push ref value)
  | pop : AtomicStmt (.pop ref)
  | delete : AtomicStmt (.delete ref)

mutual

/-- A declarative certificate saying that `entry` is the compiled control
    point for one structured source statement. -/
inductive CompilesStmt (code : Array Command) :
    Solm.Stmt → PC → LoopTargets → PC → Prop where
  | while :
      code.get? conditionPC = some (.branch condition bodyEntry next) →
      CompilesBlock code body conditionPC
        { breakTarget := some next, continueTarget := some conditionPC,
          allowReturn := loop.allowReturn } bodyEntry →
      CompilesStmt code (.while condition body) next loop conditionPC
  | for :
      code.get? entry = some (.jump initEntry) →
      code.get? conditionPC = some (.branch condition bodyEntry next) →
      CompilesBlock code post conditionPC strictPostTargets postEntry →
      CompilesBlock code body postEntry
        { breakTarget := some next, continueTarget := some postEntry,
          allowReturn := loop.allowReturn } bodyEntry →
      CompilesBlock code init conditionPC
        { allowUnboundAbrupt := false, allowReturn := loop.allowReturn } initEntry →
      CompilesStmt code (.for init condition post body) next loop entry
  | ite :
      code.get? entry = some (.branch condition trueEntry falseEntry) →
      CompilesBlock code ifTrue next loop trueEntry →
      CompilesBlock code ifFalse next loop falseEntry →
      CompilesStmt code (.ite condition ifTrue ifFalse) next loop entry
  | internalCall :
      code.get? entry = some (.internalCall name args result next) →
      CompilesStmt code (.internalCall name args result) next loop entry
  | checkedCall :
      code.get? entry = some
        (.checkedCall receiver name eth args result successEntry
          errorResult failureEntry perm) →
      CompilesBlock code onSuccess next loop successEntry →
      CompilesBlock code onFailure next loop failureEntry →
      CompilesStmt code
        (.checkedCall receiver name eth args result onSuccess
          errorResult onFailure perm) next loop entry
  | return :
      loop.allowReturn = true →
      code.get? entry = some (.return values) →
      CompilesStmt code (.return values) next loop entry
  | returnFault :
      loop.allowReturn = false →
      code.get? entry = some (.blockedReturn values) →
      CompilesStmt code (.return values) next loop entry
  | breakJump :
      loop.breakTarget = some target →
      code.get? entry = some (.jump target) →
      CompilesStmt code .break next loop entry
  | breakFallthrough :
      loop.breakTarget = none →
      loop.allowUnboundAbrupt = true →
      code.get? entry = some .fallthrough →
      CompilesStmt code .break next loop entry
  | breakFault :
      loop.breakTarget = none →
      loop.allowUnboundAbrupt = false →
      code.get? entry = some (.fault .malformedBreak) →
      CompilesStmt code .break next loop entry
  | continueJump :
      loop.continueTarget = some target →
      code.get? entry = some (.jump target) →
      CompilesStmt code .continue next loop entry
  | continueFallthrough :
      loop.continueTarget = none →
      loop.allowUnboundAbrupt = true →
      code.get? entry = some .fallthrough →
      CompilesStmt code .continue next loop entry
  | continueFault :
      loop.continueTarget = none →
      loop.allowUnboundAbrupt = false →
      code.get? entry = some (.fault .malformedContinue) →
      CompilesStmt code .continue next loop entry
  | atomic :
      AtomicStmt stmt →
      code.get? entry = some (.atomic stmt next) →
      CompilesStmt code stmt next loop entry

/-- A list is compiled backwards: the first statement enters at `entry` and
    normal completion of the last statement transfers to `next`. -/
inductive CompilesBlock (code : Array Command) :
    List Solm.Stmt → PC → LoopTargets → PC → Prop where
  | nil : CompilesBlock code [] next loop next
  | cons :
      CompilesBlock code rest next loop restEntry →
      CompilesStmt code stmt restEntry loop entry →
      CompilesBlock code (stmt :: rest) next loop entry

end

mutual

theorem CompilesStmt.mono {before after : Array Command}
    (extension : CodeExtends before after)
    (compiled : CompilesStmt before stmt next loop entry) :
    CompilesStmt after stmt next loop entry := by
  cases compiled with
  | «while» hcode hbody =>
      exact .while (extension _ _ hcode) (CompilesBlock.mono extension hbody)
  | «for» hentry hcode hpost hbody hinit =>
      exact .for (extension _ _ hentry) (extension _ _ hcode)
        (CompilesBlock.mono extension hpost)
        (CompilesBlock.mono extension hbody) (CompilesBlock.mono extension hinit)
  | ite hcode htrue hfalse =>
      exact .ite (extension _ _ hcode) (CompilesBlock.mono extension htrue)
        (CompilesBlock.mono extension hfalse)
  | internalCall hcode => exact .internalCall (extension _ _ hcode)
  | checkedCall hcode hsuccess hfailure =>
      exact .checkedCall (extension _ _ hcode)
        (CompilesBlock.mono extension hsuccess) (CompilesBlock.mono extension hfailure)
  | «return» hallowed hcode => exact .return hallowed (extension _ _ hcode)
  | returnFault hstrict hcode =>
      exact .returnFault hstrict (extension _ _ hcode)
  | breakJump htarget hcode => exact .breakJump htarget (extension _ _ hcode)
  | breakFallthrough htarget hallowed hcode =>
      exact .breakFallthrough htarget hallowed (extension _ _ hcode)
  | breakFault htarget hstrict hcode =>
      exact .breakFault htarget hstrict (extension _ _ hcode)
  | continueJump htarget hcode => exact .continueJump htarget (extension _ _ hcode)
  | continueFallthrough htarget hallowed hcode =>
      exact .continueFallthrough htarget hallowed (extension _ _ hcode)
  | continueFault htarget hstrict hcode =>
      exact .continueFault htarget hstrict (extension _ _ hcode)
  | atomic hatomic hcode => exact .atomic hatomic (extension _ _ hcode)

theorem CompilesBlock.mono {before after : Array Command}
    (extension : CodeExtends before after)
    (compiled : CompilesBlock before statements next loop entry) :
    CompilesBlock after statements next loop entry := by
  cases compiled with
  | nil => exact .nil
  | cons hrest hstmt =>
      exact .cons (CompilesBlock.mono extension hrest)
        (CompilesStmt.mono extension hstmt)

end

theorem emit_spec (code : Array Command) (command : Command) :
    (emit command).run code = (code.size, code.push command) := by
  rfl

theorem emit_get (code : Array Command) (command : Command) :
    (code.push command).get? code.size = some command := by
  simp [Array.get?]

theorem patch_reserved_extends {base work : Array Command} {reserved : Command}
    (extension : CodeExtends (base.push reserved) work) (replacement : Command) :
    CodeExtends base (work.set! base.size replacement) := by
  intro pc command hcode
  have hlt : pc < base.size := (Array.getElem?_eq_some_iff.mp hcode).choose
  have hwork : work.get? pc = some command :=
    extension pc command (CodeExtends.push base reserved pc command hcode)
  rw [Array.get?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · rename_i heq
    omega
  · exact hwork

theorem patch_reserved_get {base work : Array Command} {reserved : Command}
    (extension : CodeExtends (base.push reserved) work) (replacement : Command) :
    (work.set! base.size replacement).get? base.size = some replacement := by
  have hpresent : work.get? base.size = some reserved :=
    extension base.size reserved (emit_get base reserved)
  have hlt : base.size < work.size :=
    (Array.getElem?_eq_some_iff.mp hpresent).choose
  simp [Array.get?, Array.set!_eq_setIfInBounds, hlt]

theorem patch_fault_preserves_get {code : Array Command} {faultPC commandPC : PC}
    {command : Command}
    (hfault : code.get? faultPC = some (.fault .invalidPC))
    (hcommand : code.get? commandPC = some command)
    (notFault : command ≠ .fault .invalidPC) (replacement : Command) :
    (code.set! faultPC replacement).get? commandPC = some command := by
  have hne : faultPC ≠ commandPC := by
    intro heq
    subst commandPC
    rw [hfault] at hcommand
    exact notFault (Option.some.inj hcommand.symm)
  rw [Array.get?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  simp only [hne, ↓reduceIte]
  change code[commandPC]? = some command at hcommand
  exact hcommand

mutual

theorem CompilesStmt.patchFault {code : Array Command}
    (hfault : code.get? faultPC = some (.fault .invalidPC))
    (compiled : CompilesStmt code stmt next loop entry)
    (replacement : Command) :
    CompilesStmt (code.set! faultPC replacement) stmt next loop entry := by
  cases compiled with
  | «while» hcode hbody =>
      exact .while (patch_fault_preserves_get hfault hcode (by simp) _)
        (CompilesBlock.patchFault hfault hbody replacement)
  | «for» hentry hcode hpost hbody hinit =>
      exact .for (patch_fault_preserves_get hfault hentry (by simp) _)
        (patch_fault_preserves_get hfault hcode (by simp) _)
        (CompilesBlock.patchFault hfault hpost replacement)
        (CompilesBlock.patchFault hfault hbody replacement)
        (CompilesBlock.patchFault hfault hinit replacement)
  | ite hcode htrue hfalse =>
      exact .ite (patch_fault_preserves_get hfault hcode (by simp) _)
        (CompilesBlock.patchFault hfault htrue replacement)
        (CompilesBlock.patchFault hfault hfalse replacement)
  | internalCall hcode =>
      exact .internalCall (patch_fault_preserves_get hfault hcode (by simp) _)
  | checkedCall hcode hsuccess hfailure =>
      exact .checkedCall (patch_fault_preserves_get hfault hcode (by simp) _)
        (CompilesBlock.patchFault hfault hsuccess replacement)
        (CompilesBlock.patchFault hfault hfailure replacement)
  | «return» hallowed hcode =>
      exact .return hallowed (patch_fault_preserves_get hfault hcode (by simp) _)
  | returnFault hstrict hcode =>
      exact .returnFault hstrict
        (patch_fault_preserves_get hfault hcode (by simp) _)
  | breakJump htarget hcode =>
      exact .breakJump htarget (patch_fault_preserves_get hfault hcode (by simp) _)
  | breakFallthrough htarget hallowed hcode =>
      exact .breakFallthrough htarget hallowed
        (patch_fault_preserves_get hfault hcode (by simp) _)
  | breakFault htarget hstrict hcode =>
      exact .breakFault htarget hstrict
        (patch_fault_preserves_get hfault hcode (by simp) _)
  | continueJump htarget hcode =>
      exact .continueJump htarget (patch_fault_preserves_get hfault hcode (by simp) _)
  | continueFallthrough htarget hallowed hcode =>
      exact .continueFallthrough htarget hallowed
        (patch_fault_preserves_get hfault hcode (by simp) _)
  | continueFault htarget hstrict hcode =>
      exact .continueFault htarget hstrict
        (patch_fault_preserves_get hfault hcode (by simp) _)
  | atomic hatomic hcode =>
      exact .atomic hatomic (patch_fault_preserves_get hfault hcode (by simp) _)

theorem CompilesBlock.patchFault {code : Array Command}
    (hfault : code.get? faultPC = some (.fault .invalidPC))
    (compiled : CompilesBlock code statements next loop entry)
    (replacement : Command) :
    CompilesBlock (code.set! faultPC replacement) statements next loop entry := by
  cases compiled with
  | nil => exact .nil
  | cons hrest hstmt =>
      exact .cons (CompilesBlock.patchFault hfault hrest replacement)
        (CompilesStmt.patchFault hfault hstmt replacement)

end

theorem emit_atomic_compiles (code : Array Command) (stmt : Solm.Stmt)
    (atomic : AtomicStmt stmt)
    (next : PC) (loop : LoopTargets) :
    let result := (emit (.atomic stmt next)).run code
    CodeExtends code result.2 ∧
      CompilesStmt result.2 stmt next loop result.1 :=
  ⟨CodeExtends.push code _, .atomic atomic (emit_get code _)⟩

mutual

/-- The executable lowering produces its declarative compilation certificate
    and never changes commands that were already present. -/
theorem lowerBlock_spec (statements : List Solm.Stmt) (next : PC)
    (loop : LoopTargets) (code : Array Command) :
    let result := (lowerBlock statements next loop).run code
    CodeExtends code result.2 ∧
      CompilesBlock result.2 statements next loop result.1 := by
  cases statements with
  | nil =>
      exact ⟨CodeExtends.refl code, .nil⟩
  | cons stmt rest =>
      let restResult := (lowerBlock rest next loop).run code
      have hrest := lowerBlock_spec rest next loop code
      change CodeExtends code restResult.2 ∧
        CompilesBlock restResult.2 rest next loop restResult.1 at hrest
      let stmtResult := (lowerStmt stmt restResult.1 loop).run restResult.2
      have hstmt := lowerStmt_spec stmt restResult.1 loop restResult.2
      change CodeExtends restResult.2 stmtResult.2 ∧
        CompilesStmt stmtResult.2 stmt restResult.1 loop stmtResult.1 at hstmt
      change CodeExtends code stmtResult.2 ∧
        CompilesBlock stmtResult.2 (stmt :: rest) next loop stmtResult.1
      exact ⟨CodeExtends.trans hrest.1 hstmt.1,
        .cons (hrest.2.mono hstmt.1) hstmt.2⟩

theorem lowerStmt_spec (stmt : Solm.Stmt) (next : PC)
    (loop : LoopTargets) (code : Array Command) :
    let result := (lowerStmt stmt next loop).run code
    CodeExtends code result.2 ∧
      CompilesStmt result.2 stmt next loop result.1 := by
  cases stmt with
  | letDecl name ty expr => exact emit_atomic_compiles code _ .letDecl next loop
  | letStorage name ref => exact emit_atomic_compiles code _ .letStorage next loop
  | letGas name => exact emit_atomic_compiles code _ .letGas next loop
  | assign origin slot expr => exact emit_atomic_compiles code _ .assign next loop
  | require condition => exact emit_atomic_compiles code _ .require next loop
  | new name value args result salt => exact emit_atomic_compiles code _ .new next loop
  | externalCall receiver name eth args result perm =>
      exact emit_atomic_compiles code _ .externalCall next loop
  | lowLevelCall receiver eth calldata okResult dataResult perm =>
      exact emit_atomic_compiles code _ .lowLevelCall next loop
  | delegateCall receiver calldata okResult dataResult =>
      exact emit_atomic_compiles code _ .delegateCall next loop
  | push ref value => exact emit_atomic_compiles code _ .push next loop
  | pop ref => exact emit_atomic_compiles code _ .pop next loop
  | delete ref => exact emit_atomic_compiles code _ .delete next loop
  | internalCall name args result =>
      exact ⟨CodeExtends.push code _, .internalCall (emit_get code _)⟩
  | «return» values =>
      cases hallowed : loop.allowReturn with
      | false =>
          simpa [lowerStmt, hallowed] using
            (show CodeExtends code (code.push (.blockedReturn values)) ∧
                CompilesStmt (code.push (.blockedReturn values))
                  (.return values) next loop code.size from
              ⟨CodeExtends.push code _,
                .returnFault hallowed (emit_get code _)⟩)
      | true =>
          simpa [lowerStmt, hallowed] using
            (show CodeExtends code (code.push (.return values)) ∧
                CompilesStmt (code.push (.return values))
                  (.return values) next loop code.size from
              ⟨CodeExtends.push code _, .return hallowed (emit_get code _)⟩)
  | «break» =>
      cases htarget : loop.breakTarget with
      | none =>
          cases hallowed : loop.allowUnboundAbrupt with
          | false =>
              simpa [lowerStmt, htarget, hallowed] using
                (show CodeExtends code (code.push (.fault .malformedBreak)) ∧
                    CompilesStmt (code.push (.fault .malformedBreak))
                      .break next loop code.size from
                  ⟨CodeExtends.push code _,
                    .breakFault htarget hallowed (emit_get code _)⟩)
          | true =>
              simpa [lowerStmt, htarget, hallowed] using
                (show CodeExtends code (code.push .fallthrough) ∧
                    CompilesStmt (code.push .fallthrough) .break next loop code.size from
                  ⟨CodeExtends.push code _,
                    .breakFallthrough htarget hallowed (emit_get code _)⟩)
      | some target =>
          simpa [lowerStmt, htarget] using
            (show CodeExtends code (code.push (.jump target)) ∧
                CompilesStmt (code.push (.jump target)) .break next loop code.size from
              ⟨CodeExtends.push code _, .breakJump htarget (emit_get code _)⟩)
  | «continue» =>
      cases htarget : loop.continueTarget with
      | none =>
          cases hallowed : loop.allowUnboundAbrupt with
          | false =>
              simpa [lowerStmt, htarget, hallowed] using
                (show CodeExtends code (code.push (.fault .malformedContinue)) ∧
                    CompilesStmt (code.push (.fault .malformedContinue))
                      .continue next loop code.size from
                  ⟨CodeExtends.push code _,
                    .continueFault htarget hallowed (emit_get code _)⟩)
          | true =>
              simpa [lowerStmt, htarget, hallowed] using
                (show CodeExtends code (code.push .fallthrough) ∧
                    CompilesStmt (code.push .fallthrough) .continue next loop code.size from
                  ⟨CodeExtends.push code _,
                    .continueFallthrough htarget hallowed (emit_get code _)⟩)
      | some target =>
          simpa [lowerStmt, htarget] using
            (show CodeExtends code (code.push (.jump target)) ∧
                CompilesStmt (code.push (.jump target)) .continue next loop code.size from
              ⟨CodeExtends.push code _, .continueJump htarget (emit_get code _)⟩)
  | «while» condition body =>
      let reservedCode := code.push (.fault .invalidPC)
      let conditionPC := code.size
      let bodyResult := (lowerBlock body conditionPC
        { breakTarget := some next, continueTarget := some conditionPC,
          allowReturn := loop.allowReturn }).run reservedCode
      have hbody := lowerBlock_spec body conditionPC
        { breakTarget := some next, continueTarget := some conditionPC,
          allowReturn := loop.allowReturn } reservedCode
      change CodeExtends reservedCode bodyResult.2 ∧
        CompilesBlock bodyResult.2 body conditionPC
          { breakTarget := some next, continueTarget := some conditionPC,
            allowReturn := loop.allowReturn }
          bodyResult.1 at hbody
      let finalCode := bodyResult.2.set! conditionPC
        (.branch condition bodyResult.1 next)
      change CodeExtends code finalCode ∧
        CompilesStmt finalCode (.while condition body) next loop conditionPC
      have hext : CodeExtends code finalCode :=
        patch_reserved_extends hbody.1 _
      have hfault : bodyResult.2.get? conditionPC = some (.fault .invalidPC) :=
        hbody.1 conditionPC _ (emit_get code _)
      exact ⟨hext, .while (patch_reserved_get hbody.1 _)
        (hbody.2.patchFault hfault _)⟩
  | «for» init condition post body =>
      let reservedCode := code.push (.fault .invalidPC)
      let conditionPC := code.size
      let postResult :=
        (lowerBlock post conditionPC strictPostTargets).run reservedCode
      have hpost := lowerBlock_spec post conditionPC strictPostTargets reservedCode
      change CodeExtends reservedCode postResult.2 ∧
        CompilesBlock postResult.2 post conditionPC strictPostTargets postResult.1 at hpost
      let bodyLoop : LoopTargets :=
        { breakTarget := some next, continueTarget := some postResult.1,
          allowReturn := loop.allowReturn }
      let bodyResult := (lowerBlock body postResult.1 bodyLoop).run postResult.2
      have hbody := lowerBlock_spec body postResult.1 bodyLoop postResult.2
      change CodeExtends postResult.2 bodyResult.2 ∧
        CompilesBlock bodyResult.2 body postResult.1 bodyLoop bodyResult.1 at hbody
      let patchedCode := bodyResult.2.set! conditionPC
        (.branch condition bodyResult.1 next)
      have hreservedBody : CodeExtends reservedCode bodyResult.2 :=
        CodeExtends.trans hpost.1 hbody.1
      have hfault : bodyResult.2.get? conditionPC = some (.fault .invalidPC) :=
        hreservedBody conditionPC _ (emit_get code _)
      let initResult :=
        (lowerBlock init conditionPC
          { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }).run patchedCode
      have hinit := lowerBlock_spec init conditionPC
        { allowUnboundAbrupt := false, allowReturn := loop.allowReturn } patchedCode
      change CodeExtends patchedCode initResult.2 ∧
        CompilesBlock initResult.2 init conditionPC
          { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }
          initResult.1 at hinit
      let finalCode := initResult.2.push (.jump initResult.1)
      change CodeExtends code finalCode ∧
        CompilesStmt finalCode (.for init condition post body) next loop initResult.2.size
      have hpatchExt : CodeExtends code patchedCode :=
        patch_reserved_extends hreservedBody _
      have hpostPatched :
          CompilesBlock patchedCode post conditionPC strictPostTargets postResult.1 :=
        (hpost.2.mono hbody.1).patchFault hfault _
      have hbodyPatched : CompilesBlock patchedCode body postResult.1 bodyLoop bodyResult.1 :=
        hbody.2.patchFault hfault _
      have htoInit := CodeExtends.trans hpatchExt hinit.1
      have hpush := CodeExtends.push initResult.2 (.jump initResult.1)
      exact ⟨CodeExtends.trans htoInit hpush,
        .for (emit_get initResult.2 _)
          (hpush _ _ (hinit.1 _ _ (patch_reserved_get hreservedBody _)))
          ((hpostPatched.mono hinit.1).mono hpush)
          ((hbodyPatched.mono hinit.1).mono hpush)
          (hinit.2.mono hpush)⟩
  | ite condition ifTrue ifFalse =>
      let trueResult := (lowerBlock ifTrue next loop).run code
      have htrue := lowerBlock_spec ifTrue next loop code
      change CodeExtends code trueResult.2 ∧
        CompilesBlock trueResult.2 ifTrue next loop trueResult.1 at htrue
      let falseResult := (lowerBlock ifFalse next loop).run trueResult.2
      have hfalse := lowerBlock_spec ifFalse next loop trueResult.2
      change CodeExtends trueResult.2 falseResult.2 ∧
        CompilesBlock falseResult.2 ifFalse next loop falseResult.1 at hfalse
      let finalCode := falseResult.2.push
        (.branch condition trueResult.1 falseResult.1)
      change CodeExtends code finalCode ∧
        CompilesStmt finalCode (.ite condition ifTrue ifFalse) next loop falseResult.2.size
      have hpush := CodeExtends.push falseResult.2
        (.branch condition trueResult.1 falseResult.1)
      exact ⟨CodeExtends.trans (CodeExtends.trans htrue.1 hfalse.1) hpush,
        .ite (emit_get falseResult.2 _)
          ((htrue.2.mono hfalse.1).mono hpush) (hfalse.2.mono hpush)⟩
  | checkedCall receiver name eth args result onSuccess errorResult onFailure perm =>
      let successResult := (lowerBlock onSuccess next loop).run code
      have hsuccess := lowerBlock_spec onSuccess next loop code
      change CodeExtends code successResult.2 ∧
        CompilesBlock successResult.2 onSuccess next loop successResult.1 at hsuccess
      let failureResult := (lowerBlock onFailure next loop).run successResult.2
      have hfailure := lowerBlock_spec onFailure next loop successResult.2
      change CodeExtends successResult.2 failureResult.2 ∧
        CompilesBlock failureResult.2 onFailure next loop failureResult.1 at hfailure
      let command := Command.checkedCall receiver name eth args result successResult.1
        errorResult failureResult.1 perm
      let finalCode := failureResult.2.push command
      change CodeExtends code finalCode ∧
        CompilesStmt finalCode
          (.checkedCall receiver name eth args result onSuccess errorResult onFailure perm)
          next loop failureResult.2.size
      have hpush := CodeExtends.push failureResult.2 command
      exact ⟨CodeExtends.trans (CodeExtends.trans hsuccess.1 hfailure.1) hpush,
        .checkedCall (emit_get failureResult.2 command)
          ((hsuccess.2.mono hfailure.1).mono hpush) (hfailure.2.mono hpush)⟩

end

structure CompilesCallable (code : Array Command) (decl : Solm.CallableDecl)
    (entry : CallableEntry) : Prop where
  params : entry.params = decl.params
  returnType : entry.returnType = decl.returnType
  body : ∃ done, code.get? done = some .fallthrough ∧
    CompilesBlock code decl.body done {} entry.entry

theorem CompilesCallable.mono {before after : Array Command}
    (extension : CodeExtends before after)
    (compiled : CompilesCallable before decl entry) :
    CompilesCallable after decl entry := by
  obtain ⟨done, hdone, hbody⟩ := compiled.body
  exact ⟨compiled.params, compiled.returnType,
    done, extension _ _ hdone, hbody.mono extension⟩

def CompilesFunctionEntries (code : Array Command) :
    List Solm.FunctionDecl → List CallableEntry → Prop
  | [], [] => True
  | function :: functions, entry :: entries =>
      entry.name = function.name ∧
      CompilesCallable code function.toCallable entry ∧
      CompilesFunctionEntries code functions entries
  | _, _ => False

def CompilesTransitionEntries (code : Array Command) :
    List Solm.TransitionDecl → List CallableEntry → Prop
  | [], [] => True
  | transition :: transitions, entry :: entries =>
      entry.name = transition.name ∧
      CompilesCallable code transition.toCallable entry ∧
      CompilesTransitionEntries code transitions entries
  | _, _ => False

theorem CompilesFunctionEntries.mono {before after : Array Command}
    (extension : CodeExtends before after) :
    ∀ {functions entries}, CompilesFunctionEntries before functions entries →
      CompilesFunctionEntries after functions entries := by
  intro functions
  induction functions with
  | nil => intro entries h; cases entries <;> simp_all [CompilesFunctionEntries]
  | cons function functions ih =>
      intro entries h
      cases entries with
      | nil => simp [CompilesFunctionEntries] at h
      | cons entry entries =>
          rcases h with ⟨hname, hentry, hrest⟩
          exact ⟨hname, hentry.mono extension, ih hrest⟩

theorem CompilesTransitionEntries.mono {before after : Array Command}
    (extension : CodeExtends before after) :
    ∀ {transitions entries}, CompilesTransitionEntries before transitions entries →
      CompilesTransitionEntries after transitions entries := by
  intro transitions
  induction transitions with
  | nil => intro entries h; cases entries <;> simp_all [CompilesTransitionEntries]
  | cons transition transitions ih =>
      intro entries h
      cases entries with
      | nil => simp [CompilesTransitionEntries] at h
      | cons entry entries =>
          rcases h with ⟨hname, hentry, hrest⟩
          exact ⟨hname, hentry.mono extension, ih hrest⟩

theorem lowerCallable_spec (name : Solm.Ident) (decl : Solm.CallableDecl)
    (code : Array Command) :
    let result := (lowerCallable name decl).run code
    CodeExtends code result.2 ∧ result.1.name = name ∧
      CompilesCallable result.2 decl result.1 := by
  let withDone := code.push .fallthrough
  let bodyResult := (lowerBlock decl.body code.size {}).run withDone
  have hbody := lowerBlock_spec decl.body code.size {} withDone
  change CodeExtends withDone bodyResult.2 ∧
    CompilesBlock bodyResult.2 decl.body code.size {} bodyResult.1 at hbody
  change CodeExtends code bodyResult.2 ∧ name = name ∧
    CompilesCallable bodyResult.2 decl
      { name, params := decl.params, returnType := decl.returnType, entry := bodyResult.1 }
  exact ⟨CodeExtends.trans (CodeExtends.push code _) hbody.1, rfl,
    rfl, rfl, code.size, hbody.1 _ _ (emit_get code _), hbody.2⟩

mutual

theorem lowerFunctions_spec (functions : List Solm.FunctionDecl)
    (code : Array Command) :
    let result := (lowerFunctions functions).run code
    CodeExtends code result.2 ∧
      CompilesFunctionEntries result.2 functions result.1 := by
  cases functions with
  | nil => exact ⟨CodeExtends.refl code, trivial⟩
  | cons function functions =>
      let headResult := (lowerCallable function.name function.toCallable).run code
      have hhead := lowerCallable_spec function.name function.toCallable code
      change CodeExtends code headResult.2 ∧ headResult.1.name = function.name ∧
        CompilesCallable headResult.2 function.toCallable headResult.1 at hhead
      let tailResult := (lowerFunctions functions).run headResult.2
      have htail := lowerFunctions_spec functions headResult.2
      change CodeExtends headResult.2 tailResult.2 ∧
        CompilesFunctionEntries tailResult.2 functions tailResult.1 at htail
      change CodeExtends code tailResult.2 ∧
        CompilesFunctionEntries tailResult.2 (function :: functions)
          (headResult.1 :: tailResult.1)
      exact ⟨CodeExtends.trans hhead.1 htail.1, hhead.2.1,
        hhead.2.2.mono htail.1, htail.2⟩

theorem lowerTransitions_spec (transitions : List Solm.TransitionDecl)
    (code : Array Command) :
    let result := (lowerTransitions transitions).run code
    CodeExtends code result.2 ∧
      CompilesTransitionEntries result.2 transitions result.1 := by
  cases transitions with
  | nil => exact ⟨CodeExtends.refl code, trivial⟩
  | cons transition transitions =>
      let headResult := (lowerCallable transition.name transition.toCallable).run code
      have hhead := lowerCallable_spec transition.name transition.toCallable code
      change CodeExtends code headResult.2 ∧ headResult.1.name = transition.name ∧
        CompilesCallable headResult.2 transition.toCallable headResult.1 at hhead
      let tailResult := (lowerTransitions transitions).run headResult.2
      have htail := lowerTransitions_spec transitions headResult.2
      change CodeExtends headResult.2 tailResult.2 ∧
        CompilesTransitionEntries tailResult.2 transitions tailResult.1 at htail
      change CodeExtends code tailResult.2 ∧
        CompilesTransitionEntries tailResult.2 (transition :: transitions)
          (headResult.1 :: tailResult.1)
      exact ⟨CodeExtends.trans hhead.1 htail.1, hhead.2.1,
        hhead.2.2.mono htail.1, htail.2⟩

end

def CompilesOptionalTransition (code : Array Command) :
    Option Solm.TransitionDecl → Option CallableEntry → Prop
  | none, none => True
  | some transition, some entry =>
      entry.name = transition.name ∧
      CompilesCallable code transition.toCallable entry
  | _, _ => False

theorem CompilesOptionalTransition.mono {before after : Array Command}
    (extension : CodeExtends before after) :
    ∀ {transition entry}, CompilesOptionalTransition before transition entry →
      CompilesOptionalTransition after transition entry := by
  intro transition entry h
  cases transition <;> cases entry <;> simp_all [CompilesOptionalTransition]
  exact h.2.mono extension

theorem lowerOptionalTransition_spec (transition : Option Solm.TransitionDecl)
    (code : Array Command) :
    let result := (lowerOptionalTransition transition).run code
    CodeExtends code result.2 ∧
      CompilesOptionalTransition result.2 transition result.1 := by
  cases transition with
  | none => exact ⟨CodeExtends.refl code, trivial⟩
  | some transition =>
      have h := lowerCallable_spec transition.name transition.toCallable code
      change CodeExtends code ((lowerCallable transition.name transition.toCallable).run code).2 ∧
        CompilesOptionalTransition
          ((lowerCallable transition.name transition.toCallable).run code).2
          (some transition)
          (some ((lowerCallable transition.name transition.toCallable).run code).1)
      exact ⟨h.1, h.2.1, h.2.2⟩

structure ContractCompiled (lowered : LoweredContract) : Prop where
  constructor : CompilesCallable lowered.code
    { params := lowered.source.ctor.params, body := lowered.source.ctor.body }
    lowered.constructorEntry
  functions : CompilesFunctionEntries lowered.code lowered.source.functions
    lowered.functionEntries
  transitions : CompilesTransitionEntries lowered.code lowered.source.transitions
    lowered.transitionEntries
  receive : CompilesOptionalTransition lowered.code lowered.source.receive
    lowered.receiveEntry
  fallback : CompilesOptionalTransition lowered.code lowered.source.fallback
    lowered.fallbackEntry

/-- Whole-contract compilation is certified, not merely the lowering of an
    isolated statement.  In particular this is what makes interprocedural
    simulation possible. -/
theorem lowerContract_compiled (source : Solm.ContractDecl) :
    ContractCompiled (lowerContract source) := by
  let constructorDecl : Solm.CallableDecl :=
    { params := source.ctor.params, body := source.ctor.body }
  let constructorResult := (lowerCallable "<constructor>" constructorDecl).run #[]
  have hconstructor := lowerCallable_spec "<constructor>" constructorDecl #[]
  let functionsResult := (lowerFunctions source.functions).run constructorResult.2
  have hfunctions := lowerFunctions_spec source.functions constructorResult.2
  let transitionsResult :=
    (lowerTransitions source.transitions).run functionsResult.2
  have htransitions := lowerTransitions_spec source.transitions functionsResult.2
  let receiveResult :=
    (lowerOptionalTransition source.receive).run transitionsResult.2
  have hreceive := lowerOptionalTransition_spec source.receive transitionsResult.2
  let fallbackResult :=
    (lowerOptionalTransition source.fallback).run receiveResult.2
  have hfallback := lowerOptionalTransition_spec source.fallback receiveResult.2
  change CodeExtends #[] constructorResult.2 ∧
    constructorResult.1.name = "<constructor>" ∧
    CompilesCallable constructorResult.2 constructorDecl constructorResult.1 at hconstructor
  change CodeExtends constructorResult.2 functionsResult.2 ∧ _ at hfunctions
  change CodeExtends functionsResult.2 transitionsResult.2 ∧ _ at htransitions
  change CodeExtends transitionsResult.2 receiveResult.2 ∧ _ at hreceive
  change CodeExtends receiveResult.2 fallbackResult.2 ∧ _ at hfallback
  let constructorToFinal := CodeExtends.trans hfunctions.1
    (CodeExtends.trans htransitions.1 (CodeExtends.trans hreceive.1 hfallback.1))
  let functionsToFinal := CodeExtends.trans htransitions.1
    (CodeExtends.trans hreceive.1 hfallback.1)
  let transitionsToFinal := CodeExtends.trans hreceive.1 hfallback.1
  change ContractCompiled
    { source := source
      code := fallbackResult.2
      constructorEntry := constructorResult.1
      functionEntries := functionsResult.1
      transitionEntries := transitionsResult.1
      receiveEntry := receiveResult.1
      fallbackEntry := fallbackResult.1 }
  exact
    { constructor := hconstructor.2.2.mono constructorToFinal
      functions := hfunctions.2.mono functionsToFinal
      transitions := htransitions.2.mono transitionsToFinal
      receive := hreceive.2.mono hfallback.1
      fallback := hfallback.2 }

theorem CompilesFunctionEntries.lookup {code functions entries name decl}
    (compiled : CompilesFunctionEntries code functions entries)
    (found : Solm.lookupFunction? functions name = some decl) :
    ∃ entry, lookupEntry? entries name = some entry ∧
      CompilesCallable code decl entry := by
  induction functions generalizing entries with
  | nil => simp [Solm.lookupFunction?] at found
  | cons function functions ih =>
      cases entries with
      | nil => simp [CompilesFunctionEntries] at compiled
      | cons entry entries =>
          rcases compiled with ⟨hname, hentry, hrest⟩
          simp only [Solm.lookupFunction?] at found
          split at found
          · rename_i heq
            have hdecl : function.toCallable = decl := Option.some.inj found
            subst decl
            refine ⟨entry, ?_, hentry⟩
            simp [lookupEntry?, hname, heq]
          · rename_i hne
            obtain ⟨foundEntry, hlookup, hcompiled⟩ := ih hrest found
            refine ⟨foundEntry, ?_, hcompiled⟩
            simp [lookupEntry?, hname, hne, hlookup]

theorem CompilesTransitionEntries.lookup {code transitions entries name decl}
    (compiled : CompilesTransitionEntries code transitions entries)
    (found : Solm.lookupTransition? transitions name = some decl) :
    ∃ entry, lookupEntry? entries name = some entry ∧
      CompilesCallable code decl entry := by
  induction transitions generalizing entries with
  | nil => simp [Solm.lookupTransition?] at found
  | cons transition transitions ih =>
      cases entries with
      | nil => simp [CompilesTransitionEntries] at compiled
      | cons entry entries =>
          rcases compiled with ⟨hname, hentry, hrest⟩
          simp only [Solm.lookupTransition?] at found
          split at found
          · rename_i heq
            have hdecl : transition.toCallable = decl := Option.some.inj found
            subst decl
            refine ⟨entry, ?_, hentry⟩
            simp [lookupEntry?, hname, heq]
          · rename_i hne
            obtain ⟨foundEntry, hlookup, hcompiled⟩ := ih hrest found
            refine ⟨foundEntry, ?_, hcompiled⟩
            simp [lookupEntry?, hname, hne, hlookup]

theorem CompilesFunctionEntries.lookup_none {code functions entries name}
    (compiled : CompilesFunctionEntries code functions entries)
    (notFound : Solm.lookupFunction? functions name = none) :
    lookupEntry? entries name = none := by
  induction functions generalizing entries with
  | nil =>
      cases entries <;> simp_all [CompilesFunctionEntries, lookupEntry?]
  | cons function functions ih =>
      cases entries with
      | nil => simp [CompilesFunctionEntries] at compiled
      | cons entry entries =>
          rcases compiled with ⟨hname, _, hrest⟩
          simp only [Solm.lookupFunction?] at notFound
          split at notFound
          · contradiction
          · rename_i hne
            simp [lookupEntry?, hname, hne, ih hrest notFound]

theorem CompilesFunctionEntries.reflect_lookup {code functions entries name entry}
    (compiled : CompilesFunctionEntries code functions entries)
    (found : lookupEntry? entries name = some entry) :
    ∃ decl, Solm.lookupFunction? functions name = some decl ∧
      CompilesCallable code decl entry := by
  induction functions generalizing entries with
  | nil =>
      cases entries <;> simp_all [CompilesFunctionEntries, lookupEntry?]
  | cons function functions ih =>
      cases entries with
      | nil => simp [CompilesFunctionEntries] at compiled
      | cons head entries =>
          rcases compiled with ⟨hname, hhead, hrest⟩
          simp only [lookupEntry?] at found
          split at found
          · rename_i heq
            have hentry : head = entry := Option.some.inj found
            subst entry
            have hfunction : function.name = name := hname.symm.trans heq
            exact ⟨function.toCallable,
              by simp [Solm.lookupFunction?, hfunction], hhead⟩
          · rename_i hne
            obtain ⟨decl, hsource, hcompiled⟩ := ih hrest found
            have hfunction : function.name ≠ name := by
              intro heq
              exact hne (hname.trans heq)
            exact ⟨decl,
              by simp [Solm.lookupFunction?, hfunction, hsource], hcompiled⟩

theorem CompilesTransitionEntries.reflect_lookup {code transitions entries name entry}
    (compiled : CompilesTransitionEntries code transitions entries)
    (found : lookupEntry? entries name = some entry) :
    ∃ decl, Solm.lookupTransition? transitions name = some decl ∧
      CompilesCallable code decl entry := by
  induction transitions generalizing entries with
  | nil =>
      cases entries <;> simp_all [CompilesTransitionEntries, lookupEntry?]
  | cons transition transitions ih =>
      cases entries with
      | nil => simp [CompilesTransitionEntries] at compiled
      | cons head entries =>
          rcases compiled with ⟨hname, hhead, hrest⟩
          simp only [lookupEntry?] at found
          split at found
          · rename_i heq
            have hentry : head = entry := Option.some.inj found
            subst entry
            have htransition : transition.name = name := hname.symm.trans heq
            exact ⟨transition.toCallable,
              by simp [Solm.lookupTransition?, htransition], hhead⟩
          · rename_i hne
            obtain ⟨decl, hsource, hcompiled⟩ := ih hrest found
            have htransition : transition.name ≠ name := by
              intro heq
              exact hne (hname.trans heq)
            exact ⟨decl,
              by simp [Solm.lookupTransition?, htransition, hsource], hcompiled⟩

theorem ContractCompiled.lookupInternal {lowered : LoweredContract}
    (compiled : ContractCompiled lowered)
    (found : Solm.lookupCallable? lowered.source name = some decl) :
    ∃ entry, lowered.lookupInternal? name = some entry ∧
      CompilesCallable lowered.code decl entry := by
  unfold Solm.lookupCallable? at found
  unfold LoweredContract.lookupInternal?
  cases hfunction : Solm.lookupFunction? lowered.source.functions name with
  | some function =>
      have hfound := found
      simp [hfunction] at hfound
      have hdecl : function = decl := hfound
      subst decl
      obtain ⟨entry, hlookup, hcompiled⟩ :=
        compiled.functions.lookup hfunction
      exact ⟨entry, by simp [hlookup], hcompiled⟩
  | none =>
      have htransition : Solm.lookupTransition? lowered.source.transitions name = some decl := by
        simpa [hfunction] using found
      obtain ⟨entry, hlookup, hcompiled⟩ :=
        compiled.transitions.lookup htransition
      have hnone := compiled.functions.lookup_none hfunction
      exact ⟨entry, by simp [hnone, hlookup], hcompiled⟩

theorem ContractCompiled.reflectLookupInternal {lowered : LoweredContract}
    (compiled : ContractCompiled lowered)
    (found : lowered.lookupInternal? name = some entry) :
    ∃ decl, Solm.lookupCallable? lowered.source name = some decl ∧
      CompilesCallable lowered.code decl entry := by
  unfold LoweredContract.lookupInternal? at found
  cases hfunction : lookupEntry? lowered.functionEntries name with
  | some functionEntry =>
      have hfound := found
      simp [hfunction] at hfound
      have hentry : functionEntry = entry := hfound
      subst entry
      obtain ⟨decl, hsource, hcompiled⟩ :=
        compiled.functions.reflect_lookup hfunction
      exact ⟨decl, by simp [Solm.lookupCallable?, hsource], hcompiled⟩
  | none =>
      have htransition : lookupEntry? lowered.transitionEntries name = some entry := by
        simpa [hfunction] using found
      obtain ⟨decl, hsource, hcompiled⟩ :=
        compiled.transitions.reflect_lookup htransition
      have hsourceNone : Solm.lookupFunction? lowered.source.functions name = none := by
        by_contra hnot
        cases hsourceFunction : Solm.lookupFunction? lowered.source.functions name with
        | none => contradiction
        | some sourceFunction =>
            obtain ⟨functionEntry, hentryLookup, _⟩ :=
              compiled.functions.lookup hsourceFunction
            rw [hentryLookup] at hfunction
            contradiction
      exact ⟨decl, by simp [Solm.lookupCallable?, hsourceNone, hsource], hcompiled⟩

abbrev Steps (cfg : Solm.Config) (contract : LoweredContract) :=
  Relation.ReflTransGen (Step cfg contract)

theorem Steps.single (step : Step cfg contract source target) :
    Steps cfg contract source target :=
  Relation.ReflTransGen.single step

theorem Steps.comp {middle : MachineState}
    (first : Steps cfg contract source middle)
    (second : Steps cfg contract middle target) :
    Steps cfg contract source target :=
  first.trans second

def abruptTarget (target : Option PC) (allowUnbound : Bool) (fault : Fault)
    (frame : Solm.Frame) (evm : EVM.State) (calls : List ReturnFrame) : MachineState :=
  match target with
  | some pc => .running pc frame evm calls
  | none =>
      if allowUnbound then finishReturn frame evm none calls else .fault fault

/-- Interpretation of every block result under its CFG continuations. -/
def resultTarget (next : PC) (loop : LoopTargets) (calls : List ReturnFrame) :
    Solm.ExecResult → MachineState
  | .ok frame evm => .running next frame evm calls
  | .returned frame evm values =>
      if loop.allowReturn then finishReturn frame evm values calls
      else .fault .malformedReturn
  | .reverted => .reverted
  | .break frame evm =>
      abruptTarget loop.breakTarget loop.allowUnboundAbrupt .malformedBreak frame evm calls
  | .continue frame evm =>
      abruptTarget loop.continueTarget loop.allowUnboundAbrupt .malformedContinue frame evm calls

def functionTarget (calls : List ReturnFrame) : Solm.ExecResult → MachineState
  | .returned frame evm values => finishReturn frame evm values calls
  | .reverted => .reverted
  | .ok frame evm | .break frame evm | .continue frame evm =>
      finishReturn frame evm none calls

def ResultContract (source : Solm.ContractDecl) : Solm.ExecResult → Prop
  | .returned frame _ _ | .ok frame _ | .break frame _ | .continue frame _ =>
      frame.contract = source
  | .reverted => True

theorem ResultContract.change (equal : middle = source)
    (preserved : ResultContract middle result) : ResultContract source result := by
  cases result <;> simp_all [ResultContract]

theorem assignStorageRef_contract
    (assigned : Solm.assignStorageRef? cfg frame evm origin slot value =
      .ok (frame', evm')) :
    frame'.contract = frame.contract := by
  unfold Solm.assignStorageRef? at assigned
  cases origin with
  | localVar =>
      generalize hlookup : frame.locals.get? slot.base = lookup at assigned
      cases lookup with
      | none => simp at assigned
      | some root =>
          generalize hupdate : Solm.updateLocalPath? cfg frame evm root slot.steps value =
            update at assigned
          cases update <;> simp_all [bind, Solm.EvalResult.bind, pure]
          rcases assigned with ⟨rfl, rfl⟩
          rfl
  | storage =>
      generalize hresolve : Solm.resolveStorageRef? cfg frame evm slot = resolved at assigned
      cases resolved with
      | revert => simp [bind, Solm.EvalResult.bind] at assigned
      | error error => simp [bind, Solm.EvalResult.bind] at assigned
      | ok reference =>
          cases value <;> simp only [bind, Solm.EvalResult.bind, pure] at assigned
          case struct | array | bytes =>
            generalize hwrite : Solm.writeStorage? cfg evm reference.1 reference.2 _ =
              written at assigned
            cases written <;> simp_all
          all_goals
            generalize hlayout : cfg.storage.layout reference.1 evm = location at assigned
            cases location with
            | none =>
                simp [Solm.EvalResult.ofOption] at assigned
            | some location =>
                simp only [Solm.EvalResult.ofOption] at assigned
                split at assigned <;>
                  simp_all

theorem atomic_preserves_contract (atomic : AtomicStmt stmt)
    (execution : Solm.ExecStmt cfg frame evm stmt result) :
    ResultContract frame.contract result := by
  cases atomic <;> cases execution <;> simp [ResultContract]
  exact assignStorageRef_contract (by assumption)

theorem atomic_simulation (cfg : Solm.Config) (contract : LoweredContract)
    (hcode : contract.code.get? entry = some (.atomic stmt next))
    (atomic : AtomicStmt stmt)
    (execution : Solm.ExecStmt cfg frame evm stmt result) (calls : List ReturnFrame) :
    Steps cfg contract (.running entry frame evm calls)
      (resultTarget next loop calls result) := by
  cases result with
  | ok frame' evm' =>
      exact Steps.single (.atomicOK hcode execution)
  | reverted =>
      exact Steps.single (.atomicRevert hcode execution)
  | returned frame' evm' values =>
      cases atomic <;> cases execution
  | «break» frame' evm' =>
      cases atomic <;> cases execution
  | «continue» frame' evm' =>
      cases atomic <;> cases execution

structure StmtSimulation (cfg : Solm.Config) (frame : Solm.Frame) (evm : EVM.State)
    (stmt : Solm.Stmt) (result : Solm.ExecResult) : Prop where
  run : ∀ (contract : LoweredContract), ContractCompiled contract →
    frame.contract = contract.source → ∀ calls next loop entry,
    CompilesStmt contract.code stmt next loop entry →
    Steps cfg contract (.running entry frame evm calls)
      (resultTarget next loop calls result)

structure BlockSimulation (cfg : Solm.Config) (frame : Solm.Frame) (evm : EVM.State)
    (statements : List Solm.Stmt) (result : Solm.ExecResult) : Prop where
  run : ∀ (contract : LoweredContract), ContractCompiled contract →
    frame.contract = contract.source → ∀ calls next loop entry,
    CompilesBlock contract.code statements next loop entry →
    Steps cfg contract (.running entry frame evm calls)
      (resultTarget next loop calls result)

structure ForSimulation (cfg : Solm.Config) (frame : Solm.Frame) (evm : EVM.State)
    (condition : Solm.Expr) (post body : List Solm.Stmt)
    (result : Solm.ExecResult) : Prop where
  run : ∀ (contract : LoweredContract), ContractCompiled contract →
    frame.contract = contract.source → ∀ calls next outerLoop conditionPC postEntry bodyEntry,
    contract.code.get? conditionPC = some (.branch condition bodyEntry next) →
    CompilesBlock contract.code post conditionPC strictPostTargets postEntry →
    CompilesBlock contract.code body postEntry
      { breakTarget := some next, continueTarget := some postEntry,
        allowReturn := outerLoop.allowReturn } bodyEntry →
    Steps cfg contract (.running conditionPC frame evm calls)
      (resultTarget next outerLoop calls result)

structure FuncSimulation (cfg : Solm.Config) (frame : Solm.Frame) (evm : EVM.State)
    (body : List Solm.Stmt) (result : Solm.ExecResult) : Prop where
  run : ∀ (contract : LoweredContract), ContractCompiled contract →
    frame.contract = contract.source → ∀ calls entry params returnType,
    CompilesCallable contract.code { params, returnType, body } entry →
    Steps cfg contract (.running entry.entry frame evm calls)
      (functionTarget calls result)

theorem atomic_rule_simulation (atomic : AtomicStmt stmt)
    (execution : Solm.ExecStmt cfg frame evm stmt result) :
    StmtSimulation cfg frame evm stmt result ∧
      ResultContract frame.contract result := by
  refine ⟨?_, atomic_preserves_contract atomic execution⟩
  constructor
  intro contract _ _ calls next loop entry compiled
  cases atomic <;> cases compiled <;>
    exact atomic_simulation cfg contract (by assumption) (by constructor) execution calls

macro "solve_atomic_simulation" : tactic =>
  `(tactic|
    first
    | exact atomic_rule_simulation .letDecl
        (.letDecl (by assumption))
    | exact atomic_rule_simulation .letDecl
        (.letDeclRevert (by assumption))
    | exact atomic_rule_simulation .letStorage
        (.letStorage (by assumption))
    | exact atomic_rule_simulation .letStorage
        (.letStorageRevert (by assumption))
    | exact atomic_rule_simulation .letGas (.letGas _)
    | exact atomic_rule_simulation .assign
        (.assign (by assumption) (by assumption))
    | exact atomic_rule_simulation .assign
        (.assignExprRevert (by assumption))
    | exact atomic_rule_simulation .assign
        (.assignStoreRevert (by assumption) (by assumption))
    | exact atomic_rule_simulation .push
        (.pushVal (by assumption) (by assumption))
    | exact atomic_rule_simulation .push
        (.pushValExprRevert (by assumption))
    | exact atomic_rule_simulation .push
        (.pushValStoreRevert (by assumption) (by assumption))
    | exact atomic_rule_simulation .push
        (.pushGrow (by assumption))
    | exact atomic_rule_simulation .push
        (.pushGrowRevert (by assumption))
    | exact atomic_rule_simulation .pop (.pop (by assumption))
    | exact atomic_rule_simulation .pop (.popRevert (by assumption))
    | exact atomic_rule_simulation .delete (.delete (by assumption))
    | exact atomic_rule_simulation .delete (.deleteRevert (by assumption))
    | exact atomic_rule_simulation .require (.requireTrue (by assumption))
    | exact atomic_rule_simulation .require (.requireFalse (by assumption))
    | exact atomic_rule_simulation .require (.requireRevert (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallSuccess (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallFailure (by assumption) (by assumption) (by assumption)
          (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallReturnDecodeRevert (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallReceiverRevert (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallSendRevert (by assumption) (by assumption))
    | exact atomic_rule_simulation .externalCall
        (.externalCallArgsRevert (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .lowLevelCall
        (.lowLevelCallSuccess (by assumption) (by assumption) (by assumption)
          (by assumption))
    | exact atomic_rule_simulation .lowLevelCall
        (.lowLevelCallFailure (by assumption) (by assumption) (by assumption)
          (by assumption))
    | exact atomic_rule_simulation .lowLevelCall
        (.lowLevelCallReceiverRevert (by assumption))
    | exact atomic_rule_simulation .lowLevelCall
        (.lowLevelCallSendRevert (by assumption) (by assumption))
    | exact atomic_rule_simulation .lowLevelCall
        (.lowLevelCallDataRevert (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .delegateCall
        (.delegateCallSuccess (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .delegateCall
        (.delegateCallFailure (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .delegateCall
        (.delegateCallReceiverRevert (by assumption))
    | exact atomic_rule_simulation .delegateCall
        (.delegateCallDataRevert (by assumption) (by assumption))
    | exact atomic_rule_simulation .new
        (.newSuccess (by assumption) (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .new
        (.newRevert (by assumption) (by assumption) (by assumption) (by assumption))
    | exact atomic_rule_simulation .new (.newValueRevert (by assumption))
    | exact atomic_rule_simulation .new
        (.newArgsRevert (by assumption) (by assumption)))

/-- Forward semantics preservation.  The proof is induction on the existing
    mutually inductive big-step derivation; loop iterations and internal calls
    therefore contribute finite lowered paths rather than being collapsed into
    an assumed macro-step. -/
theorem execFuncBody_to_steps (execution : Solm.ExecFuncBody cfg frame evm body result) :
    FuncSimulation cfg frame evm body result := by
  have simulation : FuncSimulation cfg frame evm body result ∧
      ResultContract frame.contract result := by
    apply Solm.ExecFuncBody.rec
      (cfg := cfg)
      (motive_1 := fun frame evm stmt result _ =>
        StmtSimulation cfg frame evm stmt result ∧
          ResultContract frame.contract result)
      (motive_2 := fun frame evm condition post body result _ =>
        ForSimulation cfg frame evm condition post body result ∧
          ResultContract frame.contract result)
      (motive_3 := fun frame evm statements result _ =>
        BlockSimulation cfg frame evm statements result ∧
          ResultContract frame.contract result)
      (motive_4 := fun frame evm body result _ =>
        FuncSimulation cfg frame evm body result ∧
          ResultContract frame.contract result)
      (t := execution)
    case whileFalse =>
      intro solm evm body condition hcondition
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | «while» hcode _ =>
          exact Steps.single (.branchFalse hcode hcondition)
      | atomic hatomic _ => cases hatomic
    case whileCondRevert =>
      intro solm evm body condition hcondition
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | «while» hcode _ =>
          exact Steps.single (.branchRevert hcode hcondition)
      | atomic hatomic _ => cases hatomic
    case whileTrue =>
      intro solm evm body solm' evm' result condition hcondition _ _ blockIH stmtIH
      refine ⟨?_, ResultContract.change blockIH.2 stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «while» hcode hbody =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            ((blockIH.1.run contract hcontract hsource calls _
              { breakTarget := some next, continueTarget := some entry,
                allowReturn := loop.allowReturn } _ hbody).comp
            (stmtIH.1.run contract hcontract (blockIH.2.trans hsource)
              calls next loop entry (.while hcode hbody)))
      | atomic hatomic _ => cases hatomic
    case whileReturn =>
      intro solm evm body solm' evm' values condition hcondition _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «while» hcode hbody =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            (blockIH.1.run contract hcontract hsource calls _
              { breakTarget := some next, continueTarget := some entry,
                allowReturn := loop.allowReturn } _ hbody)
      | atomic hatomic _ => cases hatomic
    case whileRevert =>
      intro solm evm body condition hcondition _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «while» hcode hbody =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            (blockIH.1.run contract hcontract hsource calls _
              { breakTarget := some next, continueTarget := some entry,
                allowReturn := loop.allowReturn } _ hbody)
      | atomic hatomic _ => cases hatomic
    case whileBreak =>
      intro solm evm body solm' evm' condition hcondition _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «while» hcode hbody =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            (blockIH.1.run contract hcontract hsource calls _
              { breakTarget := some next, continueTarget := some entry,
                allowReturn := loop.allowReturn } _ hbody)
      | atomic hatomic _ => cases hatomic
    case whileContinue =>
      intro solm evm body solm' evm' result condition hcondition _ _ blockIH stmtIH
      refine ⟨?_, ResultContract.change blockIH.2 stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «while» hcode hbody =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            ((blockIH.1.run contract hcontract hsource calls _
              { breakTarget := some next, continueTarget := some entry,
                allowReturn := loop.allowReturn } _ hbody).comp
            (stmtIH.1.run contract hcontract (blockIH.2.trans hsource)
              calls next loop entry (.while hcode hbody)))
      | atomic hatomic _ => cases hatomic
    case «for» =>
      intro solm evm init solm1 evm1 condition post body result _ _ initIH forIH
      refine ⟨?_, ResultContract.change initIH.2 forIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «for» hentry hcode hpost hbody hinit =>
          exact (Steps.single (.jump hentry)).comp
            ((initIH.1.run contract hcontract hsource calls _
              { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }
              _ hinit).comp
            (forIH.1.run contract hcontract (initIH.2.trans hsource) calls next loop
              _ _ _ hcode hpost hbody))
      | atomic hatomic _ => cases hatomic
    case forInitReturn =>
      intro solm evm init solm1 evm1 values condition post body _ initIH
      refine ⟨?_, initIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «for» hentry _ _ _ hinit =>
          exact (Steps.single (.jump hentry)).comp
            (initIH.1.run contract hcontract hsource calls _
              { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }
              _ hinit)
      | atomic hatomic _ => cases hatomic
    case forInitRevert =>
      intro solm evm init condition post body _ initIH
      refine ⟨?_, initIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | «for» hentry _ _ _ hinit =>
          exact (Steps.single (.jump hentry)).comp
            (initIH.1.run contract hcontract hsource calls _
              { allowUnboundAbrupt := false, allowReturn := loop.allowReturn }
              _ hinit)
      | atomic hatomic _ => cases hatomic
    case iteCondRevert =>
      intro solm evm thenBody elseBody condition hcondition
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | ite hcode _ _ =>
          exact Steps.single (.branchRevert hcode hcondition)
      | atomic hatomic _ => cases hatomic
    case iteTrue =>
      intro solm evm thenBody result elseBody condition hcondition _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | ite hcode htrue _ =>
          exact (Steps.single (.branchTrue hcode hcondition)).comp
            (blockIH.1.run contract hcontract hsource calls next loop _ htrue)
      | atomic hatomic _ => cases hatomic
    case iteFalse =>
      intro solm evm elseBody result thenBody condition hcondition _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | ite hcode _ hfalse =>
          exact (Steps.single (.branchFalse hcode hcondition)).comp
            (blockIH.1.run contract hcontract hsource calls next loop _ hfalse)
      | atomic hatomic _ => cases hatomic
    case internalCallArgsRevert =>
      intro solm evm args name result hargs
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | internalCall hcode =>
          exact Steps.single (.internalCallArgsRevert hcode hargs)
      | atomic hatomic _ => cases hatomic
    case internalCallReturn =>
      intro solm evm args values name callee locals calleeFrame calleeEvm returnedValues
        result hargs hlookup hbind _ calleeIH
      refine ⟨?_, by simp [ResultContract, Solm.resumeAfterInternalCall]⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | internalCall hcode =>
          have hfound : Solm.lookupCallable? contract.source name = some callee := by
            rw [← hsource]
            exact hlookup
          obtain ⟨calleeEntry, hloweredLookup, hcallee⟩ :=
            hcontract.lookupInternal hfound
          have hloweredBind : Solm.bindParams? calleeEntry.params values = some locals := by
            rw [hcallee.params]
            exact hbind
          exact (Steps.single (.internalCall hcode hargs hloweredLookup hloweredBind)).comp
            (calleeIH.1.run contract hcontract (by simpa using hsource)
              ({ caller := solm, result, returnPC := next } :: calls)
              calleeEntry callee.params callee.returnType hcallee)
      | atomic hatomic _ => cases hatomic
    case internalCallRevert =>
      intro solm evm args values name callee locals result hargs hlookup hbind _ calleeIH
      refine ⟨?_, trivial⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | internalCall hcode =>
          have hfound : Solm.lookupCallable? contract.source name = some callee := by
            rw [← hsource]
            exact hlookup
          obtain ⟨calleeEntry, hloweredLookup, hcallee⟩ :=
            hcontract.lookupInternal hfound
          have hloweredBind : Solm.bindParams? calleeEntry.params values = some locals := by
            rw [hcallee.params]
            exact hbind
          exact (Steps.single (.internalCall hcode hargs hloweredLookup hloweredBind)).comp
            (calleeIH.1.run contract hcontract (by simpa using hsource)
              ({ caller := solm, result, returnPC := next } :: calls)
              calleeEntry callee.params callee.returnType hcallee)
      | atomic hatomic _ => cases hatomic
    case checkedCallReturnDecodeRevert =>
      intro solm evm receiver target eth sendValue args values name evm' output perm
        result onSuccess errorResult onFailure hreceiver heth hargs hcall hdecode
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | checkedCall hcode _ _ =>
          exact Steps.single (.checkedCallDecodeRevert hcode hreceiver heth hargs hcall hdecode)
      | atomic hatomic _ => cases hatomic
    case checkedCallReceiverRevert =>
      intro solm evm receiver name eth args result onSuccess errorResult onFailure perm hreceiver
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | checkedCall hcode _ _ =>
          exact Steps.single (.checkedCallReceiverRevert hcode hreceiver)
      | atomic hatomic _ => cases hatomic
    case checkedCallSendRevert =>
      intro solm evm receiver target eth name args result onSuccess errorResult onFailure perm
        hreceiver heth
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | checkedCall hcode _ _ =>
          exact Steps.single (.checkedCallValueRevert hcode hreceiver heth)
      | atomic hatomic _ => cases hatomic
    case checkedCallArgsRevert =>
      intro solm evm receiver target eth sendValue args name result onSuccess errorResult
        onFailure perm hreceiver heth hargs
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | checkedCall hcode _ _ =>
          exact Steps.single (.checkedCallArgsRevert hcode hreceiver heth hargs)
      | atomic hatomic _ => cases hatomic
    case checkedCallSuccess =>
      intro solm evm receiver target eth sendValue args values name evm' output perm returns
        returnResult onSuccess result errorResult onFailure hreceiver heth hargs hcall hdecode _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | checkedCall hcode hsuccess _ =>
          exact (Steps.single (.checkedCallSuccess hcode hreceiver heth hargs hcall hdecode)).comp
            (blockIH.1.run contract hcontract (by simpa using hsource)
              calls next loop _ hsuccess)
      | atomic hatomic _ => cases hatomic
    case checkedCallFail =>
      intro solm evm receiver target eth sendValue args values name evm' output perm
        errorResult onFailure result returnResult onSuccess hreceiver heth hargs hcall _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | checkedCall hcode _ hfailure =>
          exact (Steps.single (.checkedCallFailure hcode hreceiver heth hargs hcall)).comp
            (blockIH.1.run contract hcontract (by simpa using hsource)
              calls next loop _ hfailure)
      | atomic hatomic _ => cases hatomic
    case «return» =>
      intro solm evm expressions values heval
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | «return» hallowed hcode =>
          simpa [resultTarget, hallowed] using
            Steps.single (.returnOK hcode heval)
      | returnFault hstrict hcode =>
          simpa [resultTarget, hstrict] using
            Steps.single (.blockedReturnOK hcode heval)
      | atomic hatomic _ => cases hatomic
    case returnRevert =>
      intro solm evm expressions heval
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | «return» _ hcode =>
          exact Steps.single (.returnRevert hcode heval)
      | returnFault hstrict hcode =>
          exact Steps.single (.blockedReturnRevert hcode heval)
      | atomic hatomic _ => cases hatomic
    case «break» =>
      intro solm evm
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | breakJump htarget hcode =>
          simp [resultTarget, abruptTarget, htarget]
          exact Steps.single (.jump hcode)
      | breakFallthrough htarget hallowed hcode =>
          simp [resultTarget, abruptTarget, htarget, hallowed]
          exact Steps.single (.fallthrough hcode)
      | breakFault htarget hstrict hcode =>
          simp [resultTarget, abruptTarget, htarget, hstrict]
          exact Steps.single (.explicitFault hcode)
      | atomic hatomic _ => cases hatomic
    case «continue» =>
      intro solm evm
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled with
      | continueJump htarget hcode =>
          simp [resultTarget, abruptTarget, htarget]
          exact Steps.single (.jump hcode)
      | continueFallthrough htarget hallowed hcode =>
          simp [resultTarget, abruptTarget, htarget, hallowed]
          exact Steps.single (.fallthrough hcode)
      | continueFault htarget hstrict hcode =>
          simp [resultTarget, abruptTarget, htarget, hstrict]
          exact Steps.single (.explicitFault hcode)
      | atomic hatomic _ => cases hatomic
    case falseDone =>
      intro solm evm post body condition hcondition
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop conditionPC postEntry bodyEntry hcode _ _
      exact Steps.single (.branchFalse hcode hcondition)
    case condRevert =>
      intro solm evm post body condition hcondition
      refine ⟨?_, trivial⟩
      constructor
      intro contract _ _ calls next loop conditionPC postEntry bodyEntry hcode _ _
      exact Steps.single (.branchRevert hcode hcondition)
    case bodyReturn =>
      intro solm evm body solm' evm' values post condition hcondition _ bodyIH
      refine ⟨?_, bodyIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        (bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody)
    case bodyRevert =>
      intro solm evm body post condition hcondition _ bodyIH
      refine ⟨?_, bodyIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        (bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody)
    case bodyBreak =>
      intro solm evm body solm' evm' post condition hcondition _ bodyIH
      refine ⟨?_, bodyIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        (bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody)
    case iterate =>
      intro solm evm body solm1 evm1 post solm2 evm2 result condition hcondition
        _ _ _ bodyIH postIH loopIH
      refine ⟨?_, ResultContract.change bodyIH.2
        (ResultContract.change postIH.2 loopIH.2)⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        ((bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody).comp
        ((postIH.1.run contract hcontract (bodyIH.2.trans hsource) calls
          conditionPC strictPostTargets postEntry hpost).comp
        (loopIH.1.run contract hcontract (postIH.2.trans (bodyIH.2.trans hsource))
          calls next loop conditionPC postEntry bodyEntry hcode hpost hbody)))
    case iteratePostRevert =>
      intro solm evm body solm1 evm1 post condition hcondition _ _ bodyIH postIH
      refine ⟨?_, ResultContract.change bodyIH.2 postIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        ((bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody).comp
        (postIH.1.run contract hcontract (bodyIH.2.trans hsource) calls
          conditionPC strictPostTargets postEntry hpost))
    case continueIter =>
      intro solm evm body solm1 evm1 post solm2 evm2 result condition hcondition
        _ _ _ bodyIH postIH loopIH
      refine ⟨?_, ResultContract.change bodyIH.2
        (ResultContract.change postIH.2 loopIH.2)⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        ((bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody).comp
        ((postIH.1.run contract hcontract (bodyIH.2.trans hsource) calls
          conditionPC strictPostTargets postEntry hpost).comp
        (loopIH.1.run contract hcontract (postIH.2.trans (bodyIH.2.trans hsource))
          calls next loop conditionPC postEntry bodyEntry hcode hpost hbody)))
    case continuePostRevert =>
      intro solm evm body solm1 evm1 post condition hcondition _ _ bodyIH postIH
      refine ⟨?_, ResultContract.change bodyIH.2 postIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop conditionPC postEntry bodyEntry
        hcode hpost hbody
      exact (Steps.single (.branchTrue hcode hcondition)).comp
        ((bodyIH.1.run contract hcontract hsource calls postEntry
          { breakTarget := some next, continueTarget := some postEntry,
            allowReturn := loop.allowReturn } bodyEntry hbody).comp
        (postIH.1.run contract hcontract (bodyIH.2.trans hsource) calls
          conditionPC strictPostTargets postEntry hpost))
    case nil =>
      intro solm evm
      refine ⟨?_, by simp [ResultContract]⟩
      constructor
      intro contract _ _ calls next loop entry compiled
      cases compiled
      exact Relation.ReflTransGen.refl
    case consNormal =>
      intro solm evm stmt solm' evm' statements result _ _ stmtIH blockIH
      refine ⟨?_, ResultContract.change stmtIH.2 blockIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | cons hrest hstmt =>
          exact (stmtIH.1.run contract hcontract hsource calls _ loop _ hstmt).comp
            (blockIH.1.run contract hcontract (stmtIH.2.trans hsource)
              calls next loop _ hrest)
    case consReturn =>
      intro solm evm stmt solm' evm' values statements _ stmtIH
      refine ⟨?_, stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | @cons _ _ _ restEntry _ _ _ hstmt =>
          exact stmtIH.1.run contract hcontract hsource calls restEntry loop _ hstmt
    case consRevert =>
      intro solm evm stmt statements _ stmtIH
      refine ⟨?_, stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | @cons _ _ _ restEntry _ _ _ hstmt =>
          exact stmtIH.1.run contract hcontract hsource calls restEntry loop _ hstmt
    case consBreak =>
      intro solm evm stmt solm' evm' statements _ stmtIH
      refine ⟨?_, stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | @cons _ _ _ restEntry _ _ _ hstmt =>
          exact stmtIH.1.run contract hcontract hsource calls restEntry loop _ hstmt
    case consContinue =>
      intro solm evm stmt solm' evm' statements _ stmtIH
      refine ⟨?_, stmtIH.2⟩
      constructor
      intro contract hcontract hsource calls next loop entry compiled
      cases compiled with
      | @cons _ _ _ restEntry _ _ _ hstmt =>
          exact stmtIH.1.run contract hcontract hsource calls restEntry loop _ hstmt
    case execBlockOK =>
      intro solm evm body solm' evm' _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls entry params returnType compiled
      obtain ⟨done, hdone, hbody⟩ := compiled.body
      exact (blockIH.1.run contract hcontract hsource calls done {} entry.entry hbody).comp
        (Steps.single (.fallthrough hdone))
    case execBlockRet =>
      intro solm evm body solm' evm' values _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls entry params returnType compiled
      obtain ⟨done, _, hbody⟩ := compiled.body
      exact blockIH.1.run contract hcontract hsource calls done {} entry.entry hbody
    case execBlockRevert =>
      intro solm evm body _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls entry params returnType compiled
      obtain ⟨done, _, hbody⟩ := compiled.body
      exact blockIH.1.run contract hcontract hsource calls done {} entry.entry hbody
    case execBlockBreak =>
      intro solm evm body solm' evm' _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls entry params returnType compiled
      obtain ⟨done, _, hbody⟩ := compiled.body
      simpa [resultTarget, functionTarget, abruptTarget] using
        blockIH.1.run contract hcontract hsource calls done {} entry.entry hbody
    case execBlockContinue =>
      intro solm evm body solm' evm' _ blockIH
      refine ⟨?_, blockIH.2⟩
      constructor
      intro contract hcontract hsource calls entry params returnType compiled
      obtain ⟨done, _, hbody⟩ := compiled.body
      simpa [resultTarget, functionTarget, abruptTarget] using
        blockIH.1.run contract hcontract hsource calls done {} entry.entry hbody
    all_goals
      intros
      try solve_atomic_simulation
  exact simulation.1

theorem execFuncBody_target_result
    (execution : Solm.ExecFuncBody cfg frame evm body result) :
    (functionTarget [] result).execResult? = some result := by
  cases execution <;> rfl

/-- Contract-level semantics preservation for every certified callable entry
    emitted by `lowerContract`. -/
theorem lowerContract_callable_preservation
    (source : Solm.ContractDecl) (decl : Solm.CallableDecl)
    (entry : CallableEntry) (locals : Solm.Store) (evm : EVM.State)
    (compiledEntry : CompilesCallable (lowerContract source).code decl entry)
    (execution : Solm.ExecFuncBody cfg
      { contract := source, locals } evm decl.body result) :
    Steps cfg (lowerContract source)
      ((lowerContract source).initialState entry evm locals)
      (functionTarget [] result) :=
  (execFuncBody_to_steps execution).run (lowerContract source)
    (lowerContract_compiled source) rfl [] entry decl.params decl.returnType compiledEntry

/-- Observable form of preservation: the lowered machine reaches a final
    state whose decoded `ExecResult` is exactly the source big-step result. -/
theorem lowerContract_callable_result_preservation
    (source : Solm.ContractDecl) (decl : Solm.CallableDecl)
    (entry : CallableEntry) (locals : Solm.Store) (evm : EVM.State)
    (compiledEntry : CompilesCallable (lowerContract source).code decl entry)
    (execution : Solm.ExecFuncBody cfg
      { contract := source, locals } evm decl.body result) :
    ∃ final,
      Steps cfg (lowerContract source)
        ((lowerContract source).initialState entry evm locals) final ∧
      final.execResult? = some result := by
  exact ⟨functionTarget [] result,
    lowerContract_callable_preservation source decl entry locals evm compiledEntry execution,
    execFuncBody_target_result execution⟩

theorem lowerContract_constructor_preservation
    (source : Solm.ContractDecl) (locals : Solm.Store) (evm : EVM.State)
    (execution : Solm.ExecFuncBody cfg
      { contract := source, locals } evm source.ctor.body result) :
    ∃ final,
      Steps cfg (lowerContract source)
        ((lowerContract source).initialState
          (lowerContract source).constructorEntry evm locals) final ∧
      final.execResult? = some result := by
  apply lowerContract_callable_result_preservation source
    { params := source.ctor.params, body := source.ctor.body }
  · exact (lowerContract_compiled source).constructor
  · exact execution

/-- Named functions receive matching lowered entries and preserve every
    big-step execution from the same initial locals and EVM state. -/
theorem lowerContract_function_preservation
    (source : Solm.ContractDecl)
    (found : Solm.lookupFunction? source.functions name = some decl) :
    ∃ entry,
      lookupEntry? (lowerContract source).functionEntries name = some entry ∧
      CompilesCallable (lowerContract source).code decl entry ∧
      ∀ (locals : Solm.Store) (evm : EVM.State) (result : Solm.ExecResult),
        Solm.ExecFuncBody cfg { contract := source, locals } evm decl.body result →
        ∃ final,
          Steps cfg (lowerContract source)
            ((lowerContract source).initialState entry evm locals) final ∧
          final.execResult? = some result := by
  obtain ⟨entry, hlookup, hcompiled⟩ :=
    (lowerContract_compiled source).functions.lookup found
  exact ⟨entry, hlookup, hcompiled, fun locals evm result execution =>
    lowerContract_callable_result_preservation source decl entry locals evm
      hcompiled execution⟩


end Solm.SmallStep
