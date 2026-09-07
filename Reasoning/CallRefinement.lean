import Reasoning.Refinement
import Reasoning.ExternalCall

/-!
# Paired call progression

The raw call boundaries choose the EVM gas and substate witnesses internally and handle
depth and balance failures. They return the actual post-call cursor and source state,
related up to account-map equivalence. Statement rules use `BlockProgress` to connect
the compiler's status/ABI-decoder tail to the Solm call result.

The rules cover typed, low-level, checked, and delegate calls, including STATICCALL
permission variants, plus internal calls through a body-refinement summary.
`PairedCall` packages the concrete RD/source witnesses shared by CALL, STATICCALL and
DELEGATECALL. Obtain it with `callPaired`, `staticCallPaired`, `rawCallPaired`,
`rawStaticCallPaired`, or `delegateCallPaired`, then apply the appropriate statement rule.
`BlockProgress` rules consume concrete boundary evidence. Their `BlockRefinesFrom`
counterparts derive the boundary from incoming RD and the starting relation, and
use local refinements for the successful continuation or selected handler.
Ordinary CALL requires a writable execution context and supports arbitrary value.
Creation is outside this module's scope.
-/

namespace Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

/-- The source state agrees with the world and environment carried by an RD cursor.
Gas, machine state, and substate are deliberately not equated. -/
structure CallStateRel (s0 : State) (ee : ExecutionEnv)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (evm : State) : Prop where
  env : evm.executionEnv = ee
  readOnly : RDWorld s0 evm
  created : evm.createdAccounts = world.1
  accounts : accountMapEquiv world.2 evm.accountMap

/-- Initial world agreement for a pair of transaction states. -/
theorem CallStateRel.initState {cA gh bl σ_evm σ_solm σ₀ g A I}
    (haccounts : accountMapEquiv σ_evm σ_solm) :
    CallStateRel (initState cA gh bl σ_evm σ₀ g A I) I (cA, σ_evm)
      (initState cA gh bl σ_solm σ₀ g A I) :=
  ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl, haccounts⟩

/-- Matching storage writes preserve call-state agreement, including the read-only
world used by subsequent calls. Account maps need only be equivalent. -/
theorem CallStateRel.storageStore {s0 ee world evm}
    (h : CallStateRel s0 ee world evm) (owner : AccountAddress) (slot value : UInt256) :
    CallStateRel s0 ee (world.1, sstoreAccountMap owner world.2 slot value)
      (Solm.EVM.storageStore evm owner slot value) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [storageStore_executionEnv]; exact h.env
  · unfold Solm.EVM.storageStore State.lookupAccount
    cases evm.accountMap.find? owner <;> simpa [Option.option, State.setAccount, RDWorld] using h.readOnly
  · rw [storageStore_createdAccounts]; exact h.created
  · rw [storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap owner slot value h.accounts

/-- The common case writes storage owned by the current execution environment. -/
theorem CallStateRel.storageStore_codeOwner {s0 ee world evm}
    (h : CallStateRel s0 ee world evm) (slot value : UInt256) :
    CallStateRel s0 ee (world.1, sstoreAccountMap ee.codeOwner world.2 slot value)
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value) := by
  rw [h.env]
  exact h.storageStore ee.codeOwner slot value

/-- The concrete CALL successor, including output-memory copying and memory expansion. -/
def callCursor (pc : UInt256) (rest : List UInt256) (mem : ByteArray) (aw : UInt256)
    (inOffset inSize outOffset outSize : UInt256) (z : Bool) (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor where
  pc := pc + ⟨1⟩
  stack := (if z then ⟨1⟩ else ⟨0⟩) :: rest
  mem := out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat
  aw := UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
    outOffset.toNat outSize.toNat)
  rdata := out
  world := world

private theorem callExact {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : ℕ} {gasArg target valueWord inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {value : ℤ}
    (h : RD code ee g s0 pc
      (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (evm.createdAccounts, evm.accountMap) k C)
    (hEnv : evm.executionEnv = ee) (hWorld : RDWorld s0 evm)
    (hword : valueWord = EVM.wordOfInt value)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : ee.perm = true)
    (hov : rest.length + 1 ≤ 1024) :
    ∃ cA' σ' z out A' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize z out (cA', σ')
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
      callViaEVM evm (AccountAddress.ofUInt256 target) value
        (mem.readWithPadding inOffset.toNat inSize.toNat)
        (z, { evm with createdAccounts := cA', accountMap := σ', substate := A' }, out) ∧
      out.size < UInt256.size := by
  by_cases hd : ee.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.callValueDepthLimit hperm hdec hd hov
    refine ⟨_, _, false, ByteArray.empty,
      (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      k', C', rd, ?_, by decide⟩
    apply callViaEVM.callNotMade rfl rfl
    rintro ⟨_, hne⟩
    exact hne (hEnv ▸ hd)
  have hlt : ee.depth.val < 1024 := by
    have := ee.depth.isLt
    have hne : ee.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
    omega
  by_cases hb : valueWord ≤ (evm.accountMap.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance))
  · obtain ⟨cA', σ', z, out, A_in, callGas, k', C', ⟨g', A', hTheta⟩, rd, hsize⟩ :=
      h.callValueMade hdec hperm hb hlt hov
    refine ⟨cA', σ', z, out, A', k', C', rd, ?_, hsize⟩
    refine callViaEVM.callMade (g' := g') hword ⟨callGas, A_in, ?_⟩ rfl ?_ ?_
    · obtain ⟨hOriginal, hGenesis, hBlocks⟩ := hWorld
      rw [accountAddress_roundtrip] at hTheta
      simpa only [hEnv, hOriginal, hGenesis, hBlocks, hperm] using hTheta
    · simpa only [hEnv] using hb
    · simpa only [hEnv] using hd
  · obtain ⟨k', C', rd⟩ := h.callValueInsufficientBalance hperm hdec hb hlt hov
    refine ⟨_, _, false, ByteArray.empty,
      (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      k', C', rd, ?_, by decide⟩
    apply callViaEVM.callNotMade rfl rfl
    rintro ⟨hbal, _⟩
    apply hb
    simpa only [hword, hEnv] using hbal

/-- Synchronize a typed call attempt with one EVM CALL. Depth/balance checks and gas
witnesses are internal. The output exposes the source state, EVM cursor and RD counters,
the shared flag/bytes, and the relation needed to synchronize a later call.

The cursor is immediately after CALL; the caller's status check and return decoder have
not yet run. Those bytecode steps belong to the statement rule's continuation. -/
theorem callPaired {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {cfg : Config} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target valueWord inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {value : ℤ} {tgt : EVM.Address} {name : Ident} {args : List Value}
    (h : RD code ee g s0 pc
      (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (hword : valueWord = EVM.wordOfInt value)
    (htarget : tgt = AccountAddress.ofUInt256 target)
    (hencode : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hdec : decode code pc = some (.CALL, .none)) (hperm : ee.perm = true)
    (hov : rest.length + 1 ≤ 1024) :
    ∃ z out evm' world' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize z out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
      typedCallViaEVM cfg evm tgt name value args (z, evm', out) ∧
      CallStateRel s0 ee world' evm' ∧ out.size < UInt256.size := by
  let shadow := { evm with createdAccounts := cA, accountMap := σ }
  obtain ⟨cA', σ', z, out, A', k', C', rd, hraw, hsize⟩ :=
    callExact (evm := shadow) h hState.env hState.readOnly hword hdec hperm hov
  have htyped : typedCallViaEVM cfg shadow tgt name value args
      (z, { shadow with createdAccounts := cA', accountMap := σ', substate := A' }, out) := by
    exact ⟨_, hencode, htarget ▸ hraw⟩
  obtain ⟨σS', AS', hcall, hAccounts⟩ := typedCallViaEVM_accountMapEquiv
    (evm_solm := evm) htyped hState.accounts rfl hState.created rfl rfl rfl rfl
  refine ⟨z, out, _, (cA', σ'), k', C', rd, hcall, ?_, hsize⟩
  exact ⟨hState.env, hState.readOnly, rfl, hAccounts⟩

/-- The typed source result determined by the shared raw flag/bytes. This does not
assert that the bytecode has already executed its status check or ABI decoder. -/
def externalCallResult (cfg : Config) (frame : Frame) (evm' : State)
    (name retVar : Ident) (z : Bool) (out : ByteArray) : ExecResult :=
  if z then
    match cfg.externalABI.decode? name out with
    | some values => .ok { frame with locals := frame.locals.insert retVar (collapseReturns values) } evm'
    | none => .reverted
  else .reverted

/-- Paired progression for a typed external call at the head of a source block.

`hsuccess` receives the post-CALL RD with raw flag `true`, the source post-call state,
and their relation. It handles the bytecode status/decoder tail: successful decoding
requires `BlockProgress` for the remaining statements with the return variable bound;
failed decoding requires `RDrev` and skips those statements.

`hfailure` is entirely EVM-side: from the post-CALL RD with flag `false`, prove `RDrev`.
It needs no source state, typed-call fact, or return-data bound. The separate `hRevert`
hypothesis says that `Q` accepts matching reverts. Gas witnesses and depth/balance checks
stay internal to `callPaired`.

For use inside a `StmtsRefine` proof, introduce its related starting pair and apply this
rule directly. Setting `stmts := []` gives the singleton-call case. -/
theorem BlockProgress.externalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {cfg : Config} {frame : Frame} {pc : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset inSize outOffset outSize : UInt256} {rest : List UInt256}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar : Ident} {value : ℤ} {stmts : List Stmt} {Q : ExitRel}
    (h : RD code ee g s0 pc
      (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : evalExprs? cfg frame evm args = .ok argVals)
    (hword : valueWord = EVM.wordOfInt value)
    (htarget : EVM.address tgt = AccountAddress.ofUInt256 target)
    (hencode : cfg.externalABI.encode? name argVals =
      some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hdec : decode code pc = some (.CALL, .none)) (hperm : ee.perm = true)
    (hov : rest.length + 1 ≤ 1024)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize true out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockProgress code ee g s0 cfg
          { frame with locals := frame.locals.insert retVar (collapseReturns values) } evm' stmts Q
      | none => RDrev code g s0)
    (hfailure : ∀ out world' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize false out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      RDrev code g s0) :
    BlockProgress code ee g s0 cfg frame evm
      (.externalCall receiver name eth args retVar :: stmts) Q := by
  obtain ⟨z, out, evm', world', k', C', rd, hcall, hState', hsize⟩ :=
    callPaired h hState hword htarget hencode hdec hperm hov
  have abort (hrev : RDrev code g s0)
      (hstmt : ExecStmt cfg frame evm (.externalCall receiver name eth args retVar) .reverted) :
      BlockProgress code ee g s0 cfg frame evm
        (.externalCall receiver name eth args retVar :: stmts) Q := by
    exact ⟨.reverted, .reverted, ExecBlock.consRevert hstmt, hrev, hRevert⟩
  cases z with
  | false =>
      exact abort (hfailure out world' k' C' rd)
        (ExecStmt.externalCallFailure hreceiver heth hargs hcall)
  | true =>
      have hnext := hsuccess out evm' world' k' C' rd hcall hState' hsize
      cases hdecode : cfg.externalABI.decode? name out with
      | none =>
          exact abort (by simpa only [hdecode] using hnext)
            (ExecStmt.externalCallReturnDecodeRevert hreceiver heth hargs hcall hdecode)
      | some values =>
          exact BlockProgress.cons (ExecStmt.externalCallSuccess hreceiver heth hargs hcall hdecode)
            (by simpa only [hdecode] using hnext)

abbrev CallWorld := Batteries.RBSet AccountAddress compare × AccountMap

/-- Concrete call boundary evidence. The relation closes over the source input state;
`after` exposes the exact EVM cursor for each shared flag, output and world. -/
def PairedCall (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (call : (Bool × State × ByteArray) → Prop)
    (after : Bool → ByteArray → CallWorld → Cursor) : Prop :=
  ∃ z out evm' world' k' C',
    let cur := after z out world'
    RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
    call (z, evm', out) ∧ CallStateRel s0 ee world' evm' ∧ out.size < UInt256.size

private theorem staticCallExact {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256}
    (h : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (evm.createdAccounts, evm.accountMap) k C)
    (hEnv : evm.executionEnv = ee) (hWorld : RDWorld s0 evm)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hov : rest.length + 1 ≤ 1024) :
    ∃ cA' σ' z out A' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize z out (cA', σ')
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
      callViaEVM evm (AccountAddress.ofUInt256 target) 0
        (mem.readWithPadding inOffset.toNat inSize.toNat)
        (z, { evm with createdAccounts := cA', accountMap := σ', substate := A' }, out) false ∧
      out.size < UInt256.size := by
  by_cases hd : ee.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.solcStaticcallDepthLimit hdec hd hov
    refine ⟨_, _, false, ByteArray.empty,
      (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      k', C', rd, ?_, by decide⟩
    apply callViaEVM.callNotMade rfl rfl
    rintro ⟨_, hne⟩
    exact hne (hEnv ▸ hd)
  have hlt : ee.depth.val < 1024 := by
    have := ee.depth.isLt
    have hne : ee.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
    omega
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', ⟨g', A', hTheta⟩, rd, hsize⟩ :=
    h.solcStaticcall hdec hlt hov
  refine ⟨cA', σ', z, out, A', k', C', rd, ?_, hsize⟩
  refine callViaEVM.callMade (g' := g') wordOfInt_zero.symm ⟨callGas, A_in, ?_⟩ rfl
    (Fin.zero_le _) ?_
  · obtain ⟨hOriginal, hGenesis, hBlocks⟩ := hWorld
    rw [accountAddress_roundtrip] at hTheta
    simpa only [hEnv, hOriginal, hGenesis, hBlocks] using hTheta
  · simpa only [hEnv] using hd

private theorem delegateCallExact {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256}
    (h : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (evm.createdAccounts, evm.accountMap) k C)
    (hEnv : evm.executionEnv = ee) (hWorld : RDWorld s0 evm)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hov : rest.length + 1 ≤ 1024) :
    ∃ cA' σ' z out A' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize z out (cA', σ')
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
      delegateCallViaEVM evm (AccountAddress.ofUInt256 target)
        (mem.readWithPadding inOffset.toNat inSize.toNat)
        (z, { evm with createdAccounts := cA', accountMap := σ', substate := A' }, out) ∧
      out.size < UInt256.size := by
  by_cases hd : ee.depth = 1024
  · obtain ⟨k', C', rd⟩ := h.delegatecallDepthLimit hdec hd hov
    refine ⟨_, _, false, ByteArray.empty,
      (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      k', C', rd, ?_, by decide⟩
    apply delegateCallViaEVM.callNotMade rfl rfl
    exact hEnv ▸ hd
  have hlt : ee.depth.val < 1024 := by
    have := ee.depth.isLt
    have hne : ee.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
    omega
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', ⟨g', A', hTheta⟩, rd, hsize⟩ :=
    h.delegatecall hdec hlt hov
  refine ⟨cA', σ', z, out, A', k', C', rd, ?_, hsize⟩
  refine delegateCallViaEVM.callMade (g' := g') ⟨callGas, A_in, ?_⟩ rfl ?_
  · obtain ⟨hOriginal, hGenesis, hBlocks⟩ := hWorld
    simpa only [hEnv, hOriginal, hGenesis, hBlocks] using hTheta
  · simpa only [hEnv] using hd

/-- Pair a zero-value STATICCALL with the typed source call in read-only mode. -/
theorem staticCallPaired {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {cfg : Config} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {tgt : EVM.Address} {name : Ident} {args : List Value}
    (h : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (htarget : tgt = AccountAddress.ofUInt256 target)
    (hencode : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hov : rest.length + 1 ≤ 1024) :
    ∃ z out evm' world' k' C',
      let cur := callCursor pc rest mem aw inOffset inSize outOffset outSize z out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' ∧
      typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) false ∧
      CallStateRel s0 ee world' evm' ∧ out.size < UInt256.size := by
  let shadow := { evm with createdAccounts := cA, accountMap := σ }
  obtain ⟨cA', σ', z, out, A', k', C', rd, hraw, hsize⟩ :=
    staticCallExact (evm := shadow) h hState.env hState.readOnly hdec hov
  have htyped : typedCallViaEVM cfg shadow tgt name 0 args
      (z, { shadow with createdAccounts := cA', accountMap := σ', substate := A' }, out) false := by
    exact ⟨_, hencode, htarget ▸ hraw⟩
  obtain ⟨σS', AS', hcall, hAccounts⟩ := typedCallViaEVM_accountMapEquiv
    (evm_solm := evm) htyped hState.accounts rfl hState.created rfl rfl rfl rfl
  refine ⟨z, out, _, (cA', σ'), k', C', rd, hcall, ?_, hsize⟩
  exact ⟨hState.env, hState.readOnly, rfl, hAccounts⟩

/-- Pair DELEGATECALL with the native Solm relation, including depth-limit failure.
No assumption about the target's code, inherited value, or permission is needed. -/
theorem delegateCallPaired {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {tgt : EVM.Address} {calldata : ByteArray}
    (h : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (htarget : tgt = AccountAddress.ofUInt256 target)
    (hdata : calldata = mem.readWithPadding inOffset.toNat inSize.toNat)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hov : rest.length + 1 ≤ 1024) :
    PairedCall code ee g s0 (delegateCallViaEVM evm tgt calldata)
      (callCursor pc rest mem aw inOffset inSize outOffset outSize) := by
  let shadow := { evm with createdAccounts := cA, accountMap := σ }
  obtain ⟨cA', σ', z, out, A', k', C', rd, hraw, hsize⟩ :=
    delegateCallExact (evm := shadow) h hState.env hState.readOnly hdec hov
  rw [← htarget, ← hdata] at hraw
  obtain ⟨σS, AS, hcall, hAccounts⟩ := delegateCallViaEVM_accountMapEquiv
    (evm_solm := evm) hraw hState.accounts rfl hState.created rfl rfl rfl
  exact ⟨z, out, _, (cA', σ'), k', C', rd, hcall,
    ⟨hState.env, hState.readOnly, rfl, hAccounts⟩, hsize⟩

/-- Pair a raw CALL with verbatim calldata. -/
theorem rawCallPaired {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target valueWord inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {value : ℤ} {tgt : EVM.Address} {calldata : ByteArray}
    (h : RD code ee g s0 pc
      (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (hword : valueWord = EVM.wordOfInt value)
    (htarget : tgt = AccountAddress.ofUInt256 target)
    (hdata : calldata = mem.readWithPadding inOffset.toNat inSize.toNat)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : ee.perm = true)
    (hov : rest.length + 1 ≤ 1024) :
    PairedCall code ee g s0 (callViaEVM evm tgt value calldata)
      (callCursor pc rest mem aw inOffset inSize outOffset outSize) := by
  let cfg := rawCallTransportConfig { layout := fun _ _ => none } calldata
  obtain ⟨z, out, evm', world', k', C', rd, ⟨bytes, henc, hraw⟩, hr, hsize⟩ :=
    callPaired (cfg := cfg) (name := "") (args := []) h hState hword htarget
      (congrArg some hdata) hdec hperm hov
  have heq : calldata = bytes := Option.some.inj henc
  exact ⟨z, out, evm', world', k', C', rd, heq ▸ hraw, hr, hsize⟩

/-- Pair a raw STATICCALL with verbatim calldata and zero value. -/
theorem rawStaticCallPaired {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {rest : List UInt256} {tgt : EVM.Address} {calldata : ByteArray}
    (h : RD code ee g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: rest)
      mem aw rdata (cA, σ) k C)
    (hState : CallStateRel s0 ee (cA, σ) evm)
    (htarget : tgt = AccountAddress.ofUInt256 target)
    (hdata : calldata = mem.readWithPadding inOffset.toNat inSize.toNat)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hov : rest.length + 1 ≤ 1024) :
    PairedCall code ee g s0 (fun result => callViaEVM evm tgt 0 calldata result false)
      (callCursor pc rest mem aw inOffset inSize outOffset outSize) := by
  let cfg := rawCallTransportConfig { layout := fun _ _ => none } calldata
  obtain ⟨z, out, evm', world', k', C', rd, ⟨bytes, henc, hraw⟩, hr, hsize⟩ :=
    staticCallPaired (cfg := cfg) (name := "") (args := []) h hState htarget
      (congrArg some hdata) hdec hov
  have heq : calldata = bytes := Option.some.inj henc
  exact ⟨z, out, evm', world', k', C', rd, heq ▸ hraw, hr, hsize⟩

/-- Typed call elimination shared by CALL and STATICCALL. Supply the concrete boundary
from `callPaired` or `staticCallPaired`. Raw failure needs only the EVM revert continuation. -/
theorem BlockProgress.externalCallOfPaired {code ee g s0 evm cfg frame}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar : Ident} {value : ℤ} {stmts : List Stmt} {Q : ExitRel} {perm : Bool}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair : PairedCall code ee g s0
      (fun result => typedCallViaEVM cfg evm (EVM.address tgt) name value argVals result perm) after)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : evalExprs? cfg frame evm args = .ok argVals)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := after true out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) perm →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockProgress code ee g s0 cfg
          { frame with locals := frame.locals.insert retVar (collapseReturns values) } evm' stmts Q
      | none => RDrev code g s0)
    (hfailure : ∀ out world' k' C',
      let cur := after false out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      RDrev code g s0) :
    BlockProgress code ee g s0 cfg frame evm
      (.externalCall receiver name eth args retVar perm :: stmts) Q := by
  obtain ⟨z, out, evm', world', k', C', rd, hcall, hState', hsize⟩ := hpair
  have abort (hrev : RDrev code g s0)
      (hstmt : ExecStmt cfg frame evm (.externalCall receiver name eth args retVar perm) .reverted) :
      BlockProgress code ee g s0 cfg frame evm
        (.externalCall receiver name eth args retVar perm :: stmts) Q := by
    exact ⟨.reverted, .reverted, ExecBlock.consRevert hstmt, hrev, hRevert⟩
  cases z with
  | false =>
      exact abort (hfailure out world' k' C' rd)
        (ExecStmt.externalCallFailure hreceiver heth hargs hcall)
  | true =>
      have hnext := hsuccess out evm' world' k' C' rd hcall hState' hsize
      cases hdecode : cfg.externalABI.decode? name out with
      | none =>
          exact abort (by simpa only [hdecode] using hnext)
            (ExecStmt.externalCallReturnDecodeRevert hreceiver heth hargs hcall hdecode)
      | some values =>
          exact BlockProgress.cons (ExecStmt.externalCallSuccess hreceiver heth hargs hcall hdecode)
            (by simpa only [hdecode] using hnext)


/-- Low-level CALL/STATICCALL binds both raw results and continues even when `z = false`.
Use `rawCallPaired` or `rawStaticCallPaired` for the boundary premise. -/
theorem BlockProgress.lowLevelCall {code ee g s0 evm cfg frame}
    {receiver eth cdata : Expr} {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {okVar dataVar : Ident} {stmts : List Stmt} {Q : ExitRel} {perm : Bool}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair : PairedCall code ee g s0
      (fun result => callViaEVM evm (EVM.address tgt) value calldata result perm) after)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : evalExpr? cfg frame evm eth = .ok (.int value))
    (hdata : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hcontinue : ∀ z out evm' world' k' C',
      let cur := after z out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      callViaEVM evm (EVM.address tgt) value calldata (z, evm', out) perm →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      BlockProgress code ee g s0 cfg
        { frame with locals := (frame.locals.insert okVar (.bool z)).insert dataVar (.bytes out) }
        evm' stmts Q) :
    BlockProgress code ee g s0 cfg frame evm
      (.lowLevelCall receiver eth cdata okVar dataVar perm :: stmts) Q := by
  obtain ⟨z, out, evm', world', k', C', rd, hcall, hr, hsize⟩ := hpair
  have hnext := hcontinue z out evm' world' k' C' rd hcall hr hsize
  cases z with
  | false => exact BlockProgress.cons (ExecStmt.lowLevelCallFailure hreceiver heth hdata hcall) hnext
  | true => exact BlockProgress.cons (ExecStmt.lowLevelCallSuccess hreceiver heth hdata hcall) hnext

/-- DELEGATECALL binds both raw results and continues even when `z = false`.
Use `delegateCallPaired` for the boundary premise. -/
theorem BlockProgress.delegateCall {code ee g s0 evm cfg frame}
    {receiver cdata : Expr} {tgt : EVM.Address} {calldata : ByteArray}
    {okVar dataVar : Ident} {stmts : List Stmt} {Q : ExitRel}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair : PairedCall code ee g s0
      (fun result => delegateCallViaEVM evm (EVM.address tgt) calldata result) after)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (hdata : evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hcontinue : ∀ z out evm' world' k' C',
      let cur := after z out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      delegateCallViaEVM evm (EVM.address tgt) calldata (z, evm', out) →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      BlockProgress code ee g s0 cfg
        { frame with locals := (frame.locals.insert okVar (.bool z)).insert dataVar (.bytes out) }
        evm' stmts Q) :
    BlockProgress code ee g s0 cfg frame evm
      (.delegateCall receiver cdata okVar dataVar :: stmts) Q := by
  obtain ⟨z, out, evm', world', k', C', rd, hcall, hr, hsize⟩ := hpair
  have hnext := hcontinue z out evm' world' k' C' rd hcall hr hsize
  cases z with
  | false => exact BlockProgress.cons (ExecStmt.delegateCallFailure hreceiver hdata hcall) hnext
  | true => exact BlockProgress.cons (ExecStmt.delegateCallSuccess hreceiver hdata hcall) hnext

/-- Checked CALL/STATICCALL runs the chosen handler before the enclosing tail.
A handler's return/revert/break/continue skips the tail. Successful calls whose return
bytes fail decoding revert without entering the failure handler. -/
theorem BlockProgress.checkedCall {code ee g s0 evm cfg frame}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar errVar : Ident} {value : ℤ} {onSuccess onFail stmts : List Stmt}
    {Q : ExitRel} {perm : Bool} {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair : PairedCall code ee g s0
      (fun result => typedCallViaEVM cfg evm (EVM.address tgt) name value argVals result perm) after)
    (hreceiver : evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : evalExprs? cfg frame evm args = .ok argVals)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := after true out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) perm →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockProgress code ee g s0 cfg
          { frame with locals := frame.locals.insert retVar (collapseReturns values) }
          evm' (onSuccess ++ stmts) Q
      | none => RDrev code g s0)
    (hfailure : ∀ out evm' world' k' C',
      let cur := after false out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (false, evm', out) perm →
      CallStateRel s0 ee world' evm' → out.size < UInt256.size →
      BlockProgress code ee g s0 cfg { frame with locals := frame.locals.insert errVar (.bytes out) }
        evm' (onFail ++ stmts) Q) :
    BlockProgress code ee g s0 cfg frame evm
      (.checkedCall receiver name eth args retVar onSuccess errVar onFail perm :: stmts) Q := by
  obtain ⟨z, out, evm', world', k', C', rd, hcall, hr, hsize⟩ := hpair
  cases z with
  | false =>
      exact BlockProgress.wrapPrefix
        (fun _ hb => ExecStmt.checkedCallFail hreceiver heth hargs hcall hb)
        (hfailure out evm' world' k' C' rd hcall hr hsize)
  | true =>
      have hnext := hsuccess out evm' world' k' C' rd hcall hr hsize
      cases hd : cfg.externalABI.decode? name out with
      | none =>
          exact ⟨.reverted, .reverted,
            ExecBlock.consRevert (ExecStmt.checkedCallReturnDecodeRevert hreceiver heth hargs hcall hd),
            (by simpa only [hd] using hnext), hRevert⟩
      | some values =>
          exact BlockProgress.wrapPrefix
            (fun _ hb => ExecStmt.checkedCallSuccess hreceiver heth hargs hcall hd hb)
            (by simpa only [hd] using hnext)

/-- End relation for an internal function body. Its return value indexes the relation
at the EVM continuation cursor; fallthrough (and malformed escaping break/continue)
uses `none`, following `ExecFuncBody`. Source reverts must match EVM reverts. -/
def internalCallExit (R : Option (List Value) → StateRel) : ExitRel
  | .returned f e value, .reached cur => R value cur f e
  | .ok f e, .reached cur
  | .break f e, .reached cur
  | .continue f e, .reached cur => R none cur f e
  | .reverted, .reverted => True
  | _, _ => False

/-- Refine an internal call using paired progression for its body. The body summary
may combine manual RD steps with source evaluation; it returns both states to `hreturn`.
The caller's locals are restored before binding the returned value and running the tail. -/
theorem BlockProgress.internalCall {code ee g s0 evm cfg frame}
    {name retVar : Ident} {args : List Expr} {argVals : List Value} {callee locals}
    {stmts : List Stmt} {Q : ExitRel} {R : Option (List Value) → StateRel}
    (hargs : evalExprs? cfg frame evm args = .ok argVals)
    (hlookup : lookupCallable? frame.contract name = some callee)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : BlockProgress code ee g s0 cfg { frame with locals := locals } evm
      callee.body (internalCallExit R))
    (hRevert : Q .reverted .reverted)
    (hreturn : ∀ value cur calleeFrame calleeEvm k' C',
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      R value cur calleeFrame calleeEvm →
      BlockProgress code ee g s0 cfg (resumeAfterInternalCall frame retVar value) calleeEvm stmts Q) :
    BlockProgress code ee g s0 cfg frame evm (.internalCall name args retVar :: stmts) Q := by
  have finish {value cur calleeFrame calleeEvm}
      (hb : ExecFuncBody cfg { frame with locals := locals } evm callee.body
        (.returned calleeFrame calleeEvm value))
      (hr : ReachesEndpoint code ee g s0 (.reached cur))
      (hrel : R value cur calleeFrame calleeEvm) :
      BlockProgress code ee g s0 cfg frame evm (.internalCall name args retVar :: stmts) Q := by
    obtain ⟨k', C', rd⟩ := hr
    exact BlockProgress.cons (ExecStmt.internalCallReturn hargs hlookup hbind hb)
      (hreturn value cur calleeFrame calleeEvm k' C' rd hrel)
  rcases hbody with ⟨result, endpoint, hb, hr, hrel⟩
  cases result with
  | ok f e =>
      cases endpoint <;> simp only [internalCallExit] at hrel
      exact finish (ExecFuncBody.execBlockOK hb) hr hrel
  | returned f e value =>
      cases endpoint <;> simp only [internalCallExit] at hrel
      exact finish (ExecFuncBody.execBlockRet hb) hr hrel
  | reverted =>
      cases endpoint <;> simp only [internalCallExit] at hrel
      exact ⟨.reverted, .reverted,
        ExecBlock.consRevert (ExecStmt.internalCallRevert hargs hlookup hbind
          (ExecFuncBody.execBlockRevert hb)), hr, hRevert⟩
  | «break» f e =>
      cases endpoint <;> simp only [internalCallExit] at hrel
      exact finish (ExecFuncBody.execBlockBreak hb) hr hrel
  | «continue» f e =>
      cases endpoint <;> simp only [internalCallExit] at hrel
      exact finish (ExecFuncBody.execBlockContinue hb) hr hrel

/-- Fixed-start typed CALL/STATICCALL refinement. Derive the paired boundary from
incoming RD and `P`. Successful decoding continues with a fixed-start refinement;
raw failure and decode failure require only the corresponding EVM revert proof. -/
theorem BlockRefinesFrom.externalCallOfPaired {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P : StateRel}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar : Ident} {value : ℤ} {stmts : List Stmt} {Q : ExitRel} {perm : Bool}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair :
      RD code ee g s0 entry.pc entry.stack entry.mem entry.aw entry.rdata entry.world k C →
      P entry frame evm → PairedCall code ee g s0
      (fun result => typedCallViaEVM cfg evm (EVM.address tgt) name value argVals result perm) after)
    (hreceiver : P entry frame evm → evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : P entry frame evm → evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : P entry frame evm → evalExprs? cfg frame evm args = .ok argVals)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := after true out world'
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) perm →
      out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockRefinesFrom code ee g s0 cfg cur k' C'
          { frame with locals := frame.locals.insert retVar (collapseReturns values) }
          evm' (fun _ _ e => CallStateRel s0 ee world' e) stmts Q
      | none => RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
          RDrev code g s0)
    (hfailure : ∀ out world' k' C',
      let cur := after false out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      RDrev code g s0) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.externalCall receiver name eth args retVar perm :: stmts) Q := by
  intro rd hP
  refine BlockProgress.externalCallOfPaired (hpair rd hP)
    (hreceiver hP) (heth hP) (hargs hP) hRevert ?_ hfailure
  · intro out evm' world' k' C'
    dsimp only
    intro rd' hcall hr hsize
    have hnext := hsuccess out evm' world' k' C' hcall hsize
    cases hd : cfg.externalABI.decode? name out with
    | none =>
        simp only [hd] at hnext
        exact hnext rd'
    | some values =>
        simp only [hd] at hnext
        exact hnext rd' hr

/-- Fixed-start low-level CALL/STATICCALL refinement. The continuation receives
world agreement through its starting relation and runs for either raw flag. -/
theorem BlockRefinesFrom.lowLevelCall {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P : StateRel}
    {receiver eth cdata : Expr} {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {okVar dataVar : Ident} {stmts : List Stmt} {Q : ExitRel} {perm : Bool}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair :
      RD code ee g s0 entry.pc entry.stack entry.mem entry.aw entry.rdata entry.world k C →
      P entry frame evm → PairedCall code ee g s0
      (fun result => callViaEVM evm (EVM.address tgt) value calldata result perm) after)
    (hreceiver : P entry frame evm → evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : P entry frame evm → evalExpr? cfg frame evm eth = .ok (.int value))
    (hdata : P entry frame evm → evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hcontinue : ∀ z out evm' world' k' C',
      let cur := after z out world'
      callViaEVM evm (EVM.address tgt) value calldata (z, evm', out) perm →
      out.size < UInt256.size →
      BlockRefinesFrom code ee g s0 cfg cur k' C'
        { frame with locals := (frame.locals.insert okVar (.bool z)).insert dataVar (.bytes out) }
        evm' (fun _ _ e => CallStateRel s0 ee world' e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.lowLevelCall receiver eth cdata okVar dataVar perm :: stmts) Q := by
  intro rd hP
  apply BlockProgress.lowLevelCall (hpair rd hP) (hreceiver hP) (heth hP) (hdata hP)
  intro z out evm' world' k' C'
  dsimp only
  intro rd' hcall hr hsize
  exact hcontinue z out evm' world' k' C' hcall hsize rd' hr

/-- Fixed-start DELEGATECALL refinement, preserving the native delegate-call
relation. Both raw flags continue with the flag and output bytes bound. -/
theorem BlockRefinesFrom.delegateCall {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P : StateRel}
    {receiver cdata : Expr} {tgt : EVM.Address} {calldata : ByteArray}
    {okVar dataVar : Ident} {stmts : List Stmt} {Q : ExitRel}
    {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair :
      RD code ee g s0 entry.pc entry.stack entry.mem entry.aw entry.rdata entry.world k C →
      P entry frame evm → PairedCall code ee g s0
      (fun result => delegateCallViaEVM evm (EVM.address tgt) calldata result) after)
    (hreceiver : P entry frame evm → evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (hdata : P entry frame evm → evalExpr? cfg frame evm cdata = .ok (.bytes calldata))
    (hcontinue : ∀ z out evm' world' k' C',
      let cur := after z out world'
      delegateCallViaEVM evm (EVM.address tgt) calldata (z, evm', out) →
      out.size < UInt256.size →
      BlockRefinesFrom code ee g s0 cfg cur k' C'
        { frame with locals := (frame.locals.insert okVar (.bool z)).insert dataVar (.bytes out) }
        evm' (fun _ _ e => CallStateRel s0 ee world' e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.delegateCall receiver cdata okVar dataVar :: stmts) Q := by
  intro rd hP
  apply BlockProgress.delegateCall (hpair rd hP) (hreceiver hP) (hdata hP)
  intro z out evm' world' k' C'
  dsimp only
  intro rd' hcall hr hsize
  exact hcontinue z out evm' world' k' C' hcall hsize rd' hr

/-- Fixed-start checked CALL/STATICCALL refinement. Handler-plus-tail proofs are
local refinements at the selected post-call pair. Decode failures still revert uncaught. -/
theorem BlockRefinesFrom.checkedCall {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P : StateRel}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar errVar : Ident} {value : ℤ} {onSuccess onFail stmts : List Stmt}
    {Q : ExitRel} {perm : Bool} {after : Bool → ByteArray → CallWorld → Cursor}
    (hpair :
      RD code ee g s0 entry.pc entry.stack entry.mem entry.aw entry.rdata entry.world k C →
      P entry frame evm → PairedCall code ee g s0
      (fun result => typedCallViaEVM cfg evm (EVM.address tgt) name value argVals result perm) after)
    (hreceiver : P entry frame evm → evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : P entry frame evm → evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : P entry frame evm → evalExprs? cfg frame evm args = .ok argVals)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := after true out world'
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) perm →
      out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockRefinesFrom code ee g s0 cfg cur k' C'
          { frame with locals := frame.locals.insert retVar (collapseReturns values) }
          evm' (fun _ _ e => CallStateRel s0 ee world' e) (onSuccess ++ stmts) Q
      | none => RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
          RDrev code g s0)
    (hfailure : ∀ out evm' world' k' C',
      let cur := after false out world'
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (false, evm', out) perm →
      out.size < UInt256.size →
      BlockRefinesFrom code ee g s0 cfg cur k' C'
        { frame with locals := frame.locals.insert errVar (.bytes out) }
        evm' (fun _ _ e => CallStateRel s0 ee world' e) (onFail ++ stmts) Q) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.checkedCall receiver name eth args retVar onSuccess errVar onFail perm :: stmts) Q := by
  intro rd hP
  refine BlockProgress.checkedCall (hpair rd hP)
    (hreceiver hP) (heth hP) (hargs hP) hRevert ?_ ?_
  · intro out evm' world' k' C'
    dsimp only
    intro rd' hcall hr hsize
    have hnext := hsuccess out evm' world' k' C' hcall hsize
    cases hd : cfg.externalABI.decode? name out with
    | none =>
        simp only [hd] at hnext
        exact hnext rd'
    | some values =>
        simp only [hd] at hnext
        exact hnext rd' hr
  · intro out evm' world' k' C'
    dsimp only
    intro rd' hcall hr hsize
    exact hfailure out evm' world' k' C' hcall hsize rd' hr

/-- Fixed-start internal call refinement. `hentry` transfers the caller relation
to the callee's parameter frame. The body and return continuation are themselves
local refinements; the return relation retains the callee frame while execution resumes
in the caller's restored frame. -/
theorem BlockRefinesFrom.internalCall {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P B : StateRel}
    {name retVar : Ident} {args : List Expr} {argVals : List Value} {callee locals}
    {stmts : List Stmt} {Q : ExitRel} {R : Option (List Value) → StateRel}
    (hargs : P entry frame evm → evalExprs? cfg frame evm args = .ok argVals)
    (hlookup : lookupCallable? frame.contract name = some callee)
    (hbind : bindParams? callee.params argVals = some locals)
    (hentry : P entry frame evm → B entry { frame with locals := locals } evm)
    (hbody : BlockRefinesFrom code ee g s0 cfg entry k C { frame with locals := locals } evm B
      callee.body (internalCallExit R))
    (hRevert : Q .reverted .reverted)
    (hreturn : ∀ value cur calleeFrame calleeEvm k' C',
      BlockRefinesFrom code ee g s0 cfg cur k' C'
        (resumeAfterInternalCall frame retVar value) calleeEvm
        (fun cur _ e => R value cur calleeFrame e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.internalCall name args retVar :: stmts) Q := by
  intro rd hP
  exact BlockProgress.internalCall (hargs hP) hlookup hbind (hbody rd (hentry hP)) hRevert hreturn

/-- Fixed-start ordinary CALL rule. Operand and source-evaluation agreement can be
derived from `P`; the incoming RD supplies the CALL cursor. Successful continuations
are local refinements, while raw failure requires only EVM reversion. -/
theorem BlockRefinesFrom.externalCall {code ee g s0 evm cfg frame}
    {entry : Cursor} {k C : ℕ} {P : StateRel}
    {gasArg target valueWord inOffset inSize outOffset outSize : UInt256} {rest : List UInt256}
    {receiver eth : Expr} {args : List Expr} {argVals : List Value} {tgt : EVM.Address}
    {name retVar : Ident} {value : ℤ} {stmts : List Stmt} {Q : ExitRel}
    (hstack : P entry frame evm → entry.stack =
      gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: rest)
    (hState : P entry frame evm → CallStateRel s0 ee entry.world evm)
    (hreceiver : P entry frame evm → evalExpr? cfg frame evm receiver = .ok (.address tgt))
    (heth : P entry frame evm → evalExpr? cfg frame evm eth = .ok (.int value))
    (hargs : P entry frame evm → evalExprs? cfg frame evm args = .ok argVals)
    (hword : P entry frame evm → valueWord = EVM.wordOfInt value)
    (htarget : P entry frame evm → EVM.address tgt = AccountAddress.ofUInt256 target)
    (hencode : P entry frame evm → cfg.externalABI.encode? name argVals =
      some (entry.mem.readWithPadding inOffset.toNat inSize.toNat))
    (hdec : decode code entry.pc = some (.CALL, .none)) (hperm : ee.perm = true)
    (hov : rest.length + 1 ≤ 1024)
    (hRevert : Q .reverted .reverted)
    (hsuccess : ∀ out evm' world' k' C',
      let cur := callCursor entry.pc rest entry.mem entry.aw inOffset inSize outOffset outSize true out world'
      typedCallViaEVM cfg evm (EVM.address tgt) name value argVals (true, evm', out) →
      out.size < UInt256.size →
      match cfg.externalABI.decode? name out with
      | some values => BlockRefinesFrom code ee g s0 cfg cur k' C'
          { frame with locals := frame.locals.insert retVar (collapseReturns values) }
          evm' (fun _ _ e => CallStateRel s0 ee world' e) stmts Q
      | none => RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
          RDrev code g s0)
    (hfailure : ∀ out world' k' C',
      let cur := callCursor entry.pc rest entry.mem entry.aw inOffset inSize outOffset outSize false out world'
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k' C' →
      RDrev code g s0) :
    BlockRefinesFrom code ee g s0 cfg entry k C frame evm P
      (.externalCall receiver name eth args retVar :: stmts) Q := by
  apply BlockRefinesFrom.externalCallOfPaired
    (after := callCursor entry.pc rest entry.mem entry.aw inOffset inSize outOffset outSize)
    ?_ hreceiver heth hargs hRevert hsuccess hfailure
  intro rd hP
  rw [hstack hP] at rd
  exact callPaired rd (hState hP) (hword hP) (htarget hP) (hencode hP) hdec hperm hov

end Reasoning.Refinement
