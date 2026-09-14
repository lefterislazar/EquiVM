import Reasoning.ExternalCall
import Ethereum.Theory.AccountLocality

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

private abbrev PreservesPresent (σ τ : AccountMap) : Prop :=
  ∀ {addr : AccountAddress} {acc : Account},
    σ.find? addr = some acc → ∃ acc', τ.find? addr = some acc'

private theorem accountMap_insert_present {σ : AccountMap} {addr key : AccountAddress}
    {acc newAcc : Account}
    (hfind : σ.find? addr = some acc) :
    ∃ acc', (σ.insert key newAcc).find? addr = some acc' := by
  by_cases hcmp : compare addr key = .eq
  · exact ⟨newAcc, Batteries.RBMap.find?_insert_of_eq σ hcmp⟩
  · exact ⟨acc, by simpa [Batteries.RBMap.find?_insert_of_ne σ hcmp] using hfind⟩

private theorem accountMap_insert_insert_present {σ : AccountMap}
    {addr k₁ k₂ : AccountAddress} {acc new₁ new₂ : Account}
    (hfind : σ.find? addr = some acc) :
    ∃ acc', ((σ.insert k₁ new₁).insert k₂ new₂).find? addr = some acc' := by
  rcases accountMap_insert_present (key := k₁) (newAcc := new₁) hfind with ⟨acc₁, h₁⟩
  exact accountMap_insert_present (key := k₂) (newAcc := new₂) h₁

private theorem present_of_accountMap_eq {σ τ : AccountMap} {addr : AccountAddress}
    {acc : Account}
    (h : τ = σ) (hfind : σ.find? addr = some acc) :
    ∃ acc', τ.find? addr = some acc' := by
  rw [h]
  exact ⟨acc, hfind⟩

private theorem present_if_empty_or_self {σ τ self : AccountMap} {addr : AccountAddress}
    {acc : Account}
    (hfind : σ.find? addr = some acc)
    (hself : ∃ acc', self.find? addr = some acc')
    (hτ : τ = ∅ ∨ τ = self) :
    ∃ acc', (if τ == ∅ then σ else τ).find? addr = some acc' := by
  rcases hτ with hτ | hτ
  · subst τ
    simp [rbMap_empty_beq_empty]
    exact ⟨acc, hfind⟩
  · subst τ
    by_cases hEmpty : (self == (∅ : AccountMap)) = true
    · simp [hEmpty]
      exact ⟨acc, hfind⟩
    · simp [hEmpty]
      exact hself

private theorem sendEth_present {σ : AccountMap} {addr r s : AccountAddress}
    {acc : Account} (v : UInt256) (z : Bool)
    (hfind : σ.find? addr = some acc) :
    ∃ acc', (sendEth r s v z σ).find? addr = some acc' := by
  cases z
  · simp [sendEth]
    exact ⟨acc, hfind⟩
  · unfold sendEth
    simp
    set σ₁ : AccountMap := match σ.find? r with
      | none =>
          if v = UInt256.ofNat 0 then σ
          else σ.insert r {(default : Account) with balance := v}
      | some racc =>
          σ.insert r {racc with balance := racc.balance + v} with hσ₁
    change ∃ acc', (match σ₁.find? s with
      | none => σ₁
      | some sacc =>
          σ₁.insert s {sacc with balance := sacc.balance - v}).find? addr = some acc'
    have hσ₁present : ∃ acc₁, σ₁.find? addr = some acc₁ := by
      subst σ₁
      cases hr : σ.find? r with
      | none =>
          by_cases hv : v = UInt256.ofNat 0
          · simp [hr, hv]
            exact ⟨acc, hfind⟩
          · simp [hr, hv]
            exact accountMap_insert_present (key := r)
              (newAcc := {(default : Account) with balance := v}) hfind
      | some racc =>
          simp [hr]
          exact accountMap_insert_present (key := r)
            (newAcc := {racc with balance := racc.balance + v}) hfind
    rcases hσ₁present with ⟨acc₁, h₁⟩
    cases hs : σ₁.find? s with
    | none =>
        simpa [hs] using (show ∃ acc', σ₁.find? addr = some acc' from ⟨acc₁, h₁⟩)
    | some sacc =>
        simpa [hs] using accountMap_insert_present (key := s)
          (newAcc := {sacc with balance := sacc.balance - v}) h₁

private theorem sendEthCreate_present {σ : AccountMap} {addr a s : AccountAddress}
    {acc : Account} (v : UInt256) (z : Bool)
    (hfind : σ.find? addr = some acc) :
    ∃ acc', (sendEthCreate a s v z σ).find? addr = some acc' := by
  cases z
  · simp [sendEthCreate]
    exact ⟨acc, hfind⟩
  · unfold sendEthCreate
    simp
    cases hs : σ.find? s with
    | none =>
        simp [hs]
        exact ⟨acc, hfind⟩
    | some sacc =>
        simp [hs]
        rcases accountMap_insert_present (key := s)
          (newAcc := {sacc with balance := sacc.balance - v}) hfind with ⟨acc₁, h₁⟩
        exact accountMap_insert_present (key := a)
          (newAcc := { (σ.findD a default) with
            nonce := (σ.findD a default).nonce + ⟨1⟩,
            balance := v + (σ.findD a default).balance }) h₁

private lemma depth_succ_measure {e : Fin 1025} {n : Nat}
    (hdepth : 1024 - e.val = n + 1) (hlt : e < 1024) :
    1024 - (e + 1).val = n := by
  have hval : (e + 1).val = e.val + 1 := by
    rw [Fin.val_add_eq_of_add_lt]
    simp
    omega
  omega

private lemma depth_succ_measure_mk {e : Fin 1025} {n : Nat}
    (hdepth : 1024 - e.val = n + 1) (hlt : e < 1024) :
    1024 - (⟨e.val + 1, Nat.succ_lt_succ hlt⟩ : Fin 1025).val = n := by
  simp
  omega

private lemma execUnOp_accountMap_eq {f : Primop.Unary} {state stateOut : State}
    (h : execUnOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold execUnOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma execBinOp_accountMap_eq {f : Primop.Binary} {state stateOut : State}
    (h : execBinOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold execBinOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma execTriOp_accountMap_eq {f : Primop.Ternary} {state stateOut : State}
    (h : execTriOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold execTriOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma machineStateOp_accountMap_eq {f : MachineState → UInt256}
    {state stateOut : State}
    (h : machineStateOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold machineStateOp at h
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma executionEnvOp_accountMap_eq {f : ExecutionEnv → UInt256}
    {state stateOut : State}
    (h : executionEnvOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold executionEnvOp at h
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma unaryExecutionEnvOp_accountMap_eq
    {f : ExecutionEnv → UInt256 → UInt256} {state stateOut : State}
    (h : unaryExecutionEnvOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold unaryExecutionEnvOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma unaryStateOp_sameState_accountMap_eq
    {f : State → UInt256 → UInt256} {state stateOut : State}
    (h : unaryStateOp (fun s v => (s, f s v)) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma unaryStateOp_accountMap_eq
    {f : State → UInt256 → State × UInt256} {state stateOut : State}
    (hf : ∀ s v, (f s v).1.accountMap = s.accountMap)
    (h : unaryStateOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold unaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hf] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma stateOp_accountMap_eq {f : State → UInt256} {state stateOut : State}
    (h : stateOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold stateOp at h
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma binaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → MachineState} {state stateOut : State}
    (h : binaryMachineStateOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold binaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma binaryMachineStateOp'_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState} {state stateOut : State}
    (h : binaryMachineStateOp' f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold binaryMachineStateOp' at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma ternaryMachineStateOp_accountMap_eq
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    {state stateOut : State}
    (h : ternaryMachineStateOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold ternaryMachineStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma ternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → State} {state stateOut : State}
    (hcopy : ∀ s a b c, (f s a b c).accountMap = s.accountMap)
    (h : ternaryCopyOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold ternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma quaternaryCopyOp_accountMap_eq
    {f : State → UInt256 → UInt256 → UInt256 → UInt256 → State}
    {state stateOut : State}
    (hcopy : ∀ s a b c d, (f s a b c d).accountMap = s.accountMap)
    (h : quaternaryCopyOp f state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold quaternaryCopyOp at h
  split at h <;> try contradiction
  injection h with hstate
  simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, hcopy] using
    congrArg (fun st : State => st.accountMap) hstate.symm

private lemma calldatacopy_accountMap_eq
    (state : State) (mstart datastart size : UInt256) :
    (calldatacopy state mstart datastart size).accountMap = state.accountMap := by
  simp [calldatacopy]

private lemma codeCopy_accountMap_eq
    (state : State) (mstart cstart size : UInt256) :
    (codeCopy state mstart cstart size).accountMap = state.accountMap := by
  simp [codeCopy]

private lemma extCodeCopy'_accountMap_eq
    (state : State) (a mstart cstart size : UInt256) :
    (extCodeCopy' state a mstart cstart size).accountMap = state.accountMap := by
  simp [extCodeCopy', Ethereum.State.lookupAccount]

private lemma logOp_accountMap_eq
    {μ₀ μ₁ : UInt256} {topics : Array UInt256} {state : State} :
    (logOp μ₀ μ₁ topics state).accountMap = state.accountMap := by
  simp [logOp]

private lemma evmLogOp_accountMap_eq
    {μ₀ μ₁ : UInt256} {topics : Array UInt256} {state : State} :
    (evmLogOp state μ₀ μ₁ topics).accountMap = state.accountMap := by
  simp [evmLogOp, logOp_accountMap_eq]

private theorem sstore_present {state : State} {addr : AccountAddress} {acc : Account}
    (key value : UInt256)
    (hfind : state.accountMap.find? addr = some acc) :
    ∃ acc', (Ethereum.State.sstore state key value).accountMap.find? addr = some acc' := by
  cases howner : state.accountMap.find? state.executionEnv.codeOwner with
  | none =>
      simp [Ethereum.State.sstore, Ethereum.State.lookupAccount, howner]
      exact ⟨acc, hfind⟩
  | some owner =>
      simp [Ethereum.State.sstore, Ethereum.State.lookupAccount, Ethereum.State.setAccount,
        Ethereum.State.addAccessedStorageKey, howner]
      split
      · exact accountMap_insert_present (key := state.executionEnv.codeOwner) hfind
      · exact accountMap_insert_present (key := state.executionEnv.codeOwner) hfind

private theorem tstore_present {state : State} {addr : AccountAddress} {acc : Account}
    (key value : UInt256)
    (hfind : state.accountMap.find? addr = some acc) :
    ∃ acc', (Ethereum.State.tstore state key value).accountMap.find? addr = some acc' := by
  cases howner : state.accountMap.find? state.executionEnv.codeOwner with
  | none =>
      simp [Ethereum.State.tstore, Ethereum.State.lookupAccount, howner]
      exact ⟨acc, hfind⟩
  | some owner =>
      simp [Ethereum.State.tstore, Ethereum.State.lookupAccount, Ethereum.State.updateAccount,
        howner]
      exact accountMap_insert_present (key := state.executionEnv.codeOwner) hfind

private lemma binaryStateOp_present
    {op : State → UInt256 → UInt256 → State} {state stateOut : State}
    {addr : AccountAddress} {acc : Account}
    (hop : ∀ a b, ∃ acc', (op state a b).accountMap.find? addr = some acc')
    (h : binaryStateOp op state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  unfold binaryStateOp at h
  split at h <;> try contradiction
  injection h with hstate
  rw [← hstate]
  exact hop _ _

private lemma dup_accountMap_eq {n : Nat} {state stateOut : State}
    (h : dup n state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold dup at h
  by_cases hlen : (List.take n state.machineState.stack).length = n
  · rw [if_pos hlen] at h
    injection h with hstate
    simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
      congrArg (fun st : State => st.accountMap) hstate.symm
  · rw [if_neg hlen] at h
    contradiction

private lemma swap_accountMap_eq {n : Nat} {state stateOut : State}
    (h : swap n state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  unfold swap at h
  by_cases hlen : (List.take (n + 1) state.machineState.stack).length = n + 1
  · rw [if_pos hlen] at h
    injection h with hstate
    simpa [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
      congrArg (fun st : State => st.accountMap) hstate.symm
  · rw [if_neg hlen] at h
    contradiction

private lemma step_stoparith_accountMap_eq
    {op : Operation.SAOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.StopArith op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op with
  | STOP =>
      simp [step] at h
      rw [← h]
  | ADD | MUL | SUB | DIV | SDIV | MOD | SMOD | EXP | SIGNEXTEND =>
      simp [step] at h
      simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  | ADDMOD | MULMOD =>
      simp [step] at h
      simpa [charged] using execTriOp_accountMap_eq (state := charged) h

private lemma step_compbit_accountMap_eq
    {op : Operation.CBLOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.CompBit op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op <;> simp [step] at h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execUnOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execUnOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h
  · simpa [charged] using execBinOp_accountMap_eq (state := charged) h

private lemma step_keccak_accountMap_eq
    {op : Operation.KOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Keccak op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op
  simp [step] at h
  simpa [charged] using binaryMachineStateOp'_accountMap_eq (state := charged) h

private lemma step_env_accountMap_eq
    {op : Operation.EOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Env op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op <;> simp [step] at h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using unaryStateOp_accountMap_eq (state := charged)
      (f := Ethereum.State.balance)
      (by intro s v; simp [Ethereum.State.balance, Ethereum.State.addAccessedAccount])
      h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using unaryStateOp_sameState_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using
      ternaryCopyOp_accountMap_eq (state := charged) calldatacopy_accountMap_eq h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using
      ternaryCopyOp_accountMap_eq (state := charged) codeCopy_accountMap_eq h
  · simpa [charged] using unaryStateOp_accountMap_eq (state := charged)
      (f := Ethereum.State.extCodeSize)
      (by intro s v; simp [Ethereum.State.extCodeSize, Ethereum.State.addAccessedAccount])
      h
  · simpa [charged] using
      quaternaryCopyOp_accountMap_eq (state := charged) extCodeCopy'_accountMap_eq h
  · simpa [charged] using machineStateOp_accountMap_eq (state := charged) h
  · split at h <;> try contradiction
    injection h with hstate
    simpa [charged, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] using
      congrArg (fun st : State => st.accountMap) hstate.symm
  · simpa [charged] using unaryStateOp_accountMap_eq (state := charged)
      (f := Ethereum.State.extCodeHash)
      (by
        intro s v
        simp [Ethereum.State.extCodeHash, Ethereum.State.addAccessedAccount,
          Ethereum.State.lookupAccount]
        split <;> simp)
      h

private lemma step_push_accountMap_eq
    {op : Operation.POp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Push op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op with
  | PUSH0 =>
      simp [step, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      rw [← h]
  | PUSH1 | PUSH2 | PUSH3 | PUSH4 | PUSH5 | PUSH6 | PUSH7 | PUSH8 | PUSH9 | PUSH10
  | PUSH11 | PUSH12 | PUSH13 | PUSH14 | PUSH15 | PUSH16 | PUSH17 | PUSH18 | PUSH19 | PUSH20
  | PUSH21 | PUSH22 | PUSH23 | PUSH24 | PUSH25 | PUSH26 | PUSH27 | PUSH28 | PUSH29 | PUSH30
  | PUSH31 | PUSH32 =>
      simp [step, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
      split at h <;> try contradiction
      injection h with hstate
      simpa [charged] using congrArg (fun st : State => st.accountMap) hstate.symm

private lemma step_dup_accountMap_eq
    {op : Operation.DOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Dup op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op <;> simp [step] at h
  all_goals simpa [charged] using dup_accountMap_eq (state := charged) h

private lemma step_exchange_accountMap_eq
    {op : Operation.ExOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Exchange op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op <;> simp [step] at h
  all_goals simpa [charged] using swap_accountMap_eq (state := charged) h

private lemma step_block_accountMap_eq
    {op : Operation.BOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Block op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  cases op <;> simp [step] at h
  · simpa [charged] using unaryStateOp_sameState_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using stateOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using unaryExecutionEnvOp_accountMap_eq (state := charged) h
  · simpa [charged] using executionEnvOp_accountMap_eq (state := charged) h

private lemma step_log_accountMap_eq
    {op : Operation.LOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State}
    (h : step gasCost (.Log op, arg) state = .ok stateOut) :
    stateOut.accountMap = state.accountMap := by
  cases op <;>
    simp [step, log0Op, log1Op, log2Op, log3Op, log4Op, evmLogOp,
      Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  all_goals
    repeat split at h <;> try contradiction
    injection h with hstate
    simpa [logOp] using congrArg (fun st : State => st.accountMap) hstate.symm

private lemma step_stackmemflow_present
    {op : Operation.SMSFOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.StackMemFlow op, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by
    simpa [charged] using hfind
  cases op <;> simp [step] at h
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact ⟨acc, hfindCharged⟩
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact ⟨acc, hfindCharged⟩
  · exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · have hm := unaryStateOp_accountMap_eq (state := charged)
      (f := Ethereum.State.sload)
      (by intro s v; simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
        Ethereum.State.lookupAccount]) h
    exact present_of_accountMap_eq hm hfindCharged
  · exact binaryStateOp_present (state := charged) (op := Ethereum.State.sstore)
      (acc := acc) (fun a b => sstore_present a b hfindCharged) h
  · exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact ⟨acc, hfindCharged⟩
  · split at h <;> try contradiction
    injection h with hstate
    rw [← hstate]
    exact ⟨acc, hfindCharged⟩
  · rw [← h]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact ⟨acc, hfindCharged⟩
  · exact present_of_accountMap_eq
      (machineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · exact present_of_accountMap_eq
      (machineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · rw [← h]
    simp [Ethereum.State.incrPC]
    exact ⟨acc, hfindCharged⟩
  · have hm := unaryStateOp_accountMap_eq (state := charged)
      (f := Ethereum.State.tload)
      (by intro s v; simp [Ethereum.State.tload]) h
    exact present_of_accountMap_eq hm hfindCharged
  · exact binaryStateOp_present (state := charged) (op := Ethereum.State.tstore)
      (acc := acc) (fun a b => tstore_present a b hfindCharged) h
  · exact present_of_accountMap_eq
      (ternaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged

private lemma step_selfdestruct_present
    {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.System .SELFDESTRUCT, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by simpa [charged] using hfind
  simp [step, Ethereum.State.lookupAccount] at h
  cases hpop : charged.machineState.stack.pop with
  | none =>
      simp [hpop, charged] at h
  | some popped =>
      rcases popped with ⟨stack, targetWord⟩
      let target : AccountAddress := AccountAddress.ofUInt256 targetWord
      by_cases hcreated : charged.executionEnv.codeOwner ∈ charged.createdAccounts
      · cases howner : charged.accountMap.find? charged.executionEnv.codeOwner with
        | none =>
            simp [hpop, hcreated, howner, target, charged] at h
            rw [← h]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
            exact ⟨acc, hfind⟩
        | some ownerAcc =>
            cases htarget : charged.accountMap.find? target with
            | none =>
                by_cases hzero : ownerAcc.balance = ({ val := 0 } : UInt256)
                · simp [hpop, hcreated, howner, hzero, target, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, charged]
                  exact ⟨acc, hfind⟩
                · simp [hpop, hcreated, howner, hzero, target, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, charged]
                  exact accountMap_insert_insert_present (k₁ := target)
                    (k₂ := charged.executionEnv.codeOwner)
                    (new₁ := {(default : Account) with balance := ownerAcc.balance})
                    (new₂ := {ownerAcc with balance := { val := 0 }}) hfindCharged
            | some targetAcc =>
                by_cases hsame : target = charged.executionEnv.codeOwner
                · simp [hpop, hcreated, howner, target, hsame, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    howner, hsame, charged]
                  exact accountMap_insert_insert_present (k₁ := charged.executionEnv.codeOwner)
                    (k₂ := charged.executionEnv.codeOwner)
                    (new₁ := {ownerAcc with balance := { val := 0 }})
                    (new₂ := {ownerAcc with balance := { val := 0 }}) hfindCharged
                · simp [hpop, hcreated, howner, target, htarget, hsame, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, hsame, charged]
                  exact accountMap_insert_insert_present (k₁ := target)
                    (k₂ := charged.executionEnv.codeOwner)
                    (new₁ := {targetAcc with balance := targetAcc.balance + ownerAcc.balance})
                    (new₂ := {ownerAcc with balance := { val := 0 }}) hfindCharged
      · cases howner : charged.accountMap.find? charged.executionEnv.codeOwner with
        | none =>
            simp [hpop, hcreated, howner, target, charged] at h
            rw [← h]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
            exact ⟨acc, hfind⟩
        | some ownerAcc =>
            cases htarget : charged.accountMap.find? target with
            | none =>
                by_cases hzero : ownerAcc.balance = ({ val := 0 } : UInt256)
                · simp [hpop, hcreated, howner, hzero, target, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, charged]
                  exact ⟨acc, hfind⟩
                · simp [hpop, hcreated, howner, hzero, target, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, charged]
                  exact accountMap_insert_insert_present (k₁ := target)
                    (k₂ := charged.executionEnv.codeOwner)
                    (new₁ := {(default : Account) with balance := ownerAcc.balance})
                    (new₂ := {ownerAcc with balance := { val := 0 }}) hfindCharged
            | some targetAcc =>
                by_cases hsame : target = charged.executionEnv.codeOwner
                · simp [hpop, hcreated, howner, target, hsame, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    howner, hsame, charged]
                  exact ⟨acc, hfind⟩
                · simp [hpop, hcreated, howner, target, htarget, hsame, charged] at h
                  rw [← h]
                  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, target,
                    htarget, hsame, charged]
                  exact accountMap_insert_insert_present (k₁ := target)
                    (k₂ := charged.executionEnv.codeOwner)
                    (new₁ := {targetAcc with balance := targetAcc.balance + ownerAcc.balance})
                    (new₂ := {ownerAcc with balance := { val := 0 }}) hfindCharged

private lemma call_present_max_depth
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value valueIn inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState stateOut : State}
    {addr : AccountAddress} {acc : Account}
    (hdepth : evmState.executionEnv.depth = 1024)
    (hfind : evmState.accountMap.find? addr = some acc)
    (h : call gasCost blobVersionedHashes gas source recipient t value valueIn
        inOffset inSize outOffset outSize permission evmState = .ok (x, stateOut)) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  unfold call at h
  simp [hdepth] at h
  rcases h with ⟨_, hstate⟩
  rw [← hstate]
  simp
  exact ⟨acc, hfind⟩

private lemma call_present_succ_depth
    {gasCost n : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value valueIn inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState stateOut : State}
    {addr : AccountAddress} {acc : Account}
    (hdepth : 1024 - evmState.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
        (d : ByteArray) (H : BlockHeader) (w : Bool)
        (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
        (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v vRep d e H w =
            (cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (hfind : evmState.accountMap.find? addr = some acc)
    (h : call gasCost blobVersionedHashes gas source recipient t value valueIn
        inOffset inSize outOffset outSize permission evmState = .ok (x, stateOut)) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    exact ihTheta
      blobVersionedHashes evmState.genesisBlockHeader evmState.blocks
      evmState.createdAccounts (evmState.executionEnv.depth + 1)
      evmState.accountMap evmState.σ₀
      ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
      (AccountAddress.ofUInt256 source)
      evmState.executionEnv.sender
      (AccountAddress.ofUInt256 recipient)
      (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
      (UInt256.ofNat
        (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
          value gas evmState.accountMap evmState.machineState evmState.substate))
      (UInt256.ofNat evmState.executionEnv.gasPrice)
      value valueIn
      (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
      evmState.executionEnv.header permission
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.2.1
      (Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value valueIn
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header permission).2.2.2.2.2
      (depth_succ_measure hdepth hcall.2) rfl hfind
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp
    exact ⟨acc, hfind⟩

private lemma step_create_present_succ_depth
    {gasCost n : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
        (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
        (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
        (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
        (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.System .CREATE, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by simpa [charged] using hfind
  simp [step] at h
  cases hpop : charged.machineState.stack.pop3 with
  | none =>
      simp [hpop, charged] at h
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂⟩
      let initCode := charged.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat
      let owner : Account := (charged.accountMap.find? charged.executionEnv.codeOwner).getD default
      let σStar : AccountMap :=
        charged.accountMap.insert charged.executionEnv.codeOwner
          {owner with nonce := owner.nonce + ⟨1⟩}
      by_cases hnonce :
          ((charged.accountMap.find? charged.executionEnv.codeOwner).getD default).nonce.toNat ≥
            2 ^ 64 - 1
      · simp [hpop, hnonce, charged] at h
        repeat split at h <;> try contradiction
        all_goals
          injection h with hstate
          rw [← hstate]
          simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
          exact ⟨acc, hfindCharged⟩
      · by_cases hDepth :
            μ₀ ≤ (charged.accountMap.find? charged.executionEnv.codeOwner |>.option ⟨0⟩
              (·.balance)) ∧
              charged.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152
        · have hpre : ∃ acc₁, σStar.find? addr = some acc₁ :=
            accountMap_insert_present (key := charged.executionEnv.codeOwner)
              (newAcc := {owner with nonce := owner.nonce + ⟨1⟩}) hfindCharged
          rcases hpre with ⟨acc₁, hσStar⟩
          let eNext : Fin 1025 :=
            ⟨charged.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
          have hmeasure : 1024 - eNext.val = n := by
            dsimp [eNext, charged] at *
            omega
          have hrec :
              ∃ acc', (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.1.find? addr =
                  some acc' := by
            exact ihLambda
              charged.executionEnv.blobVersionedHashes charged.genesisBlockHeader charged.blocks
              charged.createdAccounts eNext σStar charged.σ₀ charged.substate
              charged.executionEnv.codeOwner charged.executionEnv.sender
              (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
              (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode none
              charged.executionEnv.header charged.executionEnv.perm
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext none
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.2.2
              hmeasure rfl hσStar
          simp [hpop, hnonce, hDepth, initCode, owner, σStar, eNext, charged] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact hrec
        · simp [hpop, hnonce, hDepth, initCode, owner, σStar, charged] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact ⟨acc, hfindCharged⟩

private lemma step_create2_present_succ_depth
    {gasCost n : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
        (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
        (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
        (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
        (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.System .CREATE2, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by simpa [charged] using hfind
  simp [step] at h
  cases hpop : charged.machineState.stack.pop4 with
  | none =>
      simp [hpop, charged] at h
  | some popped =>
      rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃⟩
      let initCode := charged.machineState.memory.readWithPadding μ₁.toNat μ₂.toNat
      let salt := some (UInt256.toByteArray μ₃)
      let owner : Account := (charged.accountMap.find? charged.executionEnv.codeOwner).getD default
      let σStar : AccountMap :=
        charged.accountMap.insert charged.executionEnv.codeOwner
          {owner with nonce := owner.nonce + ⟨1⟩}
      by_cases hnonce :
          ((charged.accountMap.find? charged.executionEnv.codeOwner).getD default).nonce.toNat ≥
            2 ^ 64 - 1
      · simp [hpop, hnonce, charged] at h
        repeat split at h <;> try contradiction
        all_goals
          injection h with hstate
          rw [← hstate]
          simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
          exact ⟨acc, hfindCharged⟩
      · by_cases hDepth :
            μ₀ ≤ (charged.accountMap.find? charged.executionEnv.codeOwner |>.option ⟨0⟩
              (·.balance)) ∧
              charged.executionEnv.depth < 1024 ∧ initCode.size ≤ 49152
        · have hpre : ∃ acc₁, σStar.find? addr = some acc₁ :=
            accountMap_insert_present (key := charged.executionEnv.codeOwner)
              (newAcc := {owner with nonce := owner.nonce + ⟨1⟩}) hfindCharged
          rcases hpre with ⟨acc₁, hσStar⟩
          let eNext : Fin 1025 :=
            ⟨charged.executionEnv.depth.val + 1, Nat.succ_lt_succ hDepth.2.1⟩
          have hmeasure : 1024 - eNext.val = n := by
            dsimp [eNext, charged] at *
            omega
          have hrec :
              ∃ acc', (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.1.find? addr =
                  some acc' := by
            exact ihLambda
              charged.executionEnv.blobVersionedHashes charged.genesisBlockHeader charged.blocks
              charged.createdAccounts eNext σStar charged.σ₀ charged.substate
              charged.executionEnv.codeOwner charged.executionEnv.sender
              (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
              (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode salt
              charged.executionEnv.header charged.executionEnv.perm
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.2.1
              (Lambda charged.executionEnv.blobVersionedHashes charged.createdAccounts
                charged.genesisBlockHeader charged.blocks σStar charged.σ₀ charged.substate
                charged.executionEnv.codeOwner charged.executionEnv.sender
                (UInt256.ofNat (L charged.machineState.gasAvailable.toNat))
                (UInt256.ofNat charged.executionEnv.gasPrice) μ₀ initCode eNext salt
                charged.executionEnv.header charged.executionEnv.perm).2.2.2.2.2.2
              hmeasure rfl hσStar
          simp [hpop, hnonce, hDepth, initCode, salt, owner, σStar, eNext, charged] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact hrec
        · simp [hpop, hnonce, hDepth, initCode, salt, owner, σStar, charged] at h
          repeat split at h <;> try contradiction
          all_goals
            injection h with hstate
            rw [← hstate]
            simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
            exact ⟨acc, hfindCharged⟩

private lemma step_system_present_max_depth
    {op : Operation.SOp} {gasCost : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hdepth : state.executionEnv.depth = 1024)
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.System op, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by simpa [charged] using hfind
  cases op
  · simp [step, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step] at h
    exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step, call, hdepth, bind, Except.bind] at h
    repeat split at h <;> try contradiction
    all_goals
      injection h with hstate
      rw [← hstate]
      simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, charged]
      exact ⟨acc, hfind⟩
  · simp [step] at h
    exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · simp [step] at h
  · exact step_selfdestruct_present hfind h

private lemma step_system_present_succ_depth
    {op : Operation.SOp} {gasCost n : Nat} {arg : Option (UInt256 × Nat)}
    {state stateOut : State} {addr : AccountAddress} {acc : Account}
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
        (d : ByteArray) (H : BlockHeader) (w : Bool)
        (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
        (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v vRep d e H w =
            (cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
        (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
        (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
        (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
        (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (hfind : state.accountMap.find? addr = some acc)
    (h : step gasCost (.System op, arg) state = .ok stateOut) :
    ∃ acc', stateOut.accountMap.find? addr = some acc' := by
  let charged : State :=
    { state with machineState := { state.machineState with
        execLength := state.machineState.execLength + 1,
        gasAvailable := state.machineState.gasAvailable.subNat gasCost } }
  have hfindCharged : charged.accountMap.find? addr = some acc := by simpa [charged] using hfind
  cases op
  · exact step_create_present_succ_depth (n := n) hdepth ihLambda hfind h
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact call_present_succ_depth (n := n)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta hfind hcall
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact call_present_succ_depth (n := n)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta hfind hcall
  · simp [step] at h
    exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact call_present_succ_depth (n := n)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta hfind hcall
  · exact step_create2_present_succ_depth (n := n) hdepth ihLambda hfind h
  · simp [step, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at h <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection h with hstate
    rw [← hstate]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC]
    exact call_present_succ_depth (n := n)
      (evmState := {state with
        machineState := {state.machineState with execLength := state.machineState.execLength + 1}})
      hdepth ihTheta hfind hcall
  · simp [step] at h
    exact present_of_accountMap_eq
      (binaryMachineStateOp_accountMap_eq (state := charged) h) hfindCharged
  · simp [step] at h
  · exact step_selfdestruct_present hfind h

private theorem step_account_present_max_depth :
    ∀ gasCost instr state stateOut,
      state.executionEnv.depth = 1024 →
      step gasCost instr state = .ok stateOut →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro gasCost instr state stateOut hdepth hstep addr acc hfind
  rcases instr with ⟨op, arg⟩
  cases op with
  | StopArith op =>
      exact present_of_accountMap_eq
        (step_stoparith_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | CompBit op =>
      exact present_of_accountMap_eq
        (step_compbit_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Keccak op =>
      exact present_of_accountMap_eq
        (step_keccak_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Env op =>
      exact present_of_accountMap_eq
        (step_env_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Block op =>
      exact present_of_accountMap_eq
        (step_block_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | StackMemFlow op =>
      exact step_stackmemflow_present
        (op := op) (gasCost := gasCost) (arg := arg) hfind hstep
  | Push op =>
      exact present_of_accountMap_eq
        (step_push_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Dup op =>
      exact present_of_accountMap_eq
        (step_dup_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Exchange op =>
      exact present_of_accountMap_eq
        (step_exchange_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Log op =>
      exact present_of_accountMap_eq
        (step_log_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | System op =>
      exact step_system_present_max_depth
        (op := op) (gasCost := gasCost) (arg := arg) hdepth hfind hstep

private theorem step_account_present_succ_depth :
    ∀ gasCost instr state stateOut n,
      1024 - state.executionEnv.depth.val = n + 1 →
      (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
          (d : ByteArray) (H : BlockHeader) (w : Bool)
          (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
          (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o r c g p v vRep d e H w =
              (cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
          (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
          (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
          (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
          (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o g p v i e ζ H w =
              (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      step gasCost instr state = .ok stateOut →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro gasCost instr state stateOut n hdepth ihTheta ihLambda hstep addr acc hfind
  rcases instr with ⟨op, arg⟩
  cases op with
  | StopArith op =>
      exact present_of_accountMap_eq
        (step_stoparith_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | CompBit op =>
      exact present_of_accountMap_eq
        (step_compbit_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Keccak op =>
      exact present_of_accountMap_eq
        (step_keccak_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Env op =>
      exact present_of_accountMap_eq
        (step_env_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Block op =>
      exact present_of_accountMap_eq
        (step_block_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | StackMemFlow op =>
      exact step_stackmemflow_present
        (op := op) (gasCost := gasCost) (arg := arg) hfind hstep
  | Push op =>
      exact present_of_accountMap_eq
        (step_push_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Dup op =>
      exact present_of_accountMap_eq
        (step_dup_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Exchange op =>
      exact present_of_accountMap_eq
        (step_exchange_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | Log op =>
      exact present_of_accountMap_eq
        (step_log_accountMap_eq (op := op) (gasCost := gasCost) (arg := arg) hstep)
        hfind
  | System op =>
      exact step_system_present_succ_depth
        (op := op) (gasCost := gasCost) (arg := arg)
        hdepth ihTheta ihLambda hfind hstep

private theorem Z_accountMap_eq
    {validJumps : Array UInt256} {state : State} {op : Operation}
    {stateZ : State} {cost : Nat}
    (hZ : Z validJumps op state = .ok (stateZ, cost)) :
    stateZ.accountMap = state.accountMap := by
  unfold Z at hZ
  by_cases hδ : δ op = none
  · rw [if_pos hδ] at hZ
    contradiction
  rw [if_neg hδ] at hZ
  by_cases hstack : state.machineState.stack.length < (δ op).getD 0
  · rw [if_pos hstack] at hZ
    contradiction
  rw [if_neg hstack] at hZ
  by_cases hcost₁ : state.machineState.gasAvailable.toNat < memoryExpansionCost state op
  · rw [if_pos hcost₁] at hZ
    contradiction
  rw [if_neg hcost₁] at hZ
  set state₁ : State :=
    { state with machineState.gasAvailable :=
        state.machineState.gasAvailable.subNat (memoryExpansionCost state op) } with hstate₁
  by_cases hcost₂ : state₁.machineState.gasAvailable.toNat < C' state₁ op
  · rw [if_pos (by simpa [state₁] using hcost₂)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcost₂)] at hZ
  by_cases hjump :
      op = Operation.JUMP ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjump)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjump)] at hZ
  by_cases hjumpi :
      op = Operation.JUMPI ∧
        state₁.machineState.stack[1]? ≠ some (⟨0⟩ : UInt256) ∧
        Z.notIn state₁.machineState.stack[0]? validJumps = true
  · rw [if_pos (by simpa [state₁] using hjumpi)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hjumpi)] at hZ
  by_cases hreturndata :
      op = Operation.RETURNDATACOPY ∧
        (state₁.machineState.stack.getD 1 ⟨0⟩).toNat
          + (state₁.machineState.stack.getD 2 ⟨0⟩).toNat
            > state₁.machineState.returnData.size
  · rw [if_pos (by simpa [state₁] using hreturndata)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hreturndata)] at hZ
  by_cases hstackover :
      state₁.machineState.stack.length - (δ op).getD 0 + (α op).getD 0 > 1024
  · rw [if_pos (by simpa [state₁] using hstackover)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstackover)] at hZ
  by_cases hstatic :
      (¬ state₁.executionEnv.perm) ∧
        (op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3,
            .LOG4, .TSTORE] ∨
          (op = .CALL ∧ state₁.machineState.stack[2]? ≠ some ⟨0⟩))
  · rw [if_pos (by simpa [state₁] using hstatic)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hstatic)] at hZ
  by_cases hsstore :
      (op = .SSTORE) ∧ state₁.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
  · rw [if_pos (by simpa [state₁] using hsstore)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hsstore)] at hZ
  by_cases hcreate :
      op.isCreate ∧ state₁.machineState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  · rw [if_pos (by simpa [state₁] using hcreate)] at hZ
    contradiction
  rw [if_neg (by simpa [state₁] using hcreate)] at hZ
  simp at hZ
  rcases hZ with ⟨hstate, _hcost⟩
  simpa [state₁] using congrArg (fun st : State => st.accountMap) hstate.symm

private theorem Z_account_present
    {validJumps : Array UInt256} {state : State} {op : Operation}
    {stateZ : State} {cost : Nat} :
    Z validJumps op state = .ok (stateZ, cost) →
      PreservesPresent state.accountMap stateZ.accountMap := by
  intro hZ addr acc hfind
  exact present_of_accountMap_eq (Z_accountMap_eq hZ) hfind

private theorem Xstep_account_present_max_depth :
    ∀ {validJumps : Array UInt256} {state stateOut : State}
      {ret : Option (HaltCause × ByteArray)},
      state.executionEnv.depth = 1024 →
      Xstep validJumps state = .ok (stateOut, ret) →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro validJumps state stateOut ret hdepth hXstep addr acc hfind
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at hXstep
  split at hXstep
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at hXstep
    split at hXstep
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      rcases Z_account_present hZ' hfind with ⟨accZ, hfindZ⟩
      have hStepPres := step_account_present_max_depth
        cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth } stepped
        (by simp [hdepth]) hStep'
        (by simpa using hfindZ)
      repeat split at hXstep
      all_goals
        try contradiction
        try
          injection hXstep with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          simpa using hStepPres
        try
          split at hXstep
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hStepPres
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hStepPres

private theorem Xstep_account_present_succ_depth :
    ∀ {validJumps : Array UInt256} {state stateOut : State}
      {ret : Option (HaltCause × ByteArray)} {n : Nat},
      1024 - state.executionEnv.depth.val = n + 1 →
      (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
          (d : ByteArray) (H : BlockHeader) (w : Bool)
          (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
          (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o r c g p v vRep d e H w =
              (cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
          (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
          (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
          (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
          (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o g p v i e ζ H w =
              (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      Xstep validJumps state = .ok (stateOut, ret) →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro validJumps state stateOut ret n hdepth ihTheta ihLambda hXstep addr acc hfind
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  simp [Xstep, ← hinstr] at hXstep
  split at hXstep
  · contradiction
  · rename_i stateZ cost hZ
    simp [bind, Except.bind] at hXstep
    split at hXstep
    · contradiction
    · rename_i stepped hStep
      have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
        simpa [← hinstr] using hZ
      have hStep' :
          step cost (op, arg)
            { stateZ with executionEnv.depth := state.executionEnv.depth } = .ok stepped := by
        simpa [← hinstr] using hStep
      rcases Z_account_present hZ' hfind with ⟨accZ, hfindZ⟩
      have hStepPres := step_account_present_succ_depth
        cost (op, arg) { stateZ with executionEnv.depth := state.executionEnv.depth } stepped n
        (by simp [hdepth])
        ihTheta ihLambda hStep'
        (by simpa using hfindZ)
      repeat split at hXstep
      all_goals
        try contradiction
        try
          injection hXstep with hpair
          have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
            congrArg Prod.fst hpair
          rw [← hstateEq]
          simpa using hStepPres
        try
          split at hXstep
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hStepPres
          · injection hXstep with hpair
            have hstateEq : { stepped with executionEnv := state.executionEnv } = stateOut :=
              congrArg Prod.fst hpair
            rw [← hstateEq]
            simpa using hStepPres

private theorem X_account_present_max_depth :
    ∀ {fuel : Nat} {validJumps : Array UInt256} {state stateOut : State} {out : ByteArray},
      state.executionEnv.depth = 1024 →
      X fuel validJumps state = .ok (.success stateOut out) →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro fuel validJumps state stateOut out hdepth hX addr acc hfind
  induction fuel generalizing state stateOut out acc with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error err =>
          rw [hstep] at hX
          change Except.error err = Except.ok (ExecutionResult.success stateOut out) at hX
          contradiction
      | ok stepRes =>
          rcases stepRes with ⟨state₁, ret⟩
          have hstepPres := Xstep_account_present_max_depth hdepth hstep hfind
          rw [hstep] at hX
          cases ret with
          | none =>
              change X fuel validJumps
                  { state₁ with executionEnv.depth := state.executionEnv.depth } =
                Except.ok (ExecutionResult.success stateOut out) at hX
              rcases hstepPres with ⟨acc₁, hfind₁⟩
              exact ih
                (state := { state₁ with executionEnv.depth := state.executionEnv.depth })
                (stateOut := stateOut) (out := out) (acc := acc₁)
                (by simp [hdepth]) hX (by simpa using hfind₁)
          | some retVal =>
              rcases retVal with ⟨cause, data⟩
              cases cause with
              | success =>
                  change Except.ok (ExecutionResult.success state₁ data) =
                    Except.ok (ExecutionResult.success stateOut out) at hX
                  injection hX with hres
                  injection hres with hstate _hout
                  rw [← hstate]
                  exact hstepPres
              | revert =>
                  change Except.ok
                    (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 data) =
                      Except.ok (ExecutionResult.success stateOut out) at hX
                  injection hX with hres
                  cases hres

private theorem X_account_present_succ_depth :
    ∀ {fuel : Nat} {validJumps : Array UInt256} {state stateOut : State} {out : ByteArray}
      {n : Nat},
      1024 - state.executionEnv.depth.val = n + 1 →
      (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
          (d : ByteArray) (H : BlockHeader) (w : Bool)
          (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
          (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o r c g p v vRep d e H w =
              (cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
          (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
          (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
          (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
          (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
          (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
          (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
          (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
          (zOut : Bool) (out : ByteArray),
          1024 - e.val = n →
            Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                σ σ₀ A s o g p v i e ζ H w =
              (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
            PreservesPresent σ σOut) →
      X fuel validJumps state = .ok (.success stateOut out) →
      PreservesPresent state.accountMap stateOut.accountMap := by
  intro fuel validJumps state stateOut out n hdepth ihTheta ihLambda hX addr acc hfind
  induction fuel generalizing state stateOut out acc with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error err =>
          rw [hstep] at hX
          change Except.error err = Except.ok (ExecutionResult.success stateOut out) at hX
          contradiction
      | ok stepRes =>
          rcases stepRes with ⟨state₁, ret⟩
          have hstepPres := Xstep_account_present_succ_depth hdepth ihTheta ihLambda hstep hfind
          rw [hstep] at hX
          cases ret with
          | none =>
              change X fuel validJumps
                  { state₁ with executionEnv.depth := state.executionEnv.depth } =
                Except.ok (ExecutionResult.success stateOut out) at hX
              rcases hstepPres with ⟨acc₁, hfind₁⟩
              exact ih
                (state := { state₁ with executionEnv.depth := state.executionEnv.depth })
                (stateOut := stateOut) (out := out) (acc := acc₁)
                (by simp [hdepth]) hX (by simpa using hfind₁)
          | some retVal =>
              rcases retVal with ⟨cause, data⟩
              cases cause with
              | success =>
                  change Except.ok (ExecutionResult.success state₁ data) =
                    Except.ok (ExecutionResult.success stateOut out) at hX
                  injection hX with hres
                  injection hres with hstate _hout
                  rw [← hstate]
                  exact hstepPres
              | revert =>
                  change Except.ok
                    (ExecutionResult.revert state₁.machineState.gasAvailable.toUInt256 data) =
                      Except.ok (ExecutionResult.success stateOut out) at hX
                  injection hX with hres
                  cases hres

private theorem Xi_account_present_max_depth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {createdAccountsOut : Batteries.RBSet AccountAddress compare}
    {σOut : AccountMap} {gOut : UInt256} {AOut : Substate} {out : ByteArray}
    (hdepth : I.depth = 1024)
    (hXi : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccountsOut, σOut, gOut, AOut) out)) :
    PreservesPresent σ σOut := by
  intro addr acc hfind
  simp [Ξ] at hXi
  set freshState : State :=
    { (default : State) with
      accountMap := σ,
      σ₀ := σ₀,
      executionEnv := I,
      substate := A,
      createdAccounts := createdAccounts,
      machineState := { (default : State).machineState with gasAvailable := Sat256.ofUInt256 g },
      blocks := blocks,
      genesisBlockHeader := genesisBlockHeader } with hfresh
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) freshState)
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (createdAccountsOut, σOut, gOut, AOut) out) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) freshState with
  | error err =>
      simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas data =>
          simp [hX, Except.bind] at hXi
      | success evmState' data =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hcreated, hσ, hg, hA⟩, hout⟩
          rw [← hσ]
          have hloc : PreservesPresent freshState.accountMap evmState'.accountMap :=
            X_account_present_max_depth
            (fuel := g.toNat + 1) (validJumps := D_J I.code 0)
            (state := freshState) (stateOut := evmState') (out := data)
            (by simpa [hfresh] using hdepth)
            hX
          exact hloc (by simpa [hfresh] using hfind)

private theorem Xi_account_present_succ_depth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {createdAccountsOut : Batteries.RBSet AccountAddress compare}
    {σOut : AccountMap} {gOut : UInt256} {AOut : Substate} {out : ByteArray} {n : Nat}
    (hdepth : 1024 - I.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o r : AccountAddress) (c : ToExecute) (g p v vRep : UInt256)
        (d : ByteArray) (H : BlockHeader) (w : Bool)
        (cAOut : Batteries.RBSet AccountAddress compare) (σOut : AccountMap)
        (gOut : UInt256) (AOut : Substate) (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v vRep d e H w =
            (cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (ihLambda : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
        (e : Fin 1025) (σ σ₀ : AccountMap) (A : Substate)
        (s o : AccountAddress) (g p v : UInt256) (i : ByteArray)
        (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
        (aOut : AccountAddress) (cAOut : Batteries.RBSet AccountAddress compare)
        (σOut : AccountMap) (gOut : UInt256) (AOut : Substate)
        (zOut : Bool) (out : ByteArray),
        1024 - e.val = n →
          Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o g p v i e ζ H w =
            (aOut, cAOut, σOut, gOut, AOut, zOut, out) →
          PreservesPresent σ σOut)
    (hXi : Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccountsOut, σOut, gOut, AOut) out)) :
    PreservesPresent σ σOut := by
  intro addr acc hfind
  simp [Ξ] at hXi
  set freshState : State :=
    { (default : State) with
      accountMap := σ,
      σ₀ := σ₀,
      executionEnv := I,
      substate := A,
      createdAccounts := createdAccounts,
      machineState := { (default : State).machineState with gasAvailable := Sat256.ofUInt256 g },
      blocks := blocks,
      genesisBlockHeader := genesisBlockHeader } with hfresh
  change Except.bind (X (g.toNat + 1) (D_J I.code 0) freshState)
      (fun result =>
        match result with
        | ExecutionResult.success evmState' o =>
            Except.ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
                evmState'.machineState.gasAvailable.toUInt256, evmState'.substate) o)
        | ExecutionResult.revert g' o => Except.ok (ExecutionResult.revert g' o)) =
        Except.ok (ExecutionResult.success (createdAccountsOut, σOut, gOut, AOut) out) at hXi
  cases hX : X (g.toNat + 1) (D_J I.code 0) freshState with
  | error err =>
      simp [hX, Except.bind] at hXi
  | ok res =>
      cases res with
      | revert gas data =>
          simp [hX, Except.bind] at hXi
      | success evmState' data =>
          simp [hX, Except.bind] at hXi
          rcases hXi with ⟨⟨hcreated, hσ, hg, hA⟩, hout⟩
          rw [← hσ]
          have hloc : PreservesPresent freshState.accountMap evmState'.accountMap :=
            X_account_present_succ_depth
            (fuel := g.toNat + 1) (validJumps := D_J I.code 0)
            (state := freshState) (stateOut := evmState') (out := data) (n := n)
            (by simpa [hfresh] using hdepth)
            (by simpa [hfresh] using ihTheta)
            (by simpa [hfresh] using ihLambda)
            hX
          exact hloc (by simpa [hfresh] using hfind)

private lemma precompile_ECREC_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).1 = ∅ ∨ (Ξ_ECREC σ g A I).1 = σ := by
  simp only [Ξ_ECREC]
  split <;> simp

private lemma precompile_SHA256_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).1 = ∅ ∨ (Ξ_SHA256 σ g A I).1 = σ := by
  simp only [Ξ_SHA256]
  split <;> simp

private lemma precompile_RIP160_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).1 = ∅ ∨ (Ξ_RIP160 σ g A I).1 = σ := by
  simp only [Ξ_RIP160]
  split <;> simp

private lemma precompile_ID_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ID σ g A I).1 = ∅ ∨ (Ξ_ID σ g A I).1 = σ := by
  simp only [Ξ_ID]
  split <;> simp

private lemma precompile_EXPMOD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_EXPMOD σ g A I).1 = ∅ ∨ (Ξ_EXPMOD σ g A I).1 = σ := by
  unfold Ξ_EXPMOD
  set data := I.calldata
  set base_length := nat_of_slice data 0 32
  set exp_length := nat_of_slice data 32 32
  set modulus_length := nat_of_slice data 64 32
  set exp := fun _ : Unit => nat_of_slice data (96 + base_length) exp_length
  set gᵣ :=
    (let multiplication_complexity := fun x y => ((max x y + 7) / 8) ^ 2
     let adjusted_exp_length :=
      if exp_length ≤ 32 && exp () == 0 then
        0
      else if exp_length ≤ 32 then
        Nat.log 2 (exp ())
      else
        let length_part := 8 * (exp_length - 32)
        let bits_part :=
          let exp_head := nat_of_slice data (96 + base_length) 32
          if 32 < exp_length ∧ exp_head != 0 then Nat.log 2 exp_head else 0
        length_part + bits_part
     let iterations := max adjusted_exp_length 1
     let G_quaddivisor := 3
     max 200 (multiplication_complexity base_length modulus_length * iterations / G_quaddivisor))
  simp only
  repeat' (first | split | simp)

private lemma precompile_BN_ADD_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).1 = ∅ ∨ (Ξ_BN_ADD σ g A I).1 = σ := by
  simp only [Ξ_BN_ADD]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_BN_MUL_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).1 = ∅ ∨ (Ξ_BN_MUL σ g A I).1 = σ := by
  simp only [Ξ_BN_MUL]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_SNARKV_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).1 = ∅ ∨ (Ξ_SNARKV σ g A I).1 = σ := by
  simp only [Ξ_SNARKV]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_BLAKE2_F_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).1 = ∅ ∨ (Ξ_BLAKE2_F σ g A I).1 = σ := by
  simp only [Ξ_BLAKE2_F]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompile_PointEval_accountMap_empty_or_self
    (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).1 = ∅ ∨ (Ξ_PointEval σ g A I).1 = σ := by
  simp only [Ξ_PointEval]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

private lemma precompiled_Theta_accountMap_eq
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader)
    (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap)
    (A : Substate)
    (s o r pc : AccountAddress)
    (g p v v' : UInt256)
    (d : ByteArray)
    (e : Fin 1025)
    (H : BlockHeader)
    (w : Bool) :
    (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.1 =
      (let σ₁ := sendEth r s v true σ
       let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
       let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 ×
          Substate × ByteArray :=
        match pc with
        | 1 => (∅, Ξ_ECREC σ₁ g A I)
        | 2 => (∅, Ξ_SHA256 σ₁ g A I)
        | 3 => (∅, Ξ_RIP160 σ₁ g A I)
        | 4 => (∅, Ξ_ID σ₁ g A I)
        | 5 => (∅, Ξ_EXPMOD σ₁ g A I)
        | 6 => (∅, Ξ_BN_ADD σ₁ g A I)
        | 7 => (∅, Ξ_BN_MUL σ₁ g A I)
        | 8 => (∅, Ξ_SNARKV σ₁ g A I)
        | 9 => (∅, Ξ_BLAKE2_F σ₁ g A I)
        | 10 => (∅, Ξ_PointEval σ₁ g A I)
        | _ => default
       if result.2.1 == ∅ then σ else result.2.1) := by
  unfold Θ sendEth
  simp
  rfl

private lemma precompiled_result_accountMap_empty_or_self
    (pc : AccountAddress) (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 ×
        Substate × ByteArray :=
      match pc with
      | 1 => (∅, Ξ_ECREC σ g A I)
      | 2 => (∅, Ξ_SHA256 σ g A I)
      | 3 => (∅, Ξ_RIP160 σ g A I)
      | 4 => (∅, Ξ_ID σ g A I)
      | 5 => (∅, Ξ_EXPMOD σ g A I)
      | 6 => (∅, Ξ_BN_ADD σ g A I)
      | 7 => (∅, Ξ_BN_MUL σ g A I)
      | 8 => (∅, Ξ_SNARKV σ g A I)
      | 9 => (∅, Ξ_BLAKE2_F σ g A I)
      | 10 => (∅, Ξ_PointEval σ g A I)
      | _ => default
     result.2.1) = ∅ ∨
    (let result : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 ×
        Substate × ByteArray :=
      match pc with
      | 1 => (∅, Ξ_ECREC σ g A I)
      | 2 => (∅, Ξ_SHA256 σ g A I)
      | 3 => (∅, Ξ_RIP160 σ g A I)
      | 4 => (∅, Ξ_ID σ g A I)
      | 5 => (∅, Ξ_EXPMOD σ g A I)
      | 6 => (∅, Ξ_BN_ADD σ g A I)
      | 7 => (∅, Ξ_BN_MUL σ g A I)
      | 8 => (∅, Ξ_SNARKV σ g A I)
      | 9 => (∅, Ξ_BLAKE2_F σ g A I)
      | 10 => (∅, Ξ_PointEval σ g A I)
      | _ => default
     result.2.1) = σ := by
  repeat split
  all_goals
    dsimp
    first
    | exact precompile_ECREC_accountMap_empty_or_self σ g A I
    | exact precompile_SHA256_accountMap_empty_or_self σ g A I
    | exact precompile_RIP160_accountMap_empty_or_self σ g A I
    | exact precompile_ID_accountMap_empty_or_self σ g A I
    | exact precompile_EXPMOD_accountMap_empty_or_self σ g A I
    | exact precompile_BN_ADD_accountMap_empty_or_self σ g A I
    | exact precompile_BN_MUL_accountMap_empty_or_self σ g A I
    | exact precompile_SNARKV_accountMap_empty_or_self σ g A I
    | exact precompile_BLAKE2_F_accountMap_empty_or_self σ g A I
    | exact precompile_PointEval_accountMap_empty_or_self σ g A I
    | exact Or.inl rfl

private theorem precompiled_Theta_present
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r pc : AccountAddress}
    {g p v v' : UInt256} {d : ByteArray} {e : Fin 1025} {H : BlockHeader}
    {w : Bool} {createdAccountsOut : Batteries.RBSet AccountAddress compare}
    {σOut : AccountMap} {gOut : UInt256} {AOut : Substate} {zOut : Bool}
    {out : ByteArray}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccountsOut, σOut, gOut, AOut, zOut, out)) :
    PreservesPresent σ σOut := by
  intro addr acc hfind
  have hσ_proj := congrArg (fun x => x.2.1) hTheta
  have hσ : (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
      (.Precompiled pc) g p v v' d e H w).2.1 = σOut := by
    simpa using hσ_proj
  rw [← hσ]
  rw [precompiled_Theta_accountMap_eq]
  let σ₁ := sendEth r s v true σ
  have hpre : ∃ acc', σ₁.find? addr = some acc' := by
    simpa [σ₁] using sendEth_present (r := r) (s := s) (v := v) (z := true) hfind
  exact present_if_empty_or_self (self := σ₁) hfind hpre
    (by
      let I : ExecutionEnv :=
        { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
          code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
          blobVersionedHashes := blobVersionedHashes }
      simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)

private theorem account_present_of_Theta_and_Lambda
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {g p v v' : UInt256} {d i : ByteArray} {ζ : Option ByteArray}
    {H : BlockHeader} {w : Bool} :
    ∀ a c createdAccountsOut σOut gOut AOut zOut out e,
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
          g p v v' d e H w =
        (createdAccountsOut, σOut, gOut, AOut, zOut, out) →
        PreservesPresent σ σOut) ∧
      (Lambda blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o
          g p v i e ζ H w =
        (a, createdAccountsOut, σOut, gOut, AOut, zOut, out) →
        PreservesPresent σ σOut) := by
  intros a c createdAccountsOut σOut gOut AOut zOut out e
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes genesisBlockHeader blocks createdAccounts e σ σ₀ A
      s o r c g p v v' d i ζ H w createdAccountsOut σOut AOut gOut zOut out a with
  | zero =>
      have he_eq : e = 1024 := by omega
      subst e
      constructor
      · intro hTheta addr acc hfind
        cases hc : c with
        | Precompiled pc =>
            exact precompiled_Theta_present
              (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
              (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
              (pc := pc) (g := g) (p := p) (v := v) (v' := v') (d := d)
              (e := 1024) (H := H) (w := w)
              (createdAccountsOut := createdAccountsOut) (σOut := σOut) (gOut := gOut)
              (AOut := AOut) (zOut := zOut) (out := out)
              (by simpa [hc] using hTheta) hfind
        | Code code =>
            unfold Θ at hTheta
            simp [hc] at hTheta
            split at hTheta <;> rename_i hXi
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact ⟨acc, hfind⟩
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact ⟨acc, hfind⟩
            · rename_i createdAccountsXi σXi gXi AXi returnedData
              simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              split_ifs at hσ with hempty
              · rw [← hσ]
                exact ⟨acc, hfind⟩
              · rw [← hσ]
                rcases sendEth_present (r := r) (s := s) (v := v) (z := true) hfind with
                  ⟨acc₁, hpre⟩
                have hXiPres : PreservesPresent _ σXi :=
                  Xi_account_present_max_depth (hdepth := by simp) hXi
                exact hXiPres (by simpa [sendEth] using hpre)
      · intro hLambda addr acc hfind
        unfold Lambda at hLambda
        simp at hLambda
        split at hLambda <;> rename_i hXi
        · simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          rw [← hσ]
          exact ⟨acc, hfind⟩
        · simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          rw [← hσ]
          exact ⟨acc, hfind⟩
        · rename_i createdAccountsLocal createdAccountsXi σXi gXi AXi returnedData
          simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          split_ifs at hσ with hfinal
          · rw [← hσ]
            exact ⟨acc, hfind⟩
          · rw [← hσ]
            rcases sendEthCreate_present (a := a) (s := s) (v := v) (z := true) hfind with
              ⟨acc₁, hpre⟩
            have hXiPres : PreservesPresent _ σXi :=
              Xi_account_present_max_depth (hdepth := by simp) hXi
            rcases hXiPres (by simpa [sendEthCreate, ← ha] using hpre) with
              ⟨acc₂, hσXi⟩
            exact accountMap_insert_present hσXi
  | succ n ih =>
      constructor
      · intro hTheta addr acc hfind
        cases hc : c with
        | Precompiled pc =>
            exact precompiled_Theta_present
              (blobVersionedHashes := blobVersionedHashes) (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
              (σ := σ) (σ₀ := σ₀) (A := A) (s := s) (o := o) (r := r)
              (pc := pc) (g := g) (p := p) (v := v) (v' := v') (d := d)
              (e := e) (H := H) (w := w)
              (createdAccountsOut := createdAccountsOut) (σOut := σOut) (gOut := gOut)
              (AOut := AOut) (zOut := zOut) (out := out)
              (by simpa [hc] using hTheta) hfind
        | Code code =>
            unfold Θ at hTheta
            simp [hc] at hTheta
            split at hTheta <;> rename_i hXi
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact ⟨acc, hfind⟩
            · simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              rw [← hσ]
              exact ⟨acc, hfind⟩
            · rename_i createdAccountsXi σXi gXi AXi returnedData
              simp at hTheta
              rcases hTheta with ⟨hcreated, hσ, hg, hA, hz, ho⟩
              split_ifs at hσ with hempty
              · rw [← hσ]
                exact ⟨acc, hfind⟩
              · rw [← hσ]
                rcases sendEth_present (r := r) (s := s) (v := v) (z := true) hfind with
                  ⟨acc₁, hpre⟩
                have hThetaRec : ∀ (blobVersionedHashesᵢ : List ByteArray)
                    (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
                    (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
                    (eᵢ : Fin 1025) (σᵢ σ₀ᵢ : AccountMap) (Aᵢ : Substate)
                    (sᵢ oᵢ rᵢ : AccountAddress) (cᵢ : ToExecute)
                    (gᵢ pᵢ vᵢ vRepᵢ : UInt256) (dᵢ : ByteArray)
                    (Hᵢ : BlockHeader) (wᵢ : Bool)
                    (cAOutᵢ : Batteries.RBSet AccountAddress compare) (σOutᵢ : AccountMap)
                    (gOutᵢ : UInt256) (AOutᵢ : Substate) (zOutᵢ : Bool)
                    (outᵢ : ByteArray),
                    1024 - eᵢ.val = n →
                      Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                          σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ vRepᵢ dᵢ eᵢ Hᵢ wᵢ =
                        (cAOutᵢ, σOutᵢ, gOutᵢ, AOutᵢ, zOutᵢ, outᵢ) →
                      PreservesPresent σᵢ σOutᵢ := by
                  intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ createdAccountsᵢ
                    eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ vRepᵢ dᵢ Hᵢ wᵢ
                    cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ heᵢ hThetaᵢ
                  exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                    (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ) (g := gᵢ) (p := pᵢ)
                    (v := vᵢ) (v' := vRepᵢ) (d := dᵢ) (i := default) (ζ := none)
                    (H := Hᵢ) (w := wᵢ)
                    default cᵢ cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ eᵢ heᵢ).1 hThetaᵢ
                have hLambdaRec : ∀ (blobVersionedHashesᵢ : List ByteArray)
                    (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
                    (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
                    (eᵢ : Fin 1025) (σᵢ σ₀ᵢ : AccountMap) (Aᵢ : Substate)
                    (sᵢ oᵢ : AccountAddress) (gᵢ pᵢ vᵢ : UInt256)
                    (iᵢ : ByteArray) (ζᵢ : Option ByteArray) (Hᵢ : BlockHeader) (wᵢ : Bool)
                    (aOutᵢ : AccountAddress) (cAOutᵢ : Batteries.RBSet AccountAddress compare)
                    (σOutᵢ : AccountMap) (gOutᵢ : UInt256) (AOutᵢ : Substate)
                    (zOutᵢ : Bool) (outᵢ : ByteArray),
                    1024 - eᵢ.val = n →
                      Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                          σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ eᵢ ζᵢ Hᵢ wᵢ =
                        (aOutᵢ, cAOutᵢ, σOutᵢ, gOutᵢ, AOutᵢ, zOutᵢ, outᵢ) →
                      PreservesPresent σᵢ σOutᵢ := by
                  intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ createdAccountsᵢ
                    eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ ζᵢ Hᵢ wᵢ
                    aOutᵢ cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ heᵢ hLambdaᵢ
                  exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                    (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default) (g := gᵢ) (p := pᵢ)
                    (v := vᵢ) (v' := default) (d := default) (i := iᵢ) (ζ := ζᵢ)
                    (H := Hᵢ) (w := wᵢ)
                    aOutᵢ (toExecute σᵢ default) cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ
                    eᵢ heᵢ).2 hLambdaᵢ
                have hXiPres : PreservesPresent _ σXi :=
                  Xi_account_present_succ_depth
                    (n := n) (hdepth := by simpa using hn)
                    hThetaRec hLambdaRec hXi
                exact hXiPres (by simpa [sendEth] using hpre)
      · intro hLambda addr acc hfind
        unfold Lambda at hLambda
        simp at hLambda
        split at hLambda <;> rename_i hXi
        · simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          rw [← hσ]
          exact ⟨acc, hfind⟩
        · simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          rw [← hσ]
          exact ⟨acc, hfind⟩
        · rename_i createdAccountsLocal createdAccountsXi σXi gXi AXi returnedData
          simp at hLambda
          rcases hLambda with ⟨ha, hcreated, hσ, hg, hA, hz, ho⟩
          split_ifs at hσ with hfinal
          · rw [← hσ]
            exact ⟨acc, hfind⟩
          · rw [← hσ]
            rcases sendEthCreate_present (a := a) (s := s) (v := v) (z := true) hfind with
              ⟨acc₁, hpre⟩
            have hThetaRec : ∀ (blobVersionedHashesᵢ : List ByteArray)
                (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
                (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
                (eᵢ : Fin 1025) (σᵢ σ₀ᵢ : AccountMap) (Aᵢ : Substate)
                (sᵢ oᵢ rᵢ : AccountAddress) (cᵢ : ToExecute)
                (gᵢ pᵢ vᵢ vRepᵢ : UInt256) (dᵢ : ByteArray)
                (Hᵢ : BlockHeader) (wᵢ : Bool)
                (cAOutᵢ : Batteries.RBSet AccountAddress compare) (σOutᵢ : AccountMap)
                (gOutᵢ : UInt256) (AOutᵢ : Substate) (zOutᵢ : Bool)
                (outᵢ : ByteArray),
                1024 - eᵢ.val = n →
                  Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                      σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ vRepᵢ dᵢ eᵢ Hᵢ wᵢ =
                    (cAOutᵢ, σOutᵢ, gOutᵢ, AOutᵢ, zOutᵢ, outᵢ) →
                  PreservesPresent σᵢ σOutᵢ := by
              intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ createdAccountsᵢ
                eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ vRepᵢ dᵢ Hᵢ wᵢ
                cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ heᵢ hThetaᵢ
              exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := rᵢ) (g := gᵢ) (p := pᵢ)
                (v := vᵢ) (v' := vRepᵢ) (d := dᵢ) (i := default) (ζ := none)
                (H := Hᵢ) (w := wᵢ)
                default cᵢ cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ eᵢ heᵢ).1 hThetaᵢ
            have hLambdaRec : ∀ (blobVersionedHashesᵢ : List ByteArray)
                (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
                (createdAccountsᵢ : Batteries.RBSet AccountAddress compare)
                (eᵢ : Fin 1025) (σᵢ σ₀ᵢ : AccountMap) (Aᵢ : Substate)
                (sᵢ oᵢ : AccountAddress) (gᵢ pᵢ vᵢ : UInt256)
                (iᵢ : ByteArray) (ζᵢ : Option ByteArray) (Hᵢ : BlockHeader) (wᵢ : Bool)
                (aOutᵢ : AccountAddress) (cAOutᵢ : Batteries.RBSet AccountAddress compare)
                (σOutᵢ : AccountMap) (gOutᵢ : UInt256) (AOutᵢ : Substate)
                (zOutᵢ : Bool) (outᵢ : ByteArray),
                1024 - eᵢ.val = n →
                  Lambda blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
                      σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ eᵢ ζᵢ Hᵢ wᵢ =
                    (aOutᵢ, cAOutᵢ, σOutᵢ, gOutᵢ, AOutᵢ, zOutᵢ, outᵢ) →
                  PreservesPresent σᵢ σOutᵢ := by
              intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ createdAccountsᵢ
                eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ gᵢ pᵢ vᵢ iᵢ ζᵢ Hᵢ wᵢ
                aOutᵢ cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ heᵢ hLambdaᵢ
              exact (ih (blobVersionedHashes := blobVersionedHashesᵢ)
                (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                (createdAccounts := createdAccountsᵢ) (σ := σᵢ) (σ₀ := σ₀ᵢ)
                (A := Aᵢ) (s := sᵢ) (o := oᵢ) (r := default) (g := gᵢ) (p := pᵢ)
                (v := vᵢ) (v' := default) (d := default) (i := iᵢ) (ζ := ζᵢ)
                (H := Hᵢ) (w := wᵢ)
                aOutᵢ (toExecute σᵢ default) cAOutᵢ σOutᵢ gOutᵢ AOutᵢ zOutᵢ outᵢ
                eᵢ heᵢ).2 hLambdaᵢ
            have hXiPres : PreservesPresent _ σXi :=
              Xi_account_present_succ_depth
                (n := n) (hdepth := by simpa using hn)
                hThetaRec hLambdaRec hXi
            rcases hXiPres (by simpa [sendEthCreate, ← ha] using hpre) with
              ⟨acc₂, hσXi⟩
            exact accountMap_insert_present hσXi

private theorem theta_account_present
    {blobVersionedHashes : List ByteArray}
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {s o r : AccountAddress}
    {c : ToExecute} {g p v v' : UInt256} {d : ByteArray}
    {e : Fin 1025} {H : BlockHeader} {w : Bool}
    {createdAccountsOut : Batteries.RBSet AccountAddress compare}
    {σOut : AccountMap} {gOut : UInt256} {AOut : Substate} {zOut : Bool}
    {out : ByteArray}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H w =
      (createdAccountsOut, σOut, gOut, AOut, zOut, out)) :
    PreservesPresent σ σOut :=
  (account_present_of_Theta_and_Lambda
    (i := default) (ζ := none) (a := default) (c := c)
    (createdAccountsOut := createdAccountsOut) (σOut := σOut)
    (gOut := gOut) (AOut := AOut) (zOut := zOut) (out := out) (e := e)).1 hTheta

theorem typedCallViaEVM_success_preserves_codeOwner_present {cfg : Config}
    {evm evm' : EVM.State} {target : EVM.Address} {name : Ident}
    {args : List Value} {out : ByteArray} {acc : Account}
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcall : typedCallViaEVM cfg evm target name 0 args (true, evm', out)) :
    ∃ acc', evm'.accountMap.find? evm'.executionEnv.codeOwner = some acc' := by
  obtain ⟨calldata, _hencode, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' _hvalueOK _hdepth =>
      rcases hTheta with ⟨callGas, A_in, hΘ⟩
      have hfound := theta_account_present hΘ.symm hacc
      rw [hevm']
      simpa using hfound

end Benchmarks.Dss.End
