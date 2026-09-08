import Reasoning.Reach
import Reasoning.SolmBody

/-! Static-mode terminals and Solm event/storage sequencing. -/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

theorem execBlock_append_event {cfg : Config} {body : List Stmt} {f e f' e'}
    (h : ExecBlock cfg f e body (.ok f' e')) (hp : e'.executionEnv.perm = true) :
    ExecBlock cfg f e (body ++ [.event]) (.ok f' e') :=
  execBlock_append h (.consNormal (.event hp) .nil)

theorem execBlock_append_event_static {cfg : Config} {body : List Stmt} {f e f' e'}
    (h : ExecBlock cfg f e body (.ok f' e')) (hp : e'.executionEnv.perm = false) :
    ExecBlock cfg f e (body ++ [.event]) .reverted :=
  execBlock_append h (.consRevert (.eventRevert hp))

theorem assignStorageRef_storage_scalar_static
    {cfg : Config} {solm : Frame} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc}
    {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hp : evm.executionEnv.perm = false) :
    assignStorageRef? cfg solm evm .storage slot value = .revert := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind,
    EvalResult.ofOption, hloc, pure]
  cases value <;> simp_all [storageStoreResultToEval, storageLocStore]
  all_goals rfl

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

/-- A prohibited state change terminates with a static-mode violation, or earlier out of gas. -/
def RDstatic (code : ByteArray) (g : Sat256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
  X (g.toNat + 1) (D_J code 0) s0 = .error .StaticModeViolation

private theorem RD.staticTerminal {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
      s.machineState.stack = stk → s.executionEnv = ee →
      Xstep (D_J code 0) s = .error .OutOfGass ∨
      Xstep (D_J code 0) s = .error .StaticModeViolation) :
    RDstatic code g s0 := by
  rcases h with ho | ⟨s, hx, hc, hpc, hs, _hg, hk, hC, _hm, _ha, _hr, _hacc, he, _hw⟩
  · exact Or.inl ho
  · have hf : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    rcases hstep s hc hpc hs he with ho | hp
    · left
      exact hx.trans (by rw [hf]; exact Xstep_X_X_except _ _ _ _ ho)
    · right
      exact hx.trans (by rw [hf]; exact Xstep_X_X_except _ _ _ _ hp)

theorem RD.sstoreStatic {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {slot val : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: val :: t) mem aw rdata acc k C)
    (hp : ee.perm = false) (hd : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) : RDstatic code g s0 := by
  apply h.staticTerminal
  intro s hc hpc hs he
  have hd' : decode s.executionEnv.code s.machineState.pc = some (.SSTORE, .none) := by
    rw [hc, hpc]; exact hd
  have hp' : s.executionEnv.perm = false := by rw [he]; exact hp
  rw [← hc, step_sstore s hd', hs]
  by_cases hg : s.machineState.gasAvailable.toNat < Csstore s <;> simp [hg, hp', Nat.not_lt_of_ge hov]

theorem RD.log2Static {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c d : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hp : ee.perm = false) (hd : decode code pc = some (.LOG2, .none))
    (hov : t.length ≤ 1024) : RDstatic code g s0 := by
  apply h.staticTerminal
  intro s hc hpc hs he
  have hd' : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hc, hpc]; exact hd
  have hp' : s.executionEnv.perm = false := by rw [he]; exact hp
  rw [← hc, step_log2 s hd', hs]
  by_cases hm : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2
  · simp [hm]
  · by_cases hg : s.machineState.gasAvailable.toNat - memoryExpansionCost s .LOG2 <
        GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic
    all_goals simp [hm, hg, hp', Nat.not_lt_of_ge hov]

theorem RD.log3Static {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hp : ee.perm = false) (hd : decode code pc = some (.LOG3, .none))
    (hov : t.length ≤ 1024) : RDstatic code g s0 := by
  apply h.staticTerminal
  intro s hc hpc hs he
  have hd' : decode s.executionEnv.code s.machineState.pc = some (.LOG3, .none) := by
    rw [hc, hpc]; exact hd
  have hp' : s.executionEnv.perm = false := by rw [he]; exact hp
  rw [← hc, step_log3 s hd', hs]
  by_cases hm : s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG3
  · simp [hm]
  · by_cases hg : s.machineState.gasAvailable.toNat - memoryExpansionCost s .LOG3 <
        GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic
    all_goals simp [hm, hg, hp', Nat.not_lt_of_ge hov]

theorem RDstatic.reEquivExecution {cfg contract cA gh bl σ_evm σ_solm σ₀ A I}
    {code : ByteArray} {g : UInt256} {t callargs}
    (h : RDstatic code (.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (.ofUInt256 g) A I))
    (hc : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
      (initState cA gh bl σ_solm σ₀ (.ofUInt256 g) A I) callargs t.body .reverted)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases h with ho | hs
  · exact .outOfGas (Xi_error_of_X (g := g) (by simpa [hc] using ho))
  · exact reEquiv_execution hd hdec hbody
      (.staticModeViolation (Xi_error_of_X (g := g) (by simpa [hc] using hs)) rfl)
      hfallback hreceive

end Reasoning.Reach
