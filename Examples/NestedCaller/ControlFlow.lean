import Examples.NestedCaller.Blocks
import Examples.NestedCaller.Spec
import Reasoning.CallRefinement

/-! Control-flow proofs using the generated summaries. The memory predicate is
parametric here: arithmetic and control flow preserve it, while the call decoder
must establish it for the next iteration. -/
namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory Reasoning.Refinement
open nestedCallerBlocks

set_option maxRecDepth 10000

abbrev wordValue (w : UInt256) : Value := .int (Int.ofNat w.toNat)

def loopStack (target count i last : UInt256) (rest : List UInt256) : List UInt256 :=
  [i, last, ⟨0⟩, count, target, ⟨71⟩] ++ rest

structure LoopLocals (f : Frame) (target : AccountAddress) (count i last : UInt256) : Prop where
  contract : f.contract = nestedCallerContract
  target : f.locals.get? "target" = some (.address target)
  count : f.locals.get? "count" = some (wordValue count)
  index : f.locals.get? "i" = some (wordValue i)
  last : f.locals.get? "last" = some (wordValue last)

theorem LoopLocals.insertValue {f target count i last} (h : LoopLocals f target count i last)
    (w : UInt256) : LoopLocals {f with locals := f.locals.insert "value" (wordValue w)} target count i last := by
  rcases h with ⟨hc, ht, hn, hi, hl⟩
  exact ⟨hc, by simpa only [store_get_ne (k := "value") (a := "target") _ _ (by decide)] using ht, by simpa only [store_get_ne (k := "value") (a := "count") _ _ (by decide)] using hn, by simpa only [store_get_ne (k := "value") (a := "i") _ _ (by decide)] using hi, by simpa only [store_get_ne (k := "value") (a := "last") _ _ (by decide)] using hl⟩

theorem LoopLocals.insertLast {f target count i last} (h : LoopLocals f target count i last)
    (w : UInt256) : LoopLocals {f with locals := f.locals.insert "last" (wordValue w)} target count i w := by
  rcases h with ⟨hc, ht, hn, hi, hl⟩
  exact ⟨hc, by simpa only [store_get_ne (k := "last") (a := "target") _ _ (by decide)] using ht, by simpa only [store_get_ne (k := "last") (a := "count") _ _ (by decide)] using hn, by simpa only [store_get_ne (k := "last") (a := "i") _ _ (by decide)] using hi, by simp⟩

theorem LoopLocals.insertIndex {f target count i last} (h : LoopLocals f target count i last)
    (w : UInt256) : LoopLocals {f with locals := f.locals.insert "i" (wordValue w)} target count w last := by
  rcases h with ⟨hc, ht, hn, hi, hl⟩
  exact ⟨hc, by simpa only [store_get_ne (k := "i") (a := "target") _ _ (by decide)] using ht, by simpa only [store_get_ne (k := "i") (a := "count") _ _ (by decide)] using hn, by simp, by simpa only [store_get_ne (k := "i") (a := "last") _ _ (by decide)] using hl⟩

def LoopAt (M : ℕ → ByteArray → UInt256 → Prop) (s0 : State) (ee : ExecutionEnv)
    (target : AccountAddress) (targetWord count : UInt256) (rest : List UInt256) : StateRel :=
  fun cur f e => ∃ i last, i.toNat ≤ count.toNat ∧ cur.stack = loopStack targetWord count i last rest ∧
    LoopLocals f target count i last ∧ M (i.toNat + 1) cur.mem cur.aw ∧ CallStateRel s0 ee cur.world e

def LoopInv (M : ℕ → ByteArray → UInt256 → Prop) (s0 : State) (ee : ExecutionEnv)
    (target : AccountAddress) (targetWord count : UInt256) (rest : List UInt256) (v : ℕ) : StateRel :=
  fun cur f e => ∃ i last, i.toNat + v = count.toNat ∧
    cur.stack = loopStack targetWord count i last rest ∧
    LoopLocals f target count i last ∧ M i.toNat cur.mem cur.aw ∧ CallStateRel s0 ee cur.world e

private theorem evalLt {cfg f e count i last target}
    (h : LoopLocals f target count i last) :
    evalExpr? cfg f e (.binary .lt (.var "i") (.var "count")) =
      .ok (.bool (i.toNat < count.toNat)) := by
  simp only [evalExpr?, h.index, h.count, EvalResult.ofOption, bind, EvalResult.bind,
    evalBinaryOp?, wordValue]
  congr 3
  change ((i.toNat : Int) < (count.toNat : Int)) = (i.toNat < count.toNat)
  simp

private theorem evalValueEq {cfg f e w} (h : f.locals.get? "value" = some (wordValue w)) (n : ℤ) :
    evalExpr? cfg f e (.binary .eq (.var "value") (.intLit n)) =
      .ok (.bool ((w.toNat : ℤ) == n)) := by
  simp only [evalExpr?, h, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?, wordValue]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq]
  rfl

/-- The post increments only the index. Its bound follows from the loop variant,
so the source integer and EVM word increments agree without wraparound. -/
theorem loopPostProgress {ee g s0 f e k C M target targetWord count rest v i last} {cur : Cursor}
    (hpc : cur.pc = ⟨169⟩) (hs : cur.stack = loopStack targetWord count i last rest)
    (hlen : rest.length + 9 ≤ 1024) (hv : i.toNat + (v + 1) = count.toNat)
    (hl : LoopLocals f target count i last) (hm : M (i.toNat + 1) cur.mem cur.aw)
    (hw : CallStateRel s0 ee cur.world e)
    (rd : RD nestedCallerBytecode ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C) :
    ∃ f', ∃ (next : Cursor), ∃ k' C', ExecBlock nestedCallerConfig f e loopPost (.ok f' e) ∧
      RD nestedCallerBytecode ee g s0 next.pc next.stack next.mem next.aw next.rdata next.world k' C' ∧
      fallthrough ⟨116⟩ (LoopInv M s0 ee target targetWord count rest v) (.ok f' e) (.reached next) := by
  let i' : UInt256 := ⟨1⟩ + i
  have hi' : i'.toNat = i.toNat + 1 := by
    have hc : count.toNat < UInt256.size := count.val.isLt
    dsimp [i']; rw [uadd_toNat]
    change (1 + i.toNat) % UInt256.size = i.toNat + 1
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  let f' : Frame := { f with locals := f.locals.insert "i" (wordValue i') }
  let next : Cursor := { cur with pc := ⟨116⟩, stack := loopStack targetWord count i' last rest }
  have hp : ExecBlock nestedCallerConfig f e loopPost (.ok f' e) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
    simp only [evalExpr?, hl.index, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
    simp [wordValue, hi']
  rw [hpc, hs] at rd
  have rn := nestedCaller_block_169 (by simp; omega) (by jump_dest) rd
  refine ⟨f', next, _, _, hp, rn, rfl, i', last, ?_, rfl, hl.insertIndex i', ?_, hw⟩
  · omega
  · simpa only [hi'] using hm

/-- After `sample` returns, 0 continues, 1 breaks, and all other words update
`last`. The generated branches also discard the compiler's dead value slot. -/
theorem afterSample {ee g s0 f e k C M target targetWord count rest v i last w Q} {cur : Cursor}
    (hpc : cur.pc = ⟨135⟩)
    (hs : cur.stack = w :: ⟨0⟩ :: loopStack targetWord count i last rest)
    (hlen : rest.length + 12 ≤ 1024) (hv : i.toNat + (v + 1) = count.toNat)
    (hl : LoopLocals f target count i last) (hvalue : f.locals.get? "value" = some (wordValue w))
    (hm : M (i.toNat + 1) cur.mem cur.aw) (hw : CallStateRel s0 ee cur.world e)
    (rd : RD nestedCallerBytecode ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C) :
    BlockProgress nestedCallerBytecode ee g s0 nestedCallerConfig f e loopBody.tail
      (forIterationExit nestedCallerConfig loopPost ⟨116⟩
        (LoopInv M s0 ee target targetWord count rest v)
        (sequenceExit ⟨180⟩ (LoopAt M s0 ee target targetWord count rest) Q)) := by
  rw [hpc, hs] at rd
  by_cases hz : w = ⟨0⟩
  · subst w
    have r132 := nestedCaller_block_135_fallthrough (by simp [loopStack]; omega) (by decide) rd
    have r156 := nestedCaller_block_145 (by simp [loopStack]; omega) (by jump_dest) r132
    obtain ⟨f', next, k', C', hp, rn, hrel⟩ := loopPostProgress
      (cur := {cur with pc := ⟨169⟩, stack := loopStack targetWord count i last rest})
      rfl rfl (by omega) hv hl hm hw r156
    refine ⟨.continue f e, .reached next, ?_, ⟨k', C', rn⟩, .ok f' e, hp, hrel⟩
    exact ExecBlock.consContinue (ExecStmt.iteTrue (by rw [evalValueEq hvalue 0]; rfl)
      (ExecBlock.consContinue ExecStmt.continue))
  · have hsub : UInt256.sub w ⟨0⟩ ≠ ⟨0⟩ := u256_sub_ne_zero_of_ne hz
    have r137 := nestedCaller_block_135_taken (by simp [loopStack]; omega) hsub (by jump_dest) rd
    have hzero : evalExpr? nestedCallerConfig f e (.binary .eq (.var "value") (.intLit 0)) = .ok (.bool false) := by
      rw [evalValueEq hvalue 0]; have hn : w.toNat ≠ 0 := fun h => hz (uint256_toNat_eq_zero h)
      congr 2
      simp only [beq_eq_false_iff_ne]
      exact_mod_cast hn
    apply BlockProgress.cons (ExecStmt.iteFalse hzero ExecBlock.nil)
    by_cases ho : w = ⟨1⟩
    · subst w
      have r146 := nestedCaller_block_150_fallthrough (by simp [loopStack]; omega) (by decide) r137
      have rn := nestedCaller_block_159 (by simp [loopStack]; omega) (by jump_dest) r146
      exact BlockProgress.ofRD
        (cur := {cur with pc := ⟨180⟩, stack := loopStack targetWord count i last rest})
        (ExecBlock.consBreak (ExecStmt.iteTrue (by rw [evalValueEq hvalue 1]; rfl)
          (ExecBlock.consBreak ExecStmt.break))) rn ⟨rfl, i, last, by omega, rfl, hl, hm, hw⟩
    · have hsub1 : UInt256.sub w ⟨1⟩ ≠ ⟨0⟩ := u256_sub_ne_zero_of_ne ho
      have r151 := nestedCaller_block_150_taken (by simp [loopStack]; omega) hsub1 (by jump_dest) r137
      have r156 := nestedCaller_block_164 (by simp; omega) r151
      have hone : evalExpr? nestedCallerConfig f e (.binary .eq (.var "value") (.intLit 1)) = .ok (.bool false) := by
        rw [evalValueEq hvalue 1]
        have hn : w.toNat ≠ 1 := by intro h; apply ho; apply u256_inj; exact h
        congr 2
        simp only [beq_eq_false_iff_ne]
        exact_mod_cast hn
      apply BlockProgress.cons (ExecStmt.iteFalse hone ExecBlock.nil)
      let f1 : Frame := {f with locals := f.locals.insert "last" (wordValue w)}
      obtain ⟨f', next, k', C', hp, rn, hrel⟩ := loopPostProgress
        (cur := {cur with pc := ⟨169⟩, stack := loopStack targetWord count i w rest})
        rfl rfl (by omega) hv (hl.insertLast w) hm hw r156
      refine ⟨.ok f1 e, .reached next, ?_, ⟨k', C', rn⟩, .ok f' e, hp, hrel⟩
      exact ExecBlock.consNormal (ExecStmt.letDecl
        (by simp only [evalExpr?, hvalue, EvalResult.ofOption])) ExecBlock.nil


/-- Input and output specifications of the compiled internal helper. The caller's
stack is preserved beneath the return value; the helper's locals are private. -/
def SampleEntry (M : ByteArray → UInt256 → Prop) (s0 : State) (ee : ExecutionEnv)
    (target : AccountAddress) (targetWord i : UInt256) (saved : List UInt256) : StateRel :=
  fun cur f e => cur.stack = [i, targetWord, ⟨135⟩] ++ saved ∧
    f.contract = nestedCallerContract ∧
    f.locals.get? "target" = some (.address target) ∧ f.locals.get? "i" = some (wordValue i) ∧
    M cur.mem cur.aw ∧ CallStateRel s0 ee cur.world e

def SampleReturn (M : ByteArray → UInt256 → Prop) (s0 : State) (ee : ExecutionEnv)
    (saved : List UInt256) (value : Option (List Value)) : StateRel :=
  fun cur _ e => ∃ w, value = some [wordValue w] ∧ cur.pc = ⟨135⟩ ∧
    cur.stack = w :: saved ∧ M cur.mem cur.aw ∧ CallStateRel s0 ee cur.world e

/-- Compose the real compiler loop with the helper refinement. The helper's return
is an internal cursor, whereas source reversion goes directly to transaction revert.
Both normal body completion and continue execute post; break reaches the tail. -/
theorem loopRefines {ee g s0 M target targetWord count rest stmts Q}
    (hmono : ∀ n mem aw, M n mem aw → M (n + 1) mem aw)
    (hlen : rest.length + 24 ≤ 1024)
    (hsample : ∀ i last, i.toNat < count.toNat →
      StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨191⟩
        (SampleEntry (M i.toNat) s0 ee target targetWord i (⟨0⟩ :: loopStack targetWord count i last rest))
        sampleFunction.body
        (internalCallExit (SampleReturn (M (i.toNat + 1)) s0 ee (⟨0⟩ :: loopStack targetWord count i last rest))))
    (hrevert : Q .reverted .reverted)
    (htail : StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨180⟩
      (LoopAt M s0 ee target targetWord count rest) stmts Q) (v : ℕ) :
    StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨116⟩
      (LoopInv M s0 ee target targetWord count rest v)
      (.for [] (.binary .lt (.var "i") (.var "count")) loopPost loopBody :: stmts) Q := by
  apply StmtsRefine.forLoopCombined (header := ⟨116⟩) (bodyHeader := ⟨125⟩) (exit := ⟨180⟩)
    (Inv := LoopInv M s0 ee target targetWord count rest)
    (BodyInv := fun v => LoopInv M s0 ee target targetWord count rest (v + 1))
    (R := LoopAt M s0 ee target targetWord count rest)
  · intro cur f e hi
    rcases hi with ⟨i, last, hv, hs, hl, hm, hw⟩
    rw [evalLt hl]
    have hn : ¬ i.toNat < count.toNat := by omega
    simp [hn]
  · intro v cur f e hi
    rcases hi with ⟨i, last, hv, hs, hl, hm, hw⟩
    rw [evalLt hl]
    have hn : i.toNat < count.toNat := by omega
    simp [hn]
  · intro cur k C f e hpc rd hi
    rcases hi with ⟨i, last, hv, hs, hl, hm, hw⟩
    rw [hpc, hs] at rd
    have rn := nestedCaller_block_116_taken (by simp; omega)
      (by rw [ult_zero (by omega)]; decide) (by jump_dest) rd
    exact BlockProgress.ofRD (cur := {cur with pc := ⟨180⟩}) ExecBlock.nil
      (by simpa only [hs] using rn) ⟨rfl, i, last, by omega, hs, hl, hmono _ _ _ hm, hw⟩
  · intro v cur k C f e hpc rd hi
    obtain ⟨i, last, hv, hs, hl, hm, hw⟩ := hi
    rw [hpc, hs] at rd
    have rn := nestedCaller_block_116_fallthrough (by simp; omega)
      (by rw [ult_one (by omega)]; decide) rd
    exact BlockProgress.ofRD (cur := {cur with pc := ⟨125⟩}) ExecBlock.nil
      (by simpa only [hs] using rn) ⟨rfl, i, last, hv, hs, hl, hm, hw⟩
  · intro v cur k C f e hpc rd hi
    rcases hi with ⟨i, last, hv, hs, hl, hm, hw⟩
    rw [hpc, hs] at rd
    have rn := nestedCaller_block_125 (by simp; omega) (by jump_dest) rd
    let next : Cursor := {cur with pc := ⟨191⟩, stack := [i, targetWord, ⟨135⟩, ⟨0⟩] ++ loopStack targetWord count i last rest}
    let locals : Store := ((∅ : Store).insert "i" (wordValue i)).insert "target" (.address target)
    have hb := hsample i last (by omega) next _ _ { f with locals := locals } e rfl rn
      ⟨rfl, hl.contract, by simp [locals], by dsimp only [locals]; rw [store_get_ne _ _ (by decide), store_get_self], hm, hw⟩
    refine BlockProgress.internalCall (argVals := [.address target, wordValue i])
      (callee := sampleFunction.toCallable) (locals := locals)
      (R := SampleReturn (M (i.toNat + 1)) s0 ee (⟨0⟩ :: loopStack targetWord count i last rest))
      ?_ ?_ ?_ hb (by exact hrevert) ?_
    · simp only [evalExprs?, evalExpr?, hl.target, hl.index, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
    · rw [hl.contract]; rfl
    · rfl
    · intro value next calleeFrame calleeEvm k' C' rd hr
      rcases hr with ⟨w, rfl, hpc, hs, hm, hw⟩
      exact afterSample hpc hs (by omega) hv (hl.insertValue w)
        (by simp [resumeAfterInternalCall, collapseReturns]) hm hw rd
  · exact htail

end NestedCaller
