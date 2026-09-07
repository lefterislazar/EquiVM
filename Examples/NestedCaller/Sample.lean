import Examples.NestedCaller.ControlFlow

namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory Reasoning.Refinement
open nestedCallerBlocks

set_option maxRecDepth 10000

/-- The source and bytecode have both passed the explicit gasleft guard. -/
def ProbeEntry (M : ByteArray → UInt256 → Prop) (s0 : State) (ee : ExecutionEnv)
    (target : AccountAddress) (targetWord i : UInt256) (saved : List UInt256) : StateRel :=
  fun cur f e => ∃ gas, cur.stack = [gas, ⟨0⟩, i, targetWord, ⟨135⟩] ++ saved ∧
    f.contract = nestedCallerContract ∧
    f.locals.get? "target" = some (.address target) ∧ f.locals.get? "i" = some (wordValue i) ∧
    f.locals.get? "remaining" = some (wordValue gas) ∧
    M cur.mem cur.aw ∧ CallStateRel s0 ee cur.world e

/-- The helper pairs the explicit GAS with `.letGas`. Low gas returns zero to
its actual internal continuation; otherwise execution reaches the external call
prefix. No EVM out-of-gas case split appears in the client proof. -/
theorem sampleRefines {ee g s0 M N target targetWord i saved}
    (hlen : saved.length + 12 ≤ 1024)
    (hweaken : ∀ mem aw, M mem aw → N mem aw)
    (hprobe : StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨215⟩
      (ProbeEntry M s0 ee target targetWord i saved) (sampleFunction.body.drop 2)
      (internalCallExit (SampleReturn N s0 ee saved))) :
    StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨191⟩
      (SampleEntry M s0 ee target targetWord i saved) sampleFunction.body
      (internalCallExit (SampleReturn N s0 ee saved)) := by
  intro cur k C f e hpc rd hp
  rcases hp with ⟨hs, hc, ht, hi, hm, hw⟩
  rw [hpc, hs] at rd
  have rn := nestedCaller_block_191 (by simp; omega) rd
  let gascur : Cursor := {cur with pc := ⟨194⟩, stack := [⟨0⟩, ⟨0⟩, i, targetWord, ⟨135⟩] ++ saved}
  refine BlockRefinesFrom.letGas (cur := gascur) (P := fun _ _ _ => True)
    (by change decode nestedCallerBytecode ⟨194⟩ = _; decide) (by simp [gascur]; omega) ?_ rn trivial
  intro gas rd _
  let f' : Frame := {f with locals := f.locals.insert "remaining" (wordValue gas)}
  have hg : evalExpr? nestedCallerConfig f' e
      (.binary .lt (.var "remaining") (.intLit 1000)) = .ok (.bool (gas.toNat < 1000)) := by
    simp only [evalExpr?, f', store_get_self, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
    change EvalResult.ok (Value.bool ((gas.toNat : ℤ) < 1000)) = EvalResult.ok (Value.bool (gas.toNat < 1000))
    simp
  have ht' : f'.locals.get? "target" = some (.address target) := by
    dsimp only [f']; rw [store_get_ne _ _ (by decide)]; exact ht
  have hi' : f'.locals.get? "i" = some (wordValue i) := by
    dsimp only [f']; rw [store_get_ne _ _ (by decide)]; exact hi
  by_cases hlow : gas.toNat < 1000
  · have r207 := nestedCaller_block_195_fallthrough (by simp; omega)
      (by rw [ult_one (by exact hlow)]; decide) rd
    have r340 := nestedCaller_block_207 (by simp; omega) (by jump_dest) r207
    have r135 := nestedCaller_block_340 (by simp; omega) (by jump_dest) r340
    exact BlockProgress.ofRD (cur := {cur with pc := ⟨135⟩, stack := ⟨0⟩ :: saved})
      (ExecBlock.consReturn (ExecStmt.iteTrue (by simpa [hlow] using hg)
        (ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?]; rfl)))))
      r135 ⟨⟨0⟩, rfl, rfl, rfl, hweaken _ _ hm, hw⟩
  · have r215 := nestedCaller_block_195_taken (by simp; omega)
      (by rw [ult_zero (by change 1000 ≤ gas.toNat; omega)]; decide) (by jump_dest) rd
    refine BlockProgress.cons (ExecStmt.iteFalse (by simpa [hlow] using hg) ExecBlock.nil) ?_
    exact hprobe {cur with pc := ⟨215⟩, stack := [gas, ⟨0⟩, i, targetWord, ⟨135⟩] ++ saved}
      _ _ f' e rfl r215 ⟨gas, rfl, hc, ht', hi', store_get_self _ _ _, hm, hw⟩

end NestedCaller
