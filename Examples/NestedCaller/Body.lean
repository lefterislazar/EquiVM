import Examples.NestedCaller.External
import Reasoning.RuntimeRefinement

namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory Reasoning.Refinement
open nestedCallerBlocks
set_option maxRecDepth 1500

private theorem word_add_zero (a : UInt256) : a + ⟨0⟩ = a := by
  apply u256_inj
  rw [uadd_toNat]
  change (a.toNat + 0) % UInt256.size = a.toNat
  exact Nat.mod_eq_of_lt a.val.isLt

/-- The Solidity return encoder uses the current free pointer, including after
several external calls, and returns exactly the source uint256 value. -/
theorem returnWord {ee g s0 mem aw rdata world k C fp w rest}
    (hfp : 128 ≤ fp) (hfphi : fp < 2 ^ 144)
    (hsize : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray)
    (hawlo : 3 ≤ aw.toNat) (hawhi : aw.toNat < 2 ^ 144)
    (hlen : rest.length + 12 ≤ 1024)
    (rd : RD nestedCallerBytecode ee g s0 ⟨71⟩ (w :: rest) mem aw rdata world k C) :
    RDret nestedCallerBytecode g s0 world w.toByteArray := by
  have hfpu : fp + 63 < UInt256.size := by norm_num [UInt256.size] at *; omega
  have hm := mload64_eq hsize hread hawlo hawhi
  change memLoad (UInt256.ofNat 64) aw mem = _ at hm
  have he : Reasoning.Reach.M aw (UInt256.ofNat 64) ⟨32⟩ = aw :=
    expand_eq (by change 64 + 32 ≤ aw.toNat * 32; omega)
  have r568 := nestedCaller_block_71 (by simp; omega) (by jump_dest) rd
  rw [hm, he] at r568
  have r553 := nestedCaller_block_568 (by simp; omega) (by jump_dest) r568
  have r440 := nestedCaller_block_553 (by simp; omega) (by jump_dest) r553
  have r562 := nestedCaller_block_440 (by simp; omega) (by jump_dest) r440
  have r587 := nestedCaller_block_562 (by simp; omega) (by jump_dest) r562
  simp only [word_add_zero, ulit_toNat' fp (by omega)] at r587
  have r84 := nestedCaller_block_587 (by simp; omega) (by jump_dest) r587
  let mem' := w.toByteArray.write 0 mem fp 32
  let aw' := Reasoning.Reach.M aw (UInt256.ofNat fp) ⟨32⟩
  have hwords := wordExpansion_toNat (aw := aw) hfphi
  have hsize' : fp + 32 ≤ mem'.size := toByteArray_write_size_ge_off_add32_unbounded _ _ _
  have hread' : mem'.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray := by
    rw [toByteArray_write_read_below_of_gap_unbounded _ _ _ _ hsize (by omega), hread]
  have hm' : memLoad (UInt256.ofNat 64) aw' mem' = UInt256.ofNat fp :=
    mload64_eq (by omega) hread' (by change 3 ≤ (Reasoning.Reach.M aw _ _).toNat; rw [hwords]; omega)
      (by change (Reasoning.Reach.M aw _ _).toNat < 2 ^ 144; rw [hwords]; omega)
  change RD nestedCallerBytecode ee g s0 _ _ mem' aw' _ _ _ _ at r84
  have hr := nestedCaller_block_84 (by simp; omega) r84
  rw [hm'] at hr
  have hd := usub_uadd_lit_cancel_mod (base := fp) (n := 32) (by omega) (by decide)
  change (UInt256.ofNat fp + UInt256.ofNat 32).sub (UInt256.ofNat fp) = UInt256.ofNat 32 at hd
  rw [hd, ulit_toNat' fp (by omega)] at hr
  change RDret nestedCallerBytecode g s0 world (mem'.readWithPadding fp 32) at hr
  rw [toByteArray_write_read_back_of_gap_unbounded] at hr
  exact hr

/-- Both false-guard exit and break use this return tail. -/
theorem loopTail {ee g s0 target targetWord count rest}
    (hcount : count.toNat ≤ 16) (hlen : rest.length + 12 ≤ 1024) :
    StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨180⟩
      (LoopAt MemoryAt s0 ee target targetWord count rest) [.return [.var "last"]]
      (runtimeExit (.abi [uint256])) := by
  intro cur k C f e hpc rd hp
  rcases hp with ⟨i, last, hibound, hs, hl, hm, hw⟩
  rcases hm with ⟨fp, hfplo, hfphi, hsize, hread, hawlo, hawhi⟩
  have hb := allocationBound_small (n := i.toNat + 1) (by omega)
  rw [hpc, hs] at rd
  have r71 := nestedCaller_block_180 (by simp; omega) (by jump_dest) rd
  have rr := returnWord hfplo (by omega) hsize hread hawlo (by omega) hlen r71
  refine BlockProgress.ofRDret
    (ExecBlock.consReturn (ExecStmt.return (values := [wordValue last]) ?_)) rr
    hw.created.symm hw.accounts ?_
  · simp only [evalExprs?, evalExpr?, hl.last, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · exact .abi (.returned rfl (uint256ReturnEncoding last))


/-- A complete body refinement from the decoded ABI entry. -/
theorem bodyRefines {ee g s0 targetWord count sel k C f e world}
    {target : AccountAddress}
    (hcv : ee.weiValue = ⟨0⟩) (hperm : ee.perm = true)
    (hc : f.contract = nestedCallerContract)
    (ht : f.locals.get? "target" = some (.address target))
    (hn : f.locals.get? "count" = some (wordValue count))
    (hmask : UInt256.land ⟨1461501637330902918203684832716283019655932542975⟩ targetWord = targetWord)
    (htarget : EVM.address target = AccountAddress.ofUInt256 targetWord) :
    BlockRefinesFrom nestedCallerBytecode ee g s0 nestedCallerConfig
      { pc := ⟨93⟩, stack := [count, targetWord, ⟨71⟩, sel], mem := solcFreePtrMem, aw := ⟨3⟩, rdata := ByteArray.empty, world := world } k C f e
      (fun cur _ e => CallStateRel s0 ee cur.world e) runTransition.body
      (runtimeExit (.abi [uint256])) := by
  intro rd hw
  refine BlockProgress.cons (ExecStmt.requireTrue (evalCallvalueEq_true (by rw [hw.env]; exact hcv))) ?_
  have heval : evalExpr? nestedCallerConfig f e (.binary .le (.var "count") (.intLit 16)) =
      .ok (.bool (count.toNat ≤ 16)) := by
    simp only [evalExpr?, hn, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
    change EvalResult.ok (Value.bool ((count.toNat : ℤ) ≤ 16)) = EvalResult.ok (Value.bool (count.toNat ≤ 16))
    simp
  by_cases hcount : count.toNat ≤ 16
  · have r107 := nestedCaller_block_93_taken (by simp)
      (by rw [ugt_zero (by exact hcount)]; decide) (by jump_dest) rd
    refine BlockProgress.cons (ExecStmt.requireTrue (by simpa [hcount] using heval)) ?_
    let f1 : Frame := { f with locals := f.locals.insert "last" (wordValue ⟨0⟩) }
    refine BlockProgress.cons (frame' := f1) (ExecStmt.letDecl (by simp only [evalExpr?]; rfl)) ?_
    refine BlockProgress.forInit ?_
    let f2 : Frame := { f1 with locals := f1.locals.insert "i" (wordValue ⟨0⟩) }
    let header : Cursor := {pc := ⟨116⟩, stack := loopStack targetWord count ⟨0⟩ ⟨0⟩ [sel], mem := solcFreePtrMem, aw := ⟨3⟩, rdata := ByteArray.empty, world := world}
    have rh := nestedCaller_block_107 (by simp) r107
    have hl : LoopLocals f2 target count ⟨0⟩ ⟨0⟩ := by
      refine ⟨hc, ?_, ?_, store_get_self _ _ _, ?_⟩
      · dsimp only [f2, f1]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]; exact ht
      · dsimp only [f2, f1]; rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]; exact hn
      · dsimp only [f2, f1]; rw [store_get_ne _ _ (by decide), store_get_self]
    refine BlockProgress.seqOfRD (front := [.letDecl "i" none (.intLit 0)]) (cur' := header)
      (R := LoopInv MemoryAt s0 ee target targetWord count [sel] count.toNat)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?]; rfl)) ExecBlock.nil)
      rh ⟨⟨0⟩, ⟨0⟩, by simp, rfl, hl, memoryAt_initial, hw⟩ ?_
    refine loopRefines (M := MemoryAt) (target := target) (targetWord := targetWord)
      (count := count) (rest := [sel]) (stmts := [.return [.var "last"]])
      (Q := runtimeExit (.abi [uint256])) (fun _ _ _ => memoryAt_mono) (by simp) ?_ trivial (loopTail hcount (by simp))
      count.toNat header _ _ f2 e rfl
    intro i last hibound
    apply sampleRefines (by simp [loopStack]) (fun _ _ => memoryAt_mono)
    exact probeRefines (by omega) (by simp [loopStack]) hperm hmask htarget
  · have r104 := nestedCaller_block_93_fallthrough (by simp)
      (by rw [ugt_one (by change 16 < count.toNat; omega)]; decide) rd
    exact BlockProgress.ofRDrev
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simpa [hcount] using heval)))
      (nestedCaller_block_104 (by simp) r104)

end NestedCaller
