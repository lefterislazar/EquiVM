import Benchmarks.ActAmmToken.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.ActAmmToken

theorem tokenDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [allowanceTransition, approveTransition, balanceOfTransition, burnTransition,
      burnFromTransition, mintTransition, totalSupplyTransition, transferTransition,
      transferFromTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, allowanceSelectorBytes]; rfl
    · rw [selectorOf, approveSelectorBytes]; rfl
    · rw [selectorOf, balanceOfSelectorBytes]; rfl
    · rw [selectorOf, burnSelectorBytes]; rfl
    · rw [selectorOf, burnFromSelectorBytes]; rfl
    · rw [selectorOf, mintSelectorBytes]; rfl
    · rw [selectorOf, totalSupplySelectorBytes]; rfl
    · rw [selectorOf, transferSelectorBytes]; rfl
    · rw [selectorOf, transferFromSelectorBytes]; rfl) h

theorem tokenDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 9 → (tokenSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, allowanceSelectorBytes]; simpa [tokenSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, approveSelectorBytes]; simpa [tokenSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, balanceOfSelectorBytes]; simpa [tokenSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, burnSelectorBytes]; simpa [tokenSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, burnFromSelectorBytes]; simpa [tokenSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, mintSelectorBytes]; simpa [tokenSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, totalSupplySelectorBytes]; simpa [tokenSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, transferSelectorBytes]; simpa [tokenSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, transferFromSelectorBytes]; simpa [tokenSelBytes] using hnm 2 (by omega)

theorem tokenBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

set_option maxHeartbeats 1000000 in
theorem tokenX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt tokenBytecode) (opC := solcGuardTgtOp tokenBytecode)
    (wC := solcGuardTgtWidth tokenBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem tokenX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt tokenBytecode) (opC := solcGuardTgtOp tokenBytecode)
    (wC := solcGuardTgtWidth tokenBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc tokenBytecode)
    (rtgt := solcCalldataRevertTgt tokenBytecode)
    (opR := solcCalldataRevertTgtOp tokenBytecode)
    (wR := solcCalldataRevertTgtWidth tokenBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

set_option maxHeartbeats 1000000 in
theorem tokenX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 9 → (tokenSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat tokenBytecode
        (nthArmPc tokenBytecode tokenLowFirstArmPc j)) (tokenSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [tokenLowArmEq I hsz j hj, hnm j (by omega)]
    rfl
  have heqHigh0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat tokenBytecode
        (nthArmPc tokenBytecode tokenHighFirstArmPc j)) (tokenSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [tokenHighArmEq I hsz j hj, hnm (j + 4) (by omega)]
    rfl
  obtain ⟨kS, CS, hsplit⟩ := tokenReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat tokenBytecode tokenSplitPc) (tokenSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit tokenSplitWellFormed hpivot (by simp)
    have h96 := h41
      |>.selectorArmNotTakenAuto (tokenHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenHighArmsWellFormed 4 (by omega))
          (heqHigh0 4 (by omega)) (by simp)
    have h96' : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨96⟩
        [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [tokenHighFirstArmPc, tokenSplitPc, nthArmPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h96
    obtain ⟨_, _, rd96⟩ := h96'
    have rd145 := evm_run rd96 with [push2 ⟨145⟩, jump (by jump_dest)]
    have rd146 := rd145.jumpdest (by decide) (by simp)
    exact rd146.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h100 := RD.selectorSplitTakenAuto hsplit tokenSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h101 := h100.jumpdest (by decide) (by simp)
    have h145 := h101
      |>.selectorArmNotTakenAuto (tokenLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (tokenLowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
    have h145' : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨145⟩
        [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22 + 22, ?_⟩
      simpa [tokenLowFirstArmPc, tokenLowJumpdestPc, tokenSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h145
    obtain ⟨_, _, rd145⟩ := h145'
    have rd146 := rd145.jumpdest (by decide) (by simp)
    exact rd146.revertStub (by decide) (by decide) (by decide) (by simp)

theorem tokenNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 9 → (tokenSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (tokenX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (tokenDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (tokenX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch
      hcode (tokenDispatch_none_short hshort)

theorem tokenShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (tokenX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch
    hcode (tokenDispatch_none_short hsz)

theorem tokenNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (tokenX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (tokenBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

end Benchmarks.ActAmmToken
