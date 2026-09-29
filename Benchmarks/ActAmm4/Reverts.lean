import Benchmarks.ActAmm4.Dispatch
import Benchmarks.ActAmm4.Trusted
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

theorem amm4Dispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [allowanceTransition, approveTransition, balanceOfTransition, burnTransition,
      mintTransition, swapTransition, totalSupplyTransition,
      transferTransition, transferFromTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, amm4AllowanceSelectorBytes]; rfl
    · rw [selectorOf, amm4ApproveSelectorBytes]; rfl
    · rw [selectorOf, amm4BalanceOfSelectorBytes]; rfl
    · rw [selectorOf, amm4BurnSelectorBytes]; rfl
    · rw [selectorOf, amm4MintSelectorBytes]; rfl
    · rw [selectorOf, amm4SwapSelectorBytes]; rfl
    · rw [selectorOf, amm4TotalSupplySelectorBytes]; rfl
    · rw [selectorOf, amm4TransferSelectorBytes]; rfl
    · rw [selectorOf, amm4TransferFromSelectorBytes]; rfl) h

theorem amm4Dispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 9 → (amm4SelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, amm4AllowanceSelectorBytes]; simpa [amm4SelBytes] using hnm 7 (by omega)
  · rw [selectorOf, amm4ApproveSelectorBytes]; simpa [amm4SelBytes] using hnm 0 (by omega)
  · rw [selectorOf, amm4BalanceOfSelectorBytes]; simpa [amm4SelBytes] using hnm 5 (by omega)
  · rw [selectorOf, amm4BurnSelectorBytes]; simpa [amm4SelBytes] using hnm 8 (by omega)
  · rw [selectorOf, amm4MintSelectorBytes]; simpa [amm4SelBytes] using hnm 3 (by omega)
  · rw [selectorOf, amm4SwapSelectorBytes]; simpa [amm4SelBytes] using hnm 4 (by omega)
  · rw [selectorOf, amm4TotalSupplySelectorBytes]; simpa [amm4SelBytes] using hnm 1 (by omega)
  · rw [selectorOf, amm4TransferSelectorBytes]; simpa [amm4SelBytes] using hnm 6 (by omega)
  · rw [selectorOf, amm4TransferFromSelectorBytes]; simpa [amm4SelBytes] using hnm 2 (by omega)

theorem amm4BodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

set_option maxRecDepth 2000000 in
theorem amm4X_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt amm4Bytecode) (opC := solcGuardTgtOp amm4Bytecode)
    (wC := solcGuardTgtWidth amm4Bytecode)
    (solcGuardPrologueRD hcode (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    hwv (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)

set_option maxRecDepth 2000000 in
theorem amm4X_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt amm4Bytecode) (opC := solcGuardTgtOp amm4Bytecode)
    (wC := solcGuardTgtWidth amm4Bytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc amm4Bytecode)
    (rtgt := solcCalldataRevertTgt amm4Bytecode)
    (opR := solcCalldataRevertTgtOp amm4Bytecode)
    (wR := solcCalldataRevertTgtWidth amm4Bytecode)
    h1 hsz (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide)

theorem amm4NonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (amm4X_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (amm4BodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem amm4ShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (amm4X_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (amm4Dispatch_none_short hsz)

theorem amm4NoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 9 → (amm4SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (amm4X_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (amm4Dispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (amm4X_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (amm4Dispatch_none_short hshort)


end Benchmarks.ActAmm4
