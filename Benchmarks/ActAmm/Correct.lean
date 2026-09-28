import Benchmarks.ActAmm.Constructor
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Dispatch
import Benchmarks.ActAmm.Approve
import Benchmarks.ActAmm.Burn
import Benchmarks.ActAmm.TotalSupply
import Benchmarks.ActAmm.TransferFrom
import Benchmarks.ActAmm.Swap1
import Benchmarks.ActAmm.Mint
import Benchmarks.ActAmm.BalanceOf
import Benchmarks.ActAmm.Transfer
import Benchmarks.ActAmm.Allowance
import Benchmarks.ActAmm.Swap0
import Solm.Equiv
import Reasoning.SolmBody

/-!
# Act AMM EquiVM benchmark target

Runtime equivalence for only the `Amm` bytecode selected by Act's multisource JSON.  Reserve-token
interactions remain external EVM calls; no `Token` runtime bytecode is part of this theorem.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

theorem ammDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [allowanceTransition, approveTransition, balanceOfTransition, burnTransition,
      mintTransition, swap0Transition, swap1Transition, totalSupplyTransition,
      transferTransition, transferFromTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, ammAllowanceSelectorBytes]; rfl
    · rw [selectorOf, ammApproveSelectorBytes]; rfl
    · rw [selectorOf, ammBalanceOfSelectorBytes]; rfl
    · rw [selectorOf, ammBurnSelectorBytes]; rfl
    · rw [selectorOf, ammMintSelectorBytes]; rfl
    · rw [selectorOf, ammSwap0SelectorBytes]; rfl
    · rw [selectorOf, ammSwap1SelectorBytes]; rfl
    · rw [selectorOf, ammTotalSupplySelectorBytes]; rfl
    · rw [selectorOf, ammTransferSelectorBytes]; rfl
    · rw [selectorOf, ammTransferFromSelectorBytes]; rfl) h

theorem ammDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 10 → (ammSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ammAllowanceSelectorBytes]; simpa [ammSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, ammApproveSelectorBytes]; simpa [ammSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, ammBalanceOfSelectorBytes]; simpa [ammSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, ammBurnSelectorBytes]; simpa [ammSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, ammMintSelectorBytes]; simpa [ammSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, ammSwap0SelectorBytes]; simpa [ammSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, ammSwap1SelectorBytes]; simpa [ammSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, ammTotalSupplySelectorBytes]; simpa [ammSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, ammTransferSelectorBytes]; simpa [ammSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, ammTransferFromSelectorBytes]; simpa [ammSelBytes] using hnm 3 (by omega)

theorem ammBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

set_option maxRecDepth 2000000 in
theorem ammX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ammBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt ammBytecode) (opC := solcGuardTgtOp ammBytecode)
    (wC := solcGuardTgtWidth ammBytecode)
    (solcGuardPrologueRD hcode (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    hwv (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)

set_option maxRecDepth 2000000 in
theorem ammX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ammBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt ammBytecode) (opC := solcGuardTgtOp ammBytecode)
    (wC := solcGuardTgtWidth ammBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc ammBytecode)
    (rtgt := solcCalldataRevertTgt ammBytecode)
    (opR := solcCalldataRevertTgtOp ammBytecode)
    (wR := solcCalldataRevertTgtWidth ammBytecode)
    h1 hsz (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide)
    (by native_decide) (by native_decide)

theorem ammNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ammX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (ammBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem ammShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ammX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (ammDispatch_none_short hsz)

theorem ammNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 10 → (ammSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (ammX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (ammDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (ammX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (ammDispatch_none_short hshort)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammRuntimeCorrect :
    runtimeEquivalence config ammBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    ·
      by_cases h0 : ammSelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · have hhit : (ammSelBytes 0 == I.calldata.extract 0 4) = true := by
            simpa [ammSelIs, ammSelBytes] using h0
        have hmatch := ammLowMatches 0 (by omega) hsz hhit
        have hreach := ammReachLowBody 0 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨160⟩ hcode hwv hsz hsize
          (ammLowPivotTaken 0 (by omega) hsz hhit)
          hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
        exact ammApproveBodyCore hcode hsize hperm hwv h0 hreach hAccounts
      ·
        by_cases h1 : ammSelIs I ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩
        · have hhit : (ammSelBytes 1 == I.calldata.extract 0 4) = true := by
              simpa [ammSelIs, ammSelBytes] using h1
          have hmatch := ammLowMatches 1 (by omega) hsz hhit
          have hreach := ammReachLowBody 1 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨208⟩ hcode hwv hsz hsize
            (ammLowPivotTaken 1 (by omega) hsz hhit)
            hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
          exact ammSwap0BodyCore hcode hsize hperm hwv h1 hreach hAccounts
        ·
          by_cases h2 : ammSelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
          · have hhit : (ammSelBytes 2 == I.calldata.extract 0 4) = true := by
                simpa [ammSelIs, ammSelBytes] using h2
            have hmatch := ammLowMatches 2 (by omega) hsz hhit
            have hreach := ammReachLowBody 2 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨236⟩ hcode hwv hsz hsize
              (ammLowPivotTaken 2 (by omega) hsz hhit)
              hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
            exact ammTotalSupplyBodyCore hcode hsize hperm hwv h2 hreach hAccounts
          ·
            by_cases h3 : ammSelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
            · have hhit : (ammSelBytes 3 == I.calldata.extract 0 4) = true := by
                  simpa [ammSelIs, ammSelBytes] using h3
              have hmatch := ammLowMatches 3 (by omega) hsz hhit
              have hreach := ammReachLowBody 3 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨266⟩ hcode hwv hsz hsize
                (ammLowPivotTaken 3 (by omega) hsz hhit)
                hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
              exact ammTransferFromBodyCore hcode hsize hperm hwv h3 hreach hAccounts
            ·
              by_cases h4 : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩
              · have hhit : (ammSelBytes 4 == I.calldata.extract 0 4) = true := by
                    simpa [ammSelIs, ammSelBytes] using h4
                have hmatch := ammLowMatches 4 (by omega) hsz hhit
                have hreach := ammReachLowBody 4 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨314⟩ hcode hwv hsz hsize
                  (ammLowPivotTaken 4 (by omega) hsz hhit)
                  hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                exact ammSwap1BodyCore hcode hsize hperm hwv h4 hreach hAccounts
              ·
                by_cases h5 : ammSelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩
                · have hhit : (ammSelBytes 5 == I.calldata.extract 0 4) = true := by
                      simpa [ammSelIs, ammSelBytes] using h5
                  have hmatch := ammHighMatches 0 (by omega) hsz hhit
                  have hreach := ammReachHighBody 0 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨342⟩ hcode hwv hsz hsize
                    (ammHighPivotNotTaken 0 (by omega) hsz hhit)
                    hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                  exact ammMintBodyCore hcode hsize hperm hwv h5 hreach hAccounts
                ·
                  by_cases h6 : ammSelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
                  · have hhit : (ammSelBytes 6 == I.calldata.extract 0 4) = true := by
                        simpa [ammSelIs, ammSelBytes] using h6
                    have hmatch := ammHighMatches 1 (by omega) hsz hhit
                    have hreach := ammReachHighBody 1 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨390⟩ hcode hwv hsz hsize
                      (ammHighPivotNotTaken 1 (by omega) hsz hhit)
                      hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                    exact ammBalanceOfBodyCore hcode hsize hperm hwv h6 hreach hAccounts
                  ·
                    by_cases h7 : ammSelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩
                    · have hhit : (ammSelBytes 7 == I.calldata.extract 0 4) = true := by
                          simpa [ammSelIs, ammSelBytes] using h7
                      have hmatch := ammHighMatches 2 (by omega) hsz hhit
                      have hreach := ammReachHighBody 2 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨438⟩ hcode hwv hsz hsize
                        (ammHighPivotNotTaken 2 (by omega) hsz hhit)
                        hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                      exact ammTransferBodyCore hcode hsize hperm hwv h7 hreach hAccounts
                    ·
                      by_cases h8 : ammSelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                      · have hhit : (ammSelBytes 8 == I.calldata.extract 0 4) = true := by
                            simpa [ammSelIs, ammSelBytes] using h8
                        have hmatch := ammHighMatches 3 (by omega) hsz hhit
                        have hreach := ammReachHighBody 3 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨486⟩ hcode hwv hsz hsize
                          (ammHighPivotNotTaken 3 (by omega) hsz hhit)
                          hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                        exact ammAllowanceBodyCore hcode hsize hperm hwv h8 hreach hAccounts
                      ·
                        by_cases h9 : ammSelIs I ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩
                        · have hhit : (ammSelBytes 9 == I.calldata.extract 0 4) = true := by
                              simpa [ammSelIs, ammSelBytes] using h9
                          have hmatch := ammHighMatches 4 (by omega) hsz hhit
                          have hreach := ammReachHighBody 4 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g) (by omega) ⟨534⟩ hcode hwv hsz hsize
                            (ammHighPivotNotTaken 4 (by omega) hsz hhit)
                            hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                          exact ammBurnBodyCore hcode hsize hperm hwv h9 hreach hAccounts
                        ·
                          refine ammNoDispatch hcode hsize hperm hwv ?_
                          intro i hi
                          interval_cases i
                          · simpa [ammSelIs, ammSelBytes] using h0
                          · simpa [ammSelIs, ammSelBytes] using h1
                          · simpa [ammSelIs, ammSelBytes] using h2
                          · simpa [ammSelIs, ammSelBytes] using h3
                          · simpa [ammSelIs, ammSelBytes] using h4
                          · simpa [ammSelIs, ammSelBytes] using h5
                          · simpa [ammSelIs, ammSelBytes] using h6
                          · simpa [ammSelIs, ammSelBytes] using h7
                          · simpa [ammSelIs, ammSelBytes] using h8
                          · simpa [ammSelIs, ammSelBytes] using h9
    · exact ammShortRevert hcode hsize hperm hwv (by omega)
  · exact ammNonPayable hcode hwv


theorem ammContractCorrect :
    contractEquivalence config ammCreationBytecode ammBytecode contract :=
  contractEquivalence.intro ammConstructorCorrect ammRuntimeCorrect

end Benchmarks.ActAmm
