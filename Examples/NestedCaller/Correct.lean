import Examples.NestedCaller.Body
import Examples.NestedCaller.Dispatch

/-! Full runtime refinement of the bounded nested-caller example. The dispatcher
and ABI failures are included; neither the target's code nor call outcomes are
assumed. The body proof uses the paired GAS/CALL, internal-call and combined-loop
rules, with generated RD summaries for bytecode segments. -/
namespace NestedCaller
open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory Reasoning.Refinement
set_option maxRecDepth 1500
set_option maxHeartbeats 1000000

private theorem decodeArgs {I : ExecutionEnv} (hlo : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hcanon : (targetArg I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes I.calldata =
      some (decodedLocals I) := by
  simpa [runTransition, addr, uint256, abiUInt256, calldataWord, targetArg, countArg, decodedLocals]
    using decodeCalldata_addr_uint256_ok (cd := I.calldata) (x := "target") (y := "count") hlo hhi hcanon

private theorem decodeShort {I : ExecutionEnv} (hfour : 4 ≤ I.calldata.size) (hlo : I.calldata.size < 68) :
    decodeCalldata (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short (cd := I.calldata) (x := "target") (y := "count") hfour hlo

private theorem decodeHuge {I : ExecutionEnv} (hhi : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge (cd := I.calldata) (x := "target") (y := "count") hhi

private theorem decodeNoncanon {I : ExecutionEnv} (hlo : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hcanon : ¬ (targetArg I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name) (transitionSignature runTransition).paramTypes I.calldata = none := by
  simpa [runTransition, addr, uint256, abiUInt256, calldataWord, targetArg]
    using decodeCalldata_addr_uint256_none_noncanon (cd := I.calldata) (x := "target") (y := "count") hlo hhi hcanon

private theorem canonical {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hlo : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : (runSelector == I.calldata.extract 0 4) = true)
    (hcanon : (targetArg I).toNat < EVM.addressModulus)
    (haccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor nestedCallerConfig nestedCallerContract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  obtain ⟨k, C, rd⟩ := decoderEntry (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := g)
    hcode hcv hsize (by omega) hmatch
  have hdecode := decodeBody (solcDecodeLenCheckOk_4_64 hlo hhi hsize) rd
  rw [if_pos hcanon] at hdecode
  obtain ⟨k1, C1, rbody⟩ := hdecode
  have ht : (decodedLocals I).get? "target" = some (.address (AccountAddress.ofNat (targetArg I).toNat)) := by
    rw [decodedLocals, store_get_ne _ _ (by decide), store_get_self]
  have hn : (decodedLocals I).get? "count" = some (wordValue (countArg I)) := store_get_self _ _ _
  have htarget : EVM.address (AccountAddress.ofNat (targetArg I).toNat) = AccountAddress.ofUInt256 (targetArg I) := by
    apply Fin.ext
    show (targetArg I).toNat % EVM.addressModulus % AccountAddress.size =
      (targetArg I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  have hb := bodyRefines (g := g) (s0 := initState cA gh bl σ_evm σ₀ g A I)
    (world := (cA, σ_evm)) (k := k1) (C := C1) (sel := selectorWord I)
    (f := {contract := nestedCallerContract, locals := decodedLocals I})
    (e := initState cA gh bl σ_solm σ₀ g A I)
    hcv hperm rfl ht hn (solcAddrMask_clean_left hcanon) htarget
  exact hb.toRuntimeEquivalenceFor rbody (CallStateRel.initState haccounts) hcode
    (selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some rfl rfl
      (by rw [dispatch.eq, if_pos hmatch])) (decodeArgs hlo hhi hcanon)

/-- Runtime equivalence for every input, gas budget and related account maps.
The bound on count is enforced by both programs, not imposed on this theorem. -/
theorem nestedCallerCorrect : runtimeEquivalence nestedCallerConfig nestedCallerBytecode nestedCallerContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm haccounts => ?_⟩
  by_cases hcv : I.weiValue = ⟨0⟩
  · by_cases hfour : 4 ≤ I.calldata.size
    · by_cases hmatch : (runSelector == I.calldata.extract 0 4) = true
      · have hd : dispatchMsg nestedCallerContract I.calldata = some runTransition := by
          rw [dispatch.eq, if_pos hmatch]
        obtain ⟨k, C, rd⟩ := decoderEntry (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (g := Sat256.ofUInt256 g) hcode hcv hsize hfour hmatch
        by_cases hlo : 68 ≤ I.calldata.size
        · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
          · by_cases hcanon : (targetArg I).toNat < EVM.addressModulus
            · exact canonical (g := Sat256.ofUInt256 g) hcode hcv hsize hperm hlo hhi hmatch hcanon haccounts
            · have hr := decodeBody (solcDecodeLenCheckOk_4_64 hlo hhi hsize) rd
              rw [if_neg hcanon] at hr
              exact hr.reEquivDecodingFailed hcode hd (decodeNoncanon hlo hhi hcanon)
          · have hr := badLength (solcDecodeLenCheckHuge_4_64 (by omega) hsize) rd
            exact hr.reEquivDecodingFailed hcode hd (decodeHuge (by omega))
        · have hr := badLength (solcDecodeLenCheckShort_4_64 hfour (by omega) hsize) rd
          exact hr.reEquivDecodingFailed hcode hd (decodeShort hfour (by omega))
      · have hm : (runSelector == I.calldata.extract 0 4) = false := by simpa using hmatch
        exact (wrongSelector (g := Sat256.ofUInt256 g) hcode hcv hsize hfour hm).reEquivNoDispatch
          hcode (dispatch.none_nomatch hm)
    · exact (shortSelector (g := Sat256.ofUInt256 g) hcode hcv (by omega)).reEquivNoDispatch
        hcode (dispatch.none_short (by omega))
  · exact (nonPayable (g := Sat256.ofUInt256 g) hcode hcv).reEquivNonPayable hcode rfl rfl
      (fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hcv))

end NestedCaller
