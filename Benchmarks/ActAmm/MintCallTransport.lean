import Benchmarks.ActAmm.MintErrorRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

private theorem ammExtensional_of_equiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize h addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem ammEquiv_of_extensional {σ τ : AccountMap}
    (h : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize h addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Transport a token call while retaining equality of its output substate. -/
theorem ammTypedCallTransport
    {evmE evmS evmE' : EVM.State} {tgt : EVM.Address}
    {name : Ident} {args : List Value} {z : Bool} {out : ByteArray}
    {callPerm : Bool}
    (hcall : typedCallViaEVM config evmE tgt name 0 args (z, evmE', out) callPerm)
    (hAccounts : accountMapEquiv evmE.accountMap evmS.accountMap)
    (hOriginal : evmE.σ₀ = evmS.σ₀)
    (hCreated : evmS.createdAccounts = evmE.createdAccounts)
    (hGenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hBlocks : evmS.blocks = evmE.blocks)
    (hSubstate : evmS.substate = evmE.substate)
    (hEnv : evmS.executionEnv = evmE.executionEnv) :
    ∃ (σS' : AccountMap),
      typedCallViaEVM config evmS tgt name 0 args
        (z, { evmS with
              accountMap := σS'
              substate := evmE'.substate
              createdAccounts := evmE'.createdAccounts }, out) callPerm ∧
      accountMapEquiv evmE'.accountMap σS' := by
  obtain ⟨calldata, hencode, hraw⟩ := hcall
  have hExt : accountMapExtensionalEq evmE.accountMap evmS.accountMap :=
    ammExtensional_of_equiv hAccounts
  cases hraw with
  | callMade hvalue hTheta hevm' hvalue' hdepth =>
    obtain ⟨callGas, A_in, hTheta⟩ := hTheta
    rename_i valueWord cA' σ' g' A'
    generalize hthetaS :
      Ethereum.EVM.Θ evmS.executionEnv.blobVersionedHashes evmS.createdAccounts
        evmS.genesisBlockHeader evmS.blocks evmS.accountMap evmS.σ₀ A_in
        evmS.executionEnv.codeOwner evmS.executionEnv.sender tgt
        (toExecute evmS.accountMap tgt) callGas
        (UInt256.ofNat evmS.executionEnv.gasPrice) valueWord valueWord calldata
        (evmS.executionEnv.depth + 1) evmS.executionEnv.header callPerm = thetaRes
    have hcode : toExecute evmE.accountMap tgt = toExecute evmS.accountMap tgt :=
      accountMapExtensionalEq_toExecute hExt tgt
    have hthetaS' :
      Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
        evmE.genesisBlockHeader evmE.blocks evmS.accountMap evmE.σ₀ A_in
        evmE.executionEnv.codeOwner evmE.executionEnv.sender tgt
        (toExecute evmE.accountMap tgt) callGas
        (UInt256.ofNat evmE.executionEnv.gasPrice) valueWord valueWord calldata
        (evmE.executionEnv.depth + 1) evmE.executionEnv.header callPerm =
        (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
          thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
      rw [← hthetaS]
      rw [hCreated, ← hOriginal, hGenesis, hBlocks, hEnv, hcode]
    let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
    have hrel :=
      (accountMap_extensionality_of_Theta_and_Lambda
        (blobVersionedHashes := evmE.executionEnv.blobVersionedHashes)
        (createdAccounts := evmE.createdAccounts)
        (genesisBlockHeader := evmE.genesisBlockHeader)
        (blocks := evmE.blocks)
        (σ₁ := evmE.accountMap) (σ₂ := evmS.accountMap) (σ₀ := evmE.σ₀)
        (A := A_in) (s := evmE.executionEnv.codeOwner)
        (o := evmE.executionEnv.sender) (r := tgt) (g := callGas)
        (p := UInt256.ofNat evmE.executionEnv.gasPrice)
        (v := valueWord) (v' := valueWord) (d := calldata)
        (i := ByteArray.empty) (ζ := none) (H := evmE.executionEnv.header)
        (w := callPerm) a1 a1 (toExecute evmE.accountMap tgt)
        cA' thetaRes.1 σ' thetaRes.2.1 g' thetaRes.2.2.1
        A' thetaRes.2.2.2.1 z thetaRes.2.2.2.2.1
        out thetaRes.2.2.2.2.2 (evmE.executionEnv.depth + 1)
        hExt).1 hTheta.symm hthetaS'
    have hCreated' : evmE'.createdAccounts = cA' := by simp [hevm']
    have hSubstate' : evmE'.substate = thetaRes.2.2.2.1 := by
      simpa [hevm'] using hrel.2.2.1
    have hthetaCall :
      (evmE'.createdAccounts, thetaRes.2.1, thetaRes.2.2.1,
        evmE'.substate, z, out) =
        Ethereum.EVM.Θ evmS.executionEnv.blobVersionedHashes evmS.createdAccounts
          evmS.genesisBlockHeader evmS.blocks evmS.accountMap evmS.σ₀ A_in
          evmS.executionEnv.codeOwner evmS.executionEnv.sender tgt
          (toExecute evmS.accountMap tgt) callGas
          (UInt256.ofNat evmS.executionEnv.gasPrice) valueWord valueWord calldata
          (evmS.executionEnv.depth + 1) evmS.executionEnv.header callPerm := by
      rw [hCreated', hrel.1, hSubstate', hrel.2.2.2.1,
        hrel.2.2.2.2.1]
      exact hthetaS.symm
    refine ⟨thetaRes.2.1, ?_, ?_⟩
    · refine ⟨calldata, hencode, ?_⟩
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, hthetaCall⟩ rfl (by
          rw [hEnv]
          rw [← accountMapExtensionalEq_balanceOf hExt evmE.executionEnv.codeOwner]
          exact hvalue') (by rw [hEnv]; exact hdepth)
    · simpa [hevm'] using
        ammEquiv_of_extensional hrel.2.2.2.2.2
  | callNotMade hsubstate hevm' hvalue =>
    refine ⟨evmS.accountMap, ?_, ?_⟩
    · refine ⟨calldata, hencode, ?_⟩
      apply callViaEVM.callNotMade (perm := callPerm)
      · rfl
      · simp [hevm', hCreated, hsubstate, hSubstate, State.addAccessedAccount]
      · rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf hExt evmE.executionEnv.codeOwner]
        exact hvalue
    · simpa [hevm'] using hAccounts


/-- Static-call specialization of `ammTypedCallTransport`. -/
theorem ammTypedCallStaticTransport
    {evmE evmS evmE' : EVM.State} {tgt : EVM.Address}
    {name : Ident} {args : List Value} {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM config evmE tgt name 0 args (z, evmE', out) false)
    (hAccounts : accountMapEquiv evmE.accountMap evmS.accountMap)
    (hOriginal : evmE.σ₀ = evmS.σ₀)
    (hCreated : evmS.createdAccounts = evmE.createdAccounts)
    (hGenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hBlocks : evmS.blocks = evmE.blocks)
    (hSubstate : evmS.substate = evmE.substate)
    (hEnv : evmS.executionEnv = evmE.executionEnv) :
    ∃ (σS' : AccountMap),
      typedCallViaEVM config evmS tgt name 0 args
        (z, { evmS with
              accountMap := σS'
              substate := evmE'.substate
              createdAccounts := evmE'.createdAccounts }, out) false ∧
      accountMapEquiv evmE'.accountMap σS' :=
  ammTypedCallTransport hcall hAccounts hOriginal hCreated hGenesis hBlocks
    hSubstate hEnv

end Benchmarks.ActAmm
