import Benchmarks.ActAmm4.SwapArithmeticBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 10000000 in
theorem amm4SwapSuccessFromBalanceTrace
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA4 : Batteries.RBSet AccountAddress compare}
    {σE4 σS4 : AccountMap} {A4 : Substate}
    {out0 out1 mem ret : ByteArray} {aw : UInt256}
    {sel : UInt256} {k C : Nat} {b0 b1 : Bool}
    (hcode : I.code = amm4Bytecode)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata =
      some (amm4SwapStore I))
    (hperm : I.perm = true)
    (hσ4 : accountMapEquiv σE4 σS4)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      amm4SwapSourcePrefixBalance1
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σS4, substate := A4, createdAccounts := cA4 }))
    (hlo0 : 32 ≤ out0.size) (hlo1 : 32 ≤ out1.size)
    (hle0 : (amm4SwapAmount0Word I).toNat ≤
      (solcSlotWord σE4 I ⟨5⟩).toNat)
    (hle1 : (amm4SwapAmount1Word I).toNat ≤
      (solcSlotWord σE4 I ⟨6⟩).toNat)
    (hinput : 0 < amm4SwapInput0Nat
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σS4, substate := A4, createdAccounts := cA4 }
        I out0 ∨
      0 < amm4SwapInput1Nat
        { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σS4, substate := A4, createdAccounts := cA4 }
        I out1)
    (hfitOld : (solcSlotWord σE4 I ⟨5⟩).toNat *
      (solcSlotWord σE4 I ⟨6⟩).toNat < UInt256.size)
    (hfitNew : fromByteArrayBigEndian (out0.extract 0 32) *
      fromByteArrayBigEndian (out1.extract 0 32) < UInt256.size)
    (hk : (solcSlotWord σE4 I ⟨5⟩).toNat *
      (solcSlotWord σE4 I ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (out0.extract 0 32) *
      fromByteArrayBigEndian (out1.extract 0 32))
    (rd : RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨3128⟩
      [UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32)),
        UInt256.ofNat (fromByteArrayBigEndian (out0.extract 0 32)),
        amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      mem aw ret (cA4, σE4) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE4 : EVM.State :=
    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σE4, substate := A4, createdAccounts := cA4 }
  let evmS4 : EVM.State :=
    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
      accountMap := σS4, substate := A4, createdAccounts := cA4 }
  have hState4 : EVMStateEquiv evmE4 evmS4 := by
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · rfl
    · simpa [evmE4, evmS4, initState] using hσ4
  have hslot5 : solcSlotWord σE4 I ⟨5⟩ =
      Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨5⟩ := by
    have h := hState4.storageLoad_codeOwner ⟨5⟩
    simpa [evmE4, solcSlotWord, codeOwnerStorageWord, initState]
      using h
  have hslot6 : solcSlotWord σE4 I ⟨6⟩ =
      Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨6⟩ := by
    have h := hState4.storageLoad_codeOwner ⟨6⟩
    simpa [evmE4, solcSlotWord, codeOwnerStorageWord, initState]
      using h
  let v0 : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (out0.extract 0 32))
  let v1 : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (out1.extract 0 32))
  let a0 : UInt256 := UInt256.ofNat (amm4SwapInput0Nat evmS4 I out0)
  let a1 : UInt256 := UInt256.ofNat (amm4SwapInput1Nat evmS4 I out1)
  have hv0 : v0.toNat = fromByteArrayBigEndian (out0.extract 0 32) :=
    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo0)
  have hv1 : v1.toNat = fromByteArrayBigEndian (out1.extract 0 32) :=
    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo1)
  have hcase0 := amm4SwapInput0WordCase hslot5 hlo0 hle0
  have hcase1 := amm4SwapInput1WordCase hslot6 hlo1 hle1
  have hinput0fit : amm4SwapInput0Nat evmS4 I out0 < UInt256.size := by
    unfold amm4SwapInput0Nat
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (fromByteArrayBigEndian_extract0_32_lt hlo0)
    · decide
  have hinput1fit : amm4SwapInput1Nat evmS4 I out1 < UInt256.size := by
    unfold amm4SwapInput1Nat
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _)
        (fromByteArrayBigEndian_extract0_32_lt hlo1)
    · decide
  have ha0 : a0.toNat = amm4SwapInput0Nat evmS4 I out0 :=
    ulit_toNat' _ hinput0fit
  have ha1 : a1.toNat = amm4SwapInput1Nat evmS4 I out1 :=
    ulit_toNat' _ hinput1fit
  have hposE : 0 < a0.toNat ∨ 0 < a1.toNat := by
    rw [ha0, ha1]
    exact hinput
  have hfitNewE : v0.toNat * v1.toNat < UInt256.size := by
    rw [hv0, hv1]
    exact hfitNew
  have hkE : (solcSlotWord σE4 I ⟨5⟩).toNat *
      (solcSlotWord σE4 I ⟨6⟩).toNat ≤ v0.toNat * v1.toNat := by
    rw [hv0, hv1]
    exact hk
  have hret := amm4SwapX_successFromBalances
    (a0 := a0) (a1 := a1) (v0 := v0) (v1 := v1)
    (q0 := amm4SwapAmount0Word I) (q1 := amm4SwapAmount1Word I)
    (by simpa [v0, v1] using rd) hperm hle0 hle1
    (by simpa [a0, v0] using hcase0)
    (by simpa [a1, v1] using hcase1)
    hposE hfitOld hfitNewE hkE
  have hbody := amm4SwapSourceSuccessFromBalances I b0 b1 out0 out1
    (by simpa [evmS4] using hprefix) hlo0 hlo1
    (by rw [← hslot5]; exact hle0)
    (by rw [← hslot6]; exact hle1)
    hinput (by simpa [amm4SwapNewProductNat] using hfitNew)
    (by
      change (Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
        (Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨6⟩).toNat <
        UInt256.size
      rw [← hslot5, ← hslot6]
      exact hfitOld)
    (by
      change (Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
        (Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner ⟨6⟩).toNat ≤
        fromByteArrayBigEndian (out0.extract 0 32) *
          fromByteArrayBigEndian (out1.extract 0 32)
      rw [← hslot5, ← hslot6]
      exact hk)
  let evmE5 := amm4SwapAfterReserve1
    (amm4SwapAfterReserve0 evmE4 out0) out1
  let evmS5 := amm4SwapAfterReserve1
    (amm4SwapAfterReserve0 evmS4 out0) out1
  have hState5 : EVMStateEquiv evmE5 evmS5 := by
    simpa [evmE5, evmS5, amm4SwapAfterReserve0,
      amm4SwapAfterReserve1] using
      ((hState4.storageStore_codeOwner ⟨5⟩ rfl).storageStore_codeOwner
        ⟨6⟩ rfl)
  have hmapE5 : evmE5.accountMap =
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σE4 ⟨5⟩ v0) ⟨6⟩ v1 := by
    simp [evmE5, amm4SwapAfterReserve1, amm4SwapAfterReserve0,
      storageStore_accountMap, storageStore_executionEnv,
      evmE4, v0, v1, amm4SwapReserve0Word,
      amm4SwapReserve1Word, initState]
  have hcreated : cA4 = evmE5.createdAccounts := by
    simp [evmE5, amm4SwapAfterReserve1, amm4SwapAfterReserve0,
      storageStore_createdAccounts, evmE4]
  have henc : returnEquiv ByteArray.empty none
      swapTransition.returnType := by
    rw [show swapTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdec
    (by simpa [evmS5, evmS4] using hbody)
    hcreated (accountMapEquiv.of_eq hmapE5.symm) hState5 henc

end Benchmarks.ActAmm4
