import Benchmarks.ActAmm4.SwapSuccessBridge
import Benchmarks.ActAmm4.SwapSourceArithmeticReverts
import Benchmarks.ActAmm4.SwapArithmeticRevertTrace
import Benchmarks.ActAmm4.SwapInputRevert
import Benchmarks.ActAmm4.SwapSourceProductReverts
import Benchmarks.ActAmm4.SwapKRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000

/-- The swap suffix after both balance calls have decoded. -/
theorem amm4SwapArithmeticCore
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
          accountMap := σS4, substate := A4,
          createdAccounts := cA4 }))
    (hlo0 : 32 ≤ out0.size) (hlo1 : 32 ≤ out1.size)
    (haw : 3 ≤ aw.toNat)
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
      Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner
        ⟨5⟩ := by
    have h := hState4.storageLoad_codeOwner ⟨5⟩
    simpa [evmE4, solcSlotWord, codeOwnerStorageWord,
      initState] using h
  have hslot6 : solcSlotWord σE4 I ⟨6⟩ =
      Solm.EVM.storageLoad evmS4 evmS4.executionEnv.codeOwner
        ⟨6⟩ := by
    have h := hState4.storageLoad_codeOwner ⟨6⟩
    simpa [evmE4, solcSlotWord, codeOwnerStorageWord,
      initState] using h
  by_cases hle0 : (amm4SwapAmount0Word I).toNat ≤
      (solcSlotWord σE4 I ⟨5⟩).toNat
  · let v0 : UInt256 := UInt256.ofNat
      (fromByteArrayBigEndian (out0.extract 0 32))
    let v1 : UInt256 := UInt256.ofNat
      (fromByteArrayBigEndian (out1.extract 0 32))
    let a0 : UInt256 := UInt256.ofNat
      (amm4SwapInput0Nat evmS4 I out0)
    have hcase0 := amm4SwapInput0WordCase hslot5 hlo0 hle0
    have hres0S := amm4SwapSourceReserve0Ok I b0 b1 out0 out1
      hprefix (by rw [← hslot5]; exact hle0)
    have hin0S := amm4SwapSourceAmount0InCases I b0 b1
      out0 out1 hres0S hlo0
    obtain ⟨_, _, rd3142⟩ := amm4SwapX_reserve0AfterOut
      (by simpa [v0, v1] using rd) hle0
    have rd3183 : ∃ k' C', RD amm4Bytecode I
        (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨3183⟩
        [a0, v1, v0, amm4SwapToWord I,
          amm4SwapAmount1Word I, amm4SwapAmount0Word I,
          ⟨349⟩, sel]
        mem aw ret (cA4, σE4) k' C' := by
      rcases hcase0 with ⟨hgt, ha0⟩ | ⟨hle, ha0⟩
      · obtain ⟨_, _, rd3154⟩ :=
          amm4SwapX_amount0InPositiveBranch rd3142 hgt
        have hrd := amm4SwapX_amount0InPositive rd3154 hle0 hgt
        simpa [a0, v0, v1, ha0] using hrd
      · have hrd := amm4SwapX_amount0InZero rd3142 hle
        simpa [a0, v0, v1, ha0] using hrd
    obtain ⟨_, _, rd3183⟩ := rd3183
    by_cases hle1 : (amm4SwapAmount1Word I).toNat ≤
        (solcSlotWord σE4 I ⟨6⟩).toNat
    · let a1 : UInt256 := UInt256.ofNat
        (amm4SwapInput1Nat evmS4 I out1)
      have hcase1 := amm4SwapInput1WordCase hslot6 hlo1 hle1
      have hres1S := amm4SwapSourceReserve1Ok I b0 b1
        out0 out1 (amm4SwapInput0Nat evmS4 I out0)
        (by simpa [evmS4] using hin0S)
        (by rw [← hslot6]; exact hle1)
      have hin1S := amm4SwapSourceAmount1InCases I b0 b1
        out0 out1 hres1S hlo1
      obtain ⟨_, _, rd3197⟩ := amm4SwapX_reserve1AfterOut
        rd3183 hle1
      have rd3238 : ∃ k' C', RD amm4Bytecode I
          (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          ⟨3238⟩
          [a1, a0, v1, v0, amm4SwapToWord I,
            amm4SwapAmount1Word I, amm4SwapAmount0Word I,
            ⟨349⟩, sel]
          mem aw ret (cA4, σE4) k' C' := by
        rcases hcase1 with ⟨hgt, ha1⟩ | ⟨hle, ha1⟩
        · obtain ⟨_, _, rd3209⟩ :=
            amm4SwapX_amount1InPositiveBranch rd3197 hgt
          have hrd := amm4SwapX_amount1InPositive rd3209 hle1 hgt
          simpa [a1, v0, v1, ha1] using hrd
        · have hrd := amm4SwapX_amount1InZero rd3197 hle
          simpa [a1, v0, v1, ha1] using hrd
      obtain ⟨_, _, rd3238⟩ := rd3238
      by_cases hpos : 0 < amm4SwapInput0Nat evmS4 I out0 ∨
          0 < amm4SwapInput1Nat evmS4 I out1
      · have hinput0fit :
            amm4SwapInput0Nat evmS4 I out0 < UInt256.size := by
          unfold amm4SwapInput0Nat
          split_ifs
          · exact lt_of_le_of_lt (Nat.sub_le _ _)
              (fromByteArrayBigEndian_extract0_32_lt hlo0)
          · decide
        have hinput1fit :
            amm4SwapInput1Nat evmS4 I out1 < UInt256.size := by
          unfold amm4SwapInput1Nat
          split_ifs
          · exact lt_of_le_of_lt (Nat.sub_le _ _)
              (fromByteArrayBigEndian_extract0_32_lt hlo1)
          · decide
        have hposE : 0 < a0.toNat ∨ 0 < a1.toNat := by
          rw [show a0.toNat = amm4SwapInput0Nat evmS4 I out0
            from ulit_toNat' _ hinput0fit,
            show a1.toNat = amm4SwapInput1Nat evmS4 I out1
            from ulit_toNat' _ hinput1fit]
          exact hpos
        have hinputS := amm4SwapSourceInputGuardOk I b0 b1
          out0 out1 (amm4SwapInput0Nat evmS4 I out0)
          (amm4SwapInput1Nat evmS4 I out1)
          (by simpa [evmS4] using hin1S) hpos
        obtain ⟨_, _, rd3313⟩ :=
          amm4SwapX_inputGuardOk rd3238 hposE
        by_cases hfitOld :
            (solcSlotWord σE4 I ⟨5⟩).toNat *
              (solcSlotWord σE4 I ⟨6⟩).toNat < UInt256.size
        · obtain ⟨_, _, rd3329⟩ :=
            amm4SwapX_oldProduct rd3313 hfitOld
          by_cases hfitNew :
              amm4SwapNewProductNat out0 out1 < UInt256.size
          · have hnewS := amm4SwapSourceNewProductOk I b0 b1
              out0 out1 (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4, amm4SwapInputStore] using hinputS)
              hfitNew
            have hfitOldS : amm4SwapOldProductNat evmS4 <
                UInt256.size := by
              change (Solm.EVM.storageLoad evmS4
                evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
                (Solm.EVM.storageLoad evmS4
                  evmS4.executionEnv.codeOwner ⟨6⟩).toNat < _
              rw [← hslot5, ← hslot6]
              exact hfitOld
            have holdS := amm4SwapSourceOldProductOk I b0 b1
              out0 out1 (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4] using hnewS) hfitOldS
            have hv0 : v0.toNat =
                fromByteArrayBigEndian (out0.extract 0 32) :=
              ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo0)
            have hv1 : v1.toNat =
                fromByteArrayBigEndian (out1.extract 0 32) :=
              ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo1)
            have hfitNewE : v0.toNat * v1.toNat < UInt256.size := by
              rw [hv0, hv1]
              exact hfitNew
            obtain ⟨_, _, rd3341⟩ :=
              amm4SwapX_newProduct rd3329 hfitNewE
            by_cases hk : amm4SwapOldProductNat evmS4 ≤
                amm4SwapNewProductNat out0 out1
            · have hkE :
                  (solcSlotWord σE4 I ⟨5⟩).toNat *
                    (solcSlotWord σE4 I ⟨6⟩).toNat ≤
                  fromByteArrayBigEndian (out0.extract 0 32) *
                    fromByteArrayBigEndian (out1.extract 0 32) := by
                change (Solm.EVM.storageLoad evmS4
                  evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
                  (Solm.EVM.storageLoad evmS4
                    evmS4.executionEnv.codeOwner ⟨6⟩).toNat ≤
                  fromByteArrayBigEndian (out0.extract 0 32) *
                    fromByteArrayBigEndian (out1.extract 0 32) at hk
                rw [← hslot5, ← hslot6] at hk
                exact hk
              exact amm4SwapSuccessFromBalanceTrace hcode
                hdispatch hdec hperm hσ4 hprefix hlo0 hlo1
                hle0 hle1 hpos hfitOld
                (by simpa [amm4SwapNewProductNat] using hfitNew)
                hkE rd
            · have hkS : amm4SwapNewProductNat out0 out1 <
                  amm4SwapOldProductNat evmS4 := by omega
              have hbody := amm4SwapSourceKGuardRevert
                I b0 b1 out0 out1
                (amm4SwapInput0Nat evmS4 I out0)
                (amm4SwapInput1Nat evmS4 I out1)
                (by simpa [evmS4] using holdS) hkS
              have hprodOld :
                  (UInt256.mul (solcSlotWord σE4 I ⟨5⟩)
                    (solcSlotWord σE4 I ⟨6⟩)).toNat =
                  (solcSlotWord σE4 I ⟨5⟩).toNat *
                    (solcSlotWord σE4 I ⟨6⟩).toNat := by
                rw [u256_mul_toNat, Nat.mod_eq_of_lt hfitOld]
              have hprodNew : (UInt256.mul v0 v1).toNat =
                  v0.toNat * v1.toNat := by
                rw [u256_mul_toNat, Nat.mod_eq_of_lt hfitNewE]
              have hkE : v0.toNat * v1.toNat <
                  (solcSlotWord σE4 I ⟨5⟩).toNat *
                    (solcSlotWord σE4 I ⟨6⟩).toNat := by
                change fromByteArrayBigEndian (out0.extract 0 32) *
                  fromByteArrayBigEndian (out1.extract 0 32) <
                  (Solm.EVM.storageLoad evmS4
                    evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
                  (Solm.EVM.storageLoad evmS4
                    evmS4.executionEnv.codeOwner ⟨6⟩).toNat at hkS
                rw [hv0, hv1, hslot5, hslot6]
                exact hkS
              have hrev := amm4SwapX_kGuardRevert rd3341
                (by rw [hprodOld, hprodNew]; exact hkE)
              exact hrev.reEquivExecutionRevert hcode hdispatch
                hdec hbody
          · have hoverNew : UInt256.size ≤
                amm4SwapNewProductNat out0 out1 := by omega
            have hbody := amm4SwapSourceNewProductOverflow
              I b0 b1 out0 out1
              (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4, amm4SwapInputStore] using hinputS)
              hoverNew
            have hv0 : v0.toNat =
                fromByteArrayBigEndian (out0.extract 0 32) :=
              ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo0)
            have hv1 : v1.toNat =
                fromByteArrayBigEndian (out1.extract 0 32) :=
              ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo1)
            have hrev := amm4SwapX_newProductOverflow rd3329
              (by rw [hv0, hv1]; exact hoverNew) haw
            exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
        · have hoverOld : UInt256.size ≤
              (solcSlotWord σE4 I ⟨5⟩).toNat *
                (solcSlotWord σE4 I ⟨6⟩).toNat := by omega
          have hrev := amm4SwapX_oldProductOverflow
            rd3313 hoverOld haw
          by_cases hfitNew : amm4SwapNewProductNat out0 out1 <
              UInt256.size
          · have hnewS := amm4SwapSourceNewProductOk I b0 b1
              out0 out1 (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4, amm4SwapInputStore] using hinputS)
              hfitNew
            have hoverOldS : UInt256.size ≤
                amm4SwapOldProductNat evmS4 := by
              change UInt256.size ≤
                (Solm.EVM.storageLoad evmS4
                  evmS4.executionEnv.codeOwner ⟨5⟩).toNat *
                (Solm.EVM.storageLoad evmS4
                  evmS4.executionEnv.codeOwner ⟨6⟩).toNat
              rw [← hslot5, ← hslot6]
              exact hoverOld
            have hbody := amm4SwapSourceOldProductOverflow
              I b0 b1 out0 out1
              (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4] using hnewS) hoverOldS
            exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
          · have hoverNew : UInt256.size ≤
                amm4SwapNewProductNat out0 out1 := by omega
            have hbody := amm4SwapSourceNewProductOverflow
              I b0 b1 out0 out1
              (amm4SwapInput0Nat evmS4 I out0)
              (amm4SwapInput1Nat evmS4 I out1)
              (by simpa [evmS4, amm4SwapInputStore] using hinputS)
              hoverNew
            exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
      · have hzero0 : amm4SwapInput0Nat evmS4 I out0 = 0 := by
          omega
        have hzero1 : amm4SwapInput1Nat evmS4 I out1 = 0 := by
          omega
        have hbody := amm4SwapSourceInputGuardRevert I b0 b1
          out0 out1 (amm4SwapInput0Nat evmS4 I out0)
          (amm4SwapInput1Nat evmS4 I out1)
          (by simpa [evmS4] using hin1S) hzero0 hzero1
        have hrev := amm4SwapX_inputGuardRevert
          rd3238 (by simp only [a0, hzero0]; decide)
          (by simp only [a1, hzero1]; decide)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
    · have hunder : (solcSlotWord σE4 I ⟨6⟩).toNat <
          (amm4SwapAmount1Word I).toNat := by omega
      have hbody := amm4SwapSourceReserve1Underflow
        I b0 b1 out0 out1 (amm4SwapInput0Nat evmS4 I out0)
        (by simpa [evmS4] using hin0S)
        (by rw [← hslot6]; exact hunder)
      have hrev := amm4SwapX_reserve1Underflow rd3183 hunder haw
      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
  · have hunder : (solcSlotWord σE4 I ⟨5⟩).toNat <
        (amm4SwapAmount0Word I).toNat := by omega
    have hbody := amm4SwapSourceReserve0Underflow I b0 b1
      out0 out1 hprefix (by rw [← hslot5]; exact hunder)
    have hrev := amm4SwapX_reserve0Underflow rd hunder haw
    exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody

end Benchmarks.ActAmm4
