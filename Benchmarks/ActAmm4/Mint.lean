import Benchmarks.ActAmm4.MintDecodeRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintBodyCore_zeroSupply
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hzero : solcSlotWord σ_evm I ⟨0⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨275⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using
      EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hzeroS : Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩ =
      ⟨0⟩ := by
    rw [show Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩ =
      Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨0⟩ from
        (hσ.storageLoad_codeOwner ⟨0⟩).symm]
    simpa [evmE, solcSlotWord, codeOwnerStorageWord] using hzero
  have hbody := amm4MintSourceZeroSupply evmS I
    (by simpa [evmS, initState] using hwv) hzeroS
  exact (amm4MintX_zeroSupply (g := Sat256.ofUInt256 g)
      hsz36 hsize hbig hcanon hzero hreach)
    |>.reEquivExecutionRevert hcode (amm4Dispatch_mint hsel)
      (amm4Decode_mint_ok hsz36 hbig hcanon) hbody

/-- The mint wrapper, entered at PC 275, refines its Solm transition. -/
theorem amm4MintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨275⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4MintSelector_size hsel
  have hdispatch := amm4Dispatch_mint hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (amm4MintToWord I).toNat < EVM.addressModulus
      · by_cases hzero : solcSlotWord σ_evm I ⟨0⟩ = ⟨0⟩
        · exact amm4MintBodyCore_zeroSupply hcode hsize hwv hsel
            hsz36 hbig hcanon hzero hreach hAccounts
        · have hframe := amm4MintX_token0FrameFromEntry
            hsz36 hsize hbig hcanon hzero hreach
          by_cases hdepth : I.depth = 1024
          · have hslot : solcSlotWord σ_evm I ⟨0⟩ =
                solcSlotWord σ_solm I ⟨0⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
            have hnonzeroS : solcSlotWord σ_solm I ⟨0⟩ ≠ ⟨0⟩ := by
              intro hz
              exact hzero (hslot.trans hz)
            have hbody := amm4MintSourceToken0DepthRevert
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) hwv hdepth hnonzeroS
            exact (amm4MintX_token0DepthRevert hdepth hframe).reEquivExecutionRevert
              hcode hdispatch (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
          · have hdepthLt : I.depth.val < 1024 := by
              have hlt := I.depth.isLt
              omega
            obtain ⟨cA1, σE1, z0, o1, A1, k1, C1, rd1595, hcallE0,
                ho1size, ho1bound⟩ :=
              amm4MintX_token0Staticcall hdepthLt hframe
            let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
            let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            obtain ⟨σS1, hcallS0, hσ1⟩ :=
              amm4TypedCallStaticTransport (evmS := evmS) hcallE0
                (by simpa [evmE, evmS, initState] using hAccounts)
                (by simp [evmE, evmS, initState])
                (by simp [evmE, evmS, initState])
                (by simp [evmE, evmS, initState])
                (by simp [evmE, evmS, initState])
                (by simp [evmE, evmS, initState])
                (by simp [evmE, evmS, initState])
            have hslot0 : solcSlotWord σ_evm I ⟨0⟩ =
                solcSlotWord σ_solm I ⟨0⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
            have hnonzeroS : solcSlotWord σ_solm I ⟨0⟩ ≠ ⟨0⟩ := by
              intro hz
              exact hzero (hslot0.trans hz)
            have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
                solcSlotWord σ_solm I ⟨3⟩ := by
              simpa [solcSlotWord, codeOwnerStorageWord] using
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
            have hword0 : amm4MintToken0Word σ_evm I =
                amm4MintToken0Word σ_solm I := by
              exact congrArg (fun w => UInt256.land w solcAddrMask) hslot3
            have htarget0 :
                (EVM.address (AccountAddress.ofUInt256
                  (UInt256.land (Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val) =
                AccountAddress.ofUInt256 (amm4MintToken0Word σ_evm I) := by
              rw [hword0]
              change EVM.address (AccountAddress.ofUInt256
                (amm4MintToken0Word σ_solm I)).val = _
              apply Fin.ext
              change (AccountAddress.ofUInt256
                (amm4MintToken0Word σ_solm I)).val % EVM.twoPow 160 = _
              exact Nat.mod_eq_of_lt
                (AccountAddress.ofUInt256 (amm4MintToken0Word σ_solm I)).isLt
            have hcallS0' : typedCallViaEVM config evmS
                (EVM.address (AccountAddress.ofUInt256
                  (UInt256.land (Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
                "balanceOf" 0 [.address evmS.executionEnv.codeOwner]
                (z0, { evmS with
                  accountMap := σS1
                  substate := A1
                  createdAccounts := cA1 }, o1) false := by
              rw [htarget0]
              simpa [evmS, initState] using hcallS0
            by_cases hz0 : z0 = false
            · have rdFail := by
                simpa [hz0] using rd1595
              have hrev := amm4MintX_token0CallFailed rdFail ho1size
                (by simp only [List.length_cons, List.length_nil]; omega)
              have hcallSfail := by simpa only [hz0] using hcallS0'
              have hbody := amm4MintSourceToken0CallFailed evmS
                { evmS with
                  accountMap := σS1
                  substate := A1
                  createdAccounts := cA1 }
                I o1 (by simpa [evmS, initState] using hwv)
                (by simpa [evmS, solcSlotWord, codeOwnerStorageWord,
                  initState] using hnonzeroS) hcallSfail
              exact hrev.reEquivExecutionRevert hcode hdispatch
                (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
            · have hz0true : z0 = true := by cases z0 <;> simp_all
              have rdSuccess := by
                simpa [hz0true, amm4MintToken0PostCallMem] using rd1595
              have h1614 := amm4MintX_token0CallSucceeded rdSuccess
              by_cases hshort0 : o1.size < 32
              · obtain ⟨_, _, rd1614⟩ := h1614
                obtain ⟨_, _, rd5415⟩ :=
                  amm4MintX_token0ShortToDecoder hshort0 rd1614
                have hrev := amm4MintX_token0DecodeShortReverts hshort0 rd5415
                have hcallStrue := by simpa only [hz0true] using hcallS0'
                have hbody := amm4MintSourceToken0DecodeShort evmS
                  { evmS with
                    accountMap := σS1
                    substate := A1
                    createdAccounts := cA1 }
                  I o1 (by simpa [evmS, initState] using hwv)
                  (by simpa [evmS, solcSlotWord, codeOwnerStorageWord,
                    initState] using hnonzeroS) hshort0 hcallStrue
                exact hrev.reEquivExecutionRevert hcode hdispatch
                  (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
              · have hlo1 : 32 ≤ o1.size := by omega
                obtain ⟨_, _, rd1614⟩ := h1614
                have hframe1 := amm4MintX_token1FrameFromFirst
                  hlo1 ho1size ho1bound rd1614
                obtain ⟨cA2, σE2, z1, o2, A2, k2, C2, rd1751,
                    hcallE1, ho2size, ho2bound⟩ :=
                  amm4MintX_token1Staticcall (A1 := A1)
                    hlo1 ho1bound hdepthLt hframe1
                let evmS1 : EVM.State := { evmS with
                  accountMap := σS1
                  substate := A1
                  createdAccounts := cA1 }
                have hσ1' : accountMapEquiv σE1 σS1 := by
                  simpa [initState] using hσ1
                obtain ⟨σS2, hcallS1, hσ2⟩ :=
                  amm4TypedCallStaticTransport (evmS := evmS1) hcallE1
                    (by simpa [evmS1, initState] using hσ1')
                    (by simp [evmS1, evmS, initState])
                    (by simp [evmS1, evmS, initState])
                    (by simp [evmS1, evmS, initState])
                    (by simp [evmS1, evmS, initState])
                    (by simp [evmS1, evmS, initState])
                    (by simp [evmS1, evmS, initState])
                have hslot4 : solcSlotWord σE1 I ⟨4⟩ =
                    solcSlotWord σS1 I ⟨4⟩ := by
                  simpa [solcSlotWord, codeOwnerStorageWord] using
                    accountMapEquiv_storage_findD hσ1' I.codeOwner ⟨4⟩ ⟨0⟩
                have hword1 : amm4MintToken1Word σE1 I =
                    amm4MintToken1Word σS1 I :=
                  congrArg (fun w => UInt256.land w solcAddrMask) hslot4
                have htarget1 :
                    (EVM.address (AccountAddress.ofUInt256
                      (UInt256.land (Solm.EVM.storageLoad evmS1
                        evmS1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val) =
                    AccountAddress.ofUInt256 (amm4MintToken1Word σE1 I) := by
                  rw [hword1]
                  change EVM.address (AccountAddress.ofUInt256
                    (amm4MintToken1Word σS1 I)).val = _
                  apply Fin.ext
                  change (AccountAddress.ofUInt256
                    (amm4MintToken1Word σS1 I)).val % EVM.twoPow 160 = _
                  exact Nat.mod_eq_of_lt
                    (AccountAddress.ofUInt256 (amm4MintToken1Word σS1 I)).isLt
                have hcallS1' : typedCallViaEVM config evmS1
                    (EVM.address (AccountAddress.ofUInt256
                      (UInt256.land (Solm.EVM.storageLoad evmS1
                        evmS1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
                    "balanceOf" 0 [.address evmS1.executionEnv.codeOwner]
                    (z1, { evmS1 with
                      accountMap := σS2
                      substate := A2
                      createdAccounts := cA2 }, o2) false := by
                  rw [htarget1]
                  simpa [evmS1, evmS, initState] using hcallS1
                have hcallS0true := by simpa only [hz0true] using hcallS0'
                let evmS2 : EVM.State := { evmS1 with
                  accountMap := σS2
                  substate := A2
                  createdAccounts := cA2 }
                by_cases hz1 : z1 = false
                · have rdFail := by simpa [hz1] using rd1751
                  have hrev := amm4MintX_token1CallFailed rdFail ho2size
                    (by simp only [List.length_cons, List.length_nil]; omega)
                  have hcallS1fail := by simpa only [hz1] using hcallS1'
                  have hbody := amm4MintSourceToken1CallFailed
                    evmS evmS1 evmS2 I o1 o2
                    (by simpa [evmS, initState] using hwv)
                    (by simpa [evmS, solcSlotWord, codeOwnerStorageWord,
                      initState] using hnonzeroS)
                    hlo1 ho1bound hcallS0true hcallS1fail
                  exact hrev.reEquivExecutionRevert hcode hdispatch
                    (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                · have hz1true : z1 = true := by cases z1 <;> simp_all
                  have rdSuccess := by
                    simpa [hz1true, amm4MintToken1PostCallMem] using rd1751
                  obtain ⟨_, _, rd1770⟩ := amm4MintX_token1CallSucceeded rdSuccess
                  obtain ⟨_, _, rd5415⟩ :=
                    amm4MintX_token1ToDecoder hlo1 ho1bound ho2size rd1770
                  by_cases hshort1 : o2.size < 32
                  · have hrev := amm4MintX_token1DecodeShortReverts
                      hlo1 ho1bound hshort1 rd5415
                    have hcallS1true := by simpa only [hz1true] using hcallS1'
                    have hbody := amm4MintSourceToken1DecodeShort
                      evmS evmS1 evmS2 I o1 o2
                      (by simpa [evmS, initState] using hwv)
                      (by simpa [evmS, solcSlotWord, codeOwnerStorageWord,
                        initState] using hnonzeroS)
                      hlo1 ho1bound hshort1 hcallS0true hcallS1true
                    exact hrev.reEquivExecutionRevert hcode hdispatch
                      (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                  · have hlo2 : 32 ≤ o2.size := by omega
                    obtain ⟨_, _, rd1801⟩ := amm4MintX_token1DecodeOk
                      hlo1 ho1bound hlo2 ho2bound rd5415
                    obtain ⟨_, _, rd1804⟩ := amm4MintX_token1Decoded rd1801
                    have hcallS1true := by simpa only [hz1true] using hcallS1'
                    have hprefix := amm4MintSourceToken1CallOk
                      evmS evmS1 evmS2 I o1 o2
                      (by simpa [evmS, initState] using hwv)
                      (by simpa [evmS, solcSlotWord, codeOwnerStorageWord,
                        initState] using hnonzeroS)
                      hlo1 ho1bound hlo2 ho2bound hcallS0true hcallS1true
                    have hσ2 : accountMapEquiv σE2 σS2 := by
                      simpa [initState] using hσ2
                    have hslot5 : solcSlotWord σE2 I ⟨5⟩ =
                        solcSlotWord σS2 I ⟨5⟩ := by
                      simpa [solcSlotWord, codeOwnerStorageWord] using
                        accountMapEquiv_storage_findD hσ2 I.codeOwner ⟨5⟩ ⟨0⟩
                    let v0 : UInt256 :=
                      UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32))
                    let v1 : UInt256 :=
                      UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32))
                    have hv0nat : v0.toNat =
                        fromByteArrayBigEndian (o1.extract 0 32) := by
                      simpa [v0] using
                        (ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo1))
                    by_cases hamount0 : (solcSlotWord σE2 I ⟨5⟩).toNat ≤ v0.toNat
                    · have hleS0 :
                          (Solm.EVM.storageLoad evmS2
                            evmS2.executionEnv.codeOwner ⟨5⟩).toNat ≤
                          fromByteArrayBigEndian (o1.extract 0 32) := by
                        change (solcSlotWord σS2 I ⟨5⟩).toNat ≤ _
                        rw [← hslot5, ← hv0nat]
                        exact hamount0
                      have hprefixA0 := amm4MintSourceAmount0Ok hprefix hlo1 hleS0
                      obtain ⟨_, _, rd1821⟩ := amm4MintX_amount0Ok rd1804 hamount0
                      have hslot6 : solcSlotWord σE2 I ⟨6⟩ =
                          solcSlotWord σS2 I ⟨6⟩ := by
                        simpa [solcSlotWord, codeOwnerStorageWord] using
                          accountMapEquiv_storage_findD hσ2 I.codeOwner ⟨6⟩ ⟨0⟩
                      have hv1nat : v1.toNat =
                          fromByteArrayBigEndian (o2.extract 0 32) := by
                        simpa [v1] using
                          (ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo2))
                      by_cases hamount1 :
                          (solcSlotWord σE2 I ⟨6⟩).toNat ≤ v1.toNat
                      · have hleS1 :
                            (Solm.EVM.storageLoad evmS2
                              evmS2.executionEnv.codeOwner ⟨6⟩).toNat ≤
                            fromByteArrayBigEndian (o2.extract 0 32) := by
                          change (solcSlotWord σS2 I ⟨6⟩).toNat ≤ _
                          rw [← hslot6, ← hv1nat]
                          exact hamount1
                        have hprefixA1 := amm4MintSourceAmount1Ok
                          hprefixA0 hlo2 hleS1
                        obtain ⟨_, _, rd1838⟩ :=
                          amm4MintX_amount1Ok rd1821 hamount1
                        have hslotSupply : solcSlotWord σE2 I ⟨0⟩ =
                            solcSlotWord σS2 I ⟨0⟩ := by
                          simpa [solcSlotWord, codeOwnerStorageWord] using
                            accountMapEquiv_storage_findD hσ2 I.codeOwner ⟨0⟩ ⟨0⟩
                        have ha0nat :
                            (UInt256.sub v0 (solcSlotWord σE2 I ⟨5⟩)).toNat =
                            fromByteArrayBigEndian (o1.extract 0 32) -
                              (solcSlotWord σE2 I ⟨5⟩).toNat := by
                          rw [usub_toNat hamount0, hv0nat]
                        by_cases hnum0 :
                            (UInt256.sub v0 (solcSlotWord σE2 I ⟨5⟩)).toNat *
                              (solcSlotWord σE2 I ⟨0⟩).toNat < UInt256.size
                        · have hsourceFit :
                              (fromByteArrayBigEndian (o1.extract 0 32) -
                                (Solm.EVM.storageLoad evmS2
                                  evmS2.executionEnv.codeOwner ⟨5⟩).toNat) *
                              (Solm.EVM.storageLoad evmS2
                                evmS2.executionEnv.codeOwner ⟨0⟩).toNat <
                              UInt256.size := by
                            change (fromByteArrayBigEndian (o1.extract 0 32) -
                              (solcSlotWord σS2 I ⟨5⟩).toNat) *
                              (solcSlotWord σS2 I ⟨0⟩).toNat < UInt256.size
                            rw [← hslot5, ← hslotSupply, ← ha0nat]
                            exact hnum0
                          have hprefixNum0 := amm4MintSourceLiq0NumeratorOk
                            hprefixA1 hsourceFit
                          obtain ⟨_, _, rd1854⟩ :=
                            amm4MintX_liq0NumeratorOk rd1838 hnum0
                          by_cases hreserve0 : solcSlotWord σE2 I ⟨5⟩ = ⟨0⟩
                          · have ⟨hawlo, _, _⟩ :=
                              amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                            have hrev := amm4MintX_liq0ReserveZero
                              rd1854 hreserve0 (by omega)
                            have hsourceZero : Solm.EVM.storageLoad evmS2
                                evmS2.executionEnv.codeOwner ⟨5⟩ = ⟨0⟩ := by
                              change solcSlotWord σS2 I ⟨5⟩ = ⟨0⟩
                              rw [← hslot5]
                              exact hreserve0
                            have hbody := amm4MintSourceLiq0ReserveZero
                              hprefixNum0 hsourceZero
                            exact hrev.reEquivExecutionRevert hcode hdispatch
                              (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                          · have hsourcePos : 0 <
                                (Solm.EVM.storageLoad evmS2
                                  evmS2.executionEnv.codeOwner ⟨5⟩).toNat := by
                              change 0 < (solcSlotWord σS2 I ⟨5⟩).toNat
                              rw [← hslot5]
                              have hn : (solcSlotWord σE2 I ⟨5⟩).toNat ≠ 0 := by
                                intro hz
                                exact hreserve0 (uint256_toNat_eq_zero hz)
                              omega
                            have hprefixLiq0 := amm4MintSourceLiq0Ok
                              hprefixNum0 hsourcePos
                            obtain ⟨_, _, rd1867⟩ := amm4MintX_liq0Ok
                              rd1854 hreserve0
                            have ha1nat :
                                (UInt256.sub v1 (solcSlotWord σE2 I ⟨6⟩)).toNat =
                                fromByteArrayBigEndian (o2.extract 0 32) -
                                  (solcSlotWord σE2 I ⟨6⟩).toNat := by
                              rw [usub_toNat hamount1, hv1nat]
                            by_cases hnum1 :
                                (UInt256.sub v1 (solcSlotWord σE2 I ⟨6⟩)).toNat *
                                  (solcSlotWord σE2 I ⟨0⟩).toNat < UInt256.size
                            · have hsourceFit1 :
                                  (fromByteArrayBigEndian (o2.extract 0 32) -
                                    (Solm.EVM.storageLoad evmS2
                                      evmS2.executionEnv.codeOwner ⟨6⟩).toNat) *
                                  (Solm.EVM.storageLoad evmS2
                                    evmS2.executionEnv.codeOwner ⟨0⟩).toNat <
                                  UInt256.size := by
                                change (fromByteArrayBigEndian (o2.extract 0 32) -
                                  (solcSlotWord σS2 I ⟨6⟩).toNat) *
                                  (solcSlotWord σS2 I ⟨0⟩).toNat < UInt256.size
                                rw [← hslot6, ← hslotSupply, ← ha1nat]
                                exact hnum1
                              have hprefixNum1 := amm4MintSourceLiq1NumeratorOk
                                hprefixLiq0 hsourceFit1
                              obtain ⟨_, _, rd1883⟩ :=
                                amm4MintX_liq1NumeratorOk rd1867 hnum1
                              by_cases hreserve1 : solcSlotWord σE2 I ⟨6⟩ = ⟨0⟩
                              · have ⟨hawlo, _, _⟩ :=
                                  amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                                have hrev := amm4MintX_liq1ReserveZero
                                  rd1883 hreserve1 (by omega)
                                have hsourceZero : Solm.EVM.storageLoad evmS2
                                    evmS2.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩ := by
                                  change solcSlotWord σS2 I ⟨6⟩ = ⟨0⟩
                                  rw [← hslot6]
                                  exact hreserve1
                                have hbody := amm4MintSourceLiq1ReserveZero
                                  hprefixNum1 hsourceZero
                                exact hrev.reEquivExecutionRevert hcode hdispatch
                                  (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                              · have hsourcePos1 : 0 <
                                    (Solm.EVM.storageLoad evmS2
                                      evmS2.executionEnv.codeOwner ⟨6⟩).toNat := by
                                  change 0 < (solcSlotWord σS2 I ⟨6⟩).toNat
                                  rw [← hslot6]
                                  have hn : (solcSlotWord σE2 I ⟨6⟩).toNat ≠ 0 := by
                                    intro hz
                                    exact hreserve1 (uint256_toNat_eq_zero hz)
                                  omega
                                have hprefixLiq1 := amm4MintSourceLiq1Ok
                                  hprefixNum1 hsourcePos1
                                obtain ⟨_, _, rd1896⟩ := amm4MintX_liq1Ok
                                  rd1883 hreserve1
                                let r0E := solcSlotWord σE2 I ⟨5⟩
                                let r1E := solcSlotWord σE2 I ⟨6⟩
                                let supplyE := solcSlotWord σE2 I ⟨0⟩
                                let q0 := UInt256.div
                                  (UInt256.mul (UInt256.sub v0 r0E) supplyE) r0E
                                let q1 := UInt256.div
                                  (UInt256.mul (UInt256.sub v1 r1E) supplyE) r1E
                                have hq0 : q0.toNat =
                                    amm4MintLiq0Value o1 r0E supplyE r0E := by
                                  have hle : r0E.toNat ≤
                                      fromByteArrayBigEndian (o1.extract 0 32) := by
                                    rw [← hv0nat]
                                    exact hamount0
                                  have hfit :
                                      (fromByteArrayBigEndian (o1.extract 0 32) -
                                        r0E.toNat) * supplyE.toNat < UInt256.size := by
                                    rw [← ha0nat]
                                    exact hnum0
                                  simpa [q0, r0E, supplyE, amm4MintLiq0Value] using
                                    amm4MintRatioWord_toNat o1 r0E supplyE hlo1 hle hfit
                                have hq1 : q1.toNat =
                                    amm4MintLiq1Value o2 r1E supplyE r1E := by
                                  have hle : r1E.toNat ≤
                                      fromByteArrayBigEndian (o2.extract 0 32) := by
                                    rw [← hv1nat]
                                    exact hamount1
                                  have hfit :
                                      (fromByteArrayBigEndian (o2.extract 0 32) -
                                        r1E.toNat) * supplyE.toNat < UInt256.size := by
                                    rw [← ha1nat]
                                    exact hnum1
                                  simpa [q1, r1E, supplyE, amm4MintLiq1Value] using
                                    amm4MintRatioWord_toNat o2 r1E supplyE hlo2 hle hfit
                                have hq0S : q0.toNat =
                                    amm4MintLiq0Value o1
                                      (solcSlotWord σS2 I ⟨5⟩)
                                      (solcSlotWord σS2 I ⟨0⟩)
                                      (solcSlotWord σS2 I ⟨5⟩) := by
                                  rw [← hslot5, ← hslotSupply]
                                  exact hq0
                                have hq1S : q1.toNat =
                                    amm4MintLiq1Value o2
                                      (solcSlotWord σS2 I ⟨6⟩)
                                      (solcSlotWord σS2 I ⟨0⟩)
                                      (solcSlotWord σS2 I ⟨6⟩) := by
                                  rw [← hslot6, ← hslotSupply]
                                  exact hq1
                                by_cases hmin : q0.toNat ≤ q1.toNat
                                · have hsourceLe :
                                      amm4MintLiq0Value o1
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨5⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨5⟩) ≤
                                      amm4MintLiq1Value o2
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨6⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨6⟩) := by
                                    change amm4MintLiq0Value o1
                                        (solcSlotWord σS2 I ⟨5⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨5⟩) ≤
                                      amm4MintLiq1Value o2
                                        (solcSlotWord σS2 I ⟨6⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨6⟩)
                                    rw [← hq0S, ← hq1S]
                                    exact hmin
                                  have hselect := amm4MintSourceSelect0
                                    (evm := evmS2) (I := I) hsourceLe
                                  have hprefixSelected := execBlock_append
                                    hprefixLiq1 hselect
                                  obtain ⟨_, _, rd1915⟩ :=
                                    amm4MintX_selectLiq0 rd1896 hmin
                                  by_cases hliq0 : q0 = ⟨0⟩
                                  · have hsourceZero :
                                        amm4MintLiq0Value o1
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨5⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨5⟩) = 0 := by
                                      change amm4MintLiq0Value o1
                                        (solcSlotWord σS2 I ⟨5⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨5⟩) = 0
                                      rw [← hq0S, hliq0]
                                      decide
                                    have hbody := amm4MintSourceLiquidityZero
                                      hprefixSelected hsourceZero
                                    have hrev := amm4MintX_liquidityZeroFromTrace
                                      hlo1 ho1bound ho2size rd1915 hliq0
                                    exact hrev.reEquivExecutionRevert hcode hdispatch
                                      (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                                  · have hsourcePos : 0 <
                                        amm4MintLiq0Value o1
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨5⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨5⟩) := by
                                      change 0 < amm4MintLiq0Value o1
                                        (solcSlotWord σS2 I ⟨5⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨5⟩)
                                      rw [← hq0S]
                                      have hn : q0.toNat ≠ 0 := by
                                        intro hz
                                        exact hliq0 (uint256_toNat_eq_zero hz)
                                      omega
                                    have hprefixGuarded :=
                                      amm4MintSourceLiquidityNonzero
                                        hprefixSelected hsourcePos
                                    obtain ⟨_, _, rd1981⟩ :=
                                      amm4MintX_liquidityNonzero rd1915 hliq0
                                    by_cases hfitSupply :
                                        supplyE.toNat + q0.toNat < UInt256.size
                                    · have hsourceFit :
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩).toNat +
                                          amm4MintLiq0Value o1
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩) <
                                            UInt256.size := by
                                        change (solcSlotWord σS2 I ⟨0⟩).toNat +
                                          amm4MintLiq0Value o1
                                            (solcSlotWord σS2 I ⟨5⟩)
                                            (solcSlotWord σS2 I ⟨0⟩)
                                            (solcSlotWord σS2 I ⟨5⟩) < _
                                        rw [← hq0S, ← hslotSupply]
                                        exact hfitSupply
                                      have hprefixSupply := amm4MintSourceSupplyOk
                                        hprefixGuarded hsourceFit
                                      obtain ⟨_, _, rd2004⟩ :=
                                        amm4MintX_supplyAdded rd1981 hperm
                                          (by simpa [supplyE] using hfitSupply)
                                      let evmE2 : EVM.State :=
                                        { evmE with
                                          accountMap := σE2
                                          substate := A2
                                          createdAccounts := cA2 }
                                      have hσCall : EVMStateEquiv evmE2 evmS2 := by
                                        refine ⟨?_, ?_, ?_⟩
                                        · rfl
                                        · rfl
                                        · simpa [evmE2, evmS2] using hσ2
                                      have hnewSupply :
                                          supplyE + q0 =
                                            amm4MintNewSupplyWord evmS2 q0.toNat := by
                                        apply u256_inj
                                        rw [uadd_toNat, Nat.mod_eq_of_lt hfitSupply]
                                        unfold amm4MintNewSupplyWord
                                        rw [show (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩) =
                                          solcSlotWord σS2 I ⟨0⟩ from rfl,
                                          ← hslotSupply]
                                        exact (ulit_toNat' _ hfitSupply).symm
                                      let evmE3 := Solm.EVM.storageStore evmE2
                                        evmE2.executionEnv.codeOwner ⟨0⟩
                                        (supplyE + q0)
                                      let evmS3 := amm4MintAfterSupply evmS2 q0.toNat
                                      have hσSupply : EVMStateEquiv evmE3 evmS3 := by
                                        simpa [evmE3, evmS3, amm4MintAfterSupply]
                                          using hσCall.storageStore_codeOwner ⟨0⟩ hnewSupply
                                      have hmapE3 : evmE3.accountMap =
                                          sstoreAccountMap I.codeOwner σE2 ⟨0⟩
                                            (supplyE + q0) := by
                                        simp [evmE3, evmE2, storageStore_accountMap,
                                          evmE, initState]
                                      have hmem : 64 ≤
                                          (amm4MintToken1DecodeMem I o1 o2).size := by
                                        have hsz := amm4MintToken1DecodeMem_size_ge
                                          I hlo1 ho1bound (by
                                            norm_num [UInt256.size] at *
                                            omega)
                                        have hptr :=
                                          (show 160 ≤ (amm4MintToken0FreePtr o1).toNat from
                                            by simpa only [amm4MintToken0FreePtr] using
                                              (amm4MintToken0FreePtr_bounds o1 hlo1 ho1bound).1)
                                        omega
                                      have ⟨hawlo, _, _⟩ :=
                                        amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                                      obtain ⟨_, _, rd2070⟩ :=
                                        amm4MintX_recipientLoad rd2004 hcanon hmem
                                          (by omega)
                                      have hrecipientSlot :=
                                        amm4MintRecipientSlot_eq_solc I hcanon
                                      have hbalance :
                                          solcSlotWord
                                            (sstoreAccountMap I.codeOwner σE2 ⟨0⟩
                                              (supplyE + q0)) I
                                            (solcMappingSlot ⟨1⟩ (amm4MintToWord I)) =
                                          Solm.EVM.storageLoad evmS3
                                            evmS3.executionEnv.codeOwner
                                            (amm4MintRecipientSlot I) := by
                                        rw [← hmapE3, hrecipientSlot]
                                        change Solm.EVM.storageLoad evmE3 I.codeOwner
                                          (amm4MintRecipientSlot I) = _
                                        have howner : evmE3.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          simp [evmE3, storageStore_executionEnv,
                                            evmE2, evmE, initState]
                                        rw [← howner]
                                        exact hσSupply.storageLoad_codeOwner
                                          (amm4MintRecipientSlot I)
                                      have hliqSourceEq :
                                          amm4MintLiq0Value o1
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩) =
                                            q0.toNat := by
                                        change amm4MintLiq0Value o1
                                          (solcSlotWord σS2 I ⟨5⟩)
                                          (solcSlotWord σS2 I ⟨0⟩)
                                          (solcSlotWord σS2 I ⟨5⟩) = _
                                        exact hq0S.symm
                                      have hprefixSupply' := by
                                        simpa only [hliqSourceEq] using hprefixSupply
                                      let σE3 := sstoreAccountMap I.codeOwner σE2
                                        ⟨0⟩ (supplyE + q0)
                                      let recipientSlot :=
                                        solcMappingSlot ⟨1⟩ (amm4MintToWord I)
                                      let recipientE := solcSlotWord σE3 I recipientSlot
                                      by_cases hfitRecipient :
                                          recipientE.toNat + q0.toNat < UInt256.size
                                      · have hsourceFit :
                                            (Solm.EVM.storageLoad evmS3
                                              evmS3.executionEnv.codeOwner
                                              (amm4MintRecipientSlot I)).toNat +
                                            q0.toNat < UInt256.size := by
                                          rw [← hbalance]
                                          exact hfitRecipient
                                        have hprefixRecipient :=
                                          amm4MintSourceRecipientOk
                                            hprefixSupply' hsourceFit
                                        obtain ⟨_, _, rd2087⟩ :=
                                          amm4MintX_recipientAdded rd2070 hperm
                                            (by simpa [recipientE, recipientSlot,
                                              σE3] using hfitRecipient)
                                        have hnewRecipient :
                                            recipientE + q0 =
                                              amm4MintNewRecipientWord evmS3 I
                                                q0.toNat := by
                                          apply u256_inj
                                          rw [uadd_toNat,
                                            Nat.mod_eq_of_lt hfitRecipient]
                                          unfold amm4MintNewRecipientWord
                                          rw [← hbalance]
                                          exact (ulit_toNat' _ hfitRecipient).symm
                                        let evmE4 := Solm.EVM.storageStore evmE3
                                          evmE3.executionEnv.codeOwner
                                          (amm4MintRecipientSlot I)
                                          (recipientE + q0)
                                        let evmS4 :=
                                          amm4MintAfterRecipient evmS3 I q0.toNat
                                        have hσRecipient :
                                            EVMStateEquiv evmE4 evmS4 := by
                                          simpa [evmE4, evmS4, amm4MintAfterRecipient]
                                            using hσSupply.storageStore_codeOwner
                                              (amm4MintRecipientSlot I) hnewRecipient
                                        have howner3 : evmE3.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          simp [evmE3, storageStore_executionEnv,
                                            evmE2, evmE, initState]
                                        have hmapE4 : evmE4.accountMap =
                                            sstoreAccountMap I.codeOwner σE3
                                              recipientSlot (recipientE + q0) := by
                                          simp [evmE4, storageStore_accountMap,
                                            howner3, hmapE3, hrecipientSlot,
                                            σE3, recipientSlot]
                                        obtain ⟨_, _, rd2110⟩ :=
                                          amm4MintX_reservesStored rd2087 hperm
                                        have hprefixReserve0 :=
                                          amm4MintSourceReserve0Ok
                                            hprefixRecipient hlo1
                                        have hprefixReserve1 :=
                                          amm4MintSourceReserve1Ok
                                            hprefixReserve0 hlo2
                                        have hreserveWord0 :
                                            v0 = amm4MintReserve0Word o1 := by
                                          rfl
                                        have hreserveWord1 :
                                            v1 = amm4MintReserve1Word o2 := by
                                          rfl
                                        let evmE5 := Solm.EVM.storageStore evmE4
                                          evmE4.executionEnv.codeOwner ⟨5⟩ v0
                                        let evmS5 := amm4MintAfterReserve0 evmS4 o1
                                        have hσReserve0 :
                                            EVMStateEquiv evmE5 evmS5 := by
                                          simpa [evmE5, evmS5, amm4MintAfterReserve0]
                                            using hσRecipient.storageStore_codeOwner
                                              ⟨5⟩ hreserveWord0
                                        let evmE6 := Solm.EVM.storageStore evmE5
                                          evmE5.executionEnv.codeOwner ⟨6⟩ v1
                                        let evmS6 := amm4MintAfterReserve1 evmS5 o2
                                        have hσReserve1 :
                                            EVMStateEquiv evmE6 evmS6 := by
                                          simpa [evmE6, evmS6, amm4MintAfterReserve1]
                                            using hσReserve0.storageStore_codeOwner
                                              ⟨6⟩ hreserveWord1
                                        have howner4 : evmE4.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          rw [storageStore_executionEnv, howner3]
                                        have howner5 : evmE5.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          rw [storageStore_executionEnv, howner4]
                                        have hmapE6 : evmE6.accountMap =
                                            sstoreAccountMap I.codeOwner
                                              (sstoreAccountMap I.codeOwner
                                                (sstoreAccountMap I.codeOwner σE3
                                                  recipientSlot (recipientE + q0))
                                                ⟨5⟩ v0) ⟨6⟩ v1 := by
                                          rw [show evmE6.accountMap =
                                            sstoreAccountMap evmE5.executionEnv.codeOwner
                                              evmE5.accountMap ⟨6⟩ v1 from
                                            storageStore_accountMap _ _ _ _]
                                          rw [howner5]
                                          rw [show evmE5.accountMap =
                                            sstoreAccountMap evmE4.executionEnv.codeOwner
                                              evmE4.accountMap ⟨5⟩ v0 from
                                            storageStore_accountMap _ _ _ _]
                                          rw [howner4, hmapE4]
                                        have hbody := amm4MintSourceReturn hprefixReserve1
                                        have hret := amm4MintX_returnAfterStores
                                          rd2110 hlo1 ho1bound ho2bound
                                        have henc : returnEquiv
                                            (UInt256.toByteArray q0)
                                            (some [(.int (Int.ofNat q0.toNat))])
                                            mintTransition.returnType := by
                                          simpa [mintTransition] using
                                            (returnEquiv_of_encode (by
                                              simpa [uint256, uint256Int] using
                                                uint256ReturnEncoding q0))
                                        exact hret.reEquivExecutionGenEVMStateEquiv
                                          hcode hdispatch
                                          (amm4Decode_mint_ok hsz36 hbig hcanon)
                                          hbody
                                          (by simp [evmE6, evmE5, evmE4, evmE3,
                                            evmE2, storageStore_createdAccounts])
                                          (accountMapEquiv.of_eq (by
                                            simpa [σE3, recipientSlot, recipientE]
                                              using hmapE6.symm))
                                          hσReserve1 henc
                                      · have hoverRecipient : UInt256.size ≤
                                            recipientE.toNat + q0.toNat := by omega
                                        have hsourceOver : UInt256.size ≤
                                            (Solm.EVM.storageLoad evmS3
                                              evmS3.executionEnv.codeOwner
                                              (amm4MintRecipientSlot I)).toNat +
                                            q0.toNat := by
                                          rw [← hbalance]
                                          exact hoverRecipient
                                        have hrev := amm4MintX_recipientOverflow
                                          rd2070 (by simpa [recipientE, recipientSlot,
                                            σE3] using hoverRecipient) (by omega)
                                        have hbody := amm4MintSourceRecipientOverflow
                                          hprefixSupply' hsourceOver
                                        exact hrev.reEquivExecutionRevert hcode hdispatch
                                          (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                                    · have hoverSupply : UInt256.size ≤
                                          supplyE.toNat + q0.toNat := by omega
                                      have ⟨hawlo, _, _⟩ :=
                                        amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                                      have hrev := amm4MintX_supplyOverflow
                                        rd1981 hoverSupply (by omega)
                                      have hsourceOver : UInt256.size ≤
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩).toNat +
                                          amm4MintLiq0Value o1
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨5⟩) := by
                                        change UInt256.size ≤
                                          (solcSlotWord σS2 I ⟨0⟩).toNat +
                                          amm4MintLiq0Value o1
                                            (solcSlotWord σS2 I ⟨5⟩)
                                            (solcSlotWord σS2 I ⟨0⟩)
                                            (solcSlotWord σS2 I ⟨5⟩)
                                        rw [← hq0S, ← hslotSupply]
                                        exact hoverSupply
                                      have hbody := amm4MintSourceSupplyOverflow
                                        hprefixGuarded hsourceOver
                                      exact hrev.reEquivExecutionRevert hcode hdispatch
                                        (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                                · have hgt : q1.toNat < q0.toNat := by omega
                                  have hsourceGt :
                                      amm4MintLiq1Value o2
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨6⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨6⟩) <
                                      amm4MintLiq0Value o1
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨5⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩)
                                        (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨5⟩) := by
                                    change amm4MintLiq1Value o2
                                        (solcSlotWord σS2 I ⟨6⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨6⟩) <
                                      amm4MintLiq0Value o1
                                        (solcSlotWord σS2 I ⟨5⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨5⟩)
                                    rw [← hq1S, ← hq0S]
                                    exact hgt
                                  have hselect := amm4MintSourceSelect1
                                    (evm := evmS2) (I := I) hsourceGt
                                  have hprefixSelected := execBlock_append
                                    hprefixLiq1 hselect
                                  obtain ⟨_, _, rd1915⟩ :=
                                    amm4MintX_selectLiq1 rd1896 hgt
                                  by_cases hliq1 : q1 = ⟨0⟩
                                  · have hsourceZero :
                                        amm4MintLiq1Value o2
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨6⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨6⟩) = 0 := by
                                      change amm4MintLiq1Value o2
                                        (solcSlotWord σS2 I ⟨6⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨6⟩) = 0
                                      rw [← hq1S, hliq1]
                                      decide
                                    have hbody := amm4MintSourceLiquidityZero
                                      hprefixSelected hsourceZero
                                    have hrev := amm4MintX_liquidityZeroFromTrace
                                      hlo1 ho1bound ho2size rd1915 hliq1
                                    exact hrev.reEquivExecutionRevert hcode hdispatch
                                      (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                                  · have hsourcePos : 0 <
                                        amm4MintLiq1Value o2
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨6⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩)
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨6⟩) := by
                                      change 0 < amm4MintLiq1Value o2
                                        (solcSlotWord σS2 I ⟨6⟩)
                                        (solcSlotWord σS2 I ⟨0⟩)
                                        (solcSlotWord σS2 I ⟨6⟩)
                                      rw [← hq1S]
                                      have hn : q1.toNat ≠ 0 := by
                                        intro hz
                                        exact hliq1 (uint256_toNat_eq_zero hz)
                                      omega
                                    have hprefixGuarded :=
                                      amm4MintSourceLiquidityNonzero
                                        hprefixSelected hsourcePos
                                    obtain ⟨_, _, rd1981⟩ :=
                                      amm4MintX_liquidityNonzero rd1915 hliq1
                                    by_cases hfitSupply :
                                        supplyE.toNat + q1.toNat < UInt256.size
                                    · have hsourceFit :
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩).toNat +
                                          amm4MintLiq1Value o2
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩) <
                                            UInt256.size := by
                                        change (solcSlotWord σS2 I ⟨0⟩).toNat +
                                          amm4MintLiq1Value o2
                                            (solcSlotWord σS2 I ⟨6⟩)
                                            (solcSlotWord σS2 I ⟨0⟩)
                                            (solcSlotWord σS2 I ⟨6⟩) < _
                                        rw [← hq1S, ← hslotSupply]
                                        exact hfitSupply
                                      have hprefixSupply := amm4MintSourceSupplyOk
                                        hprefixGuarded hsourceFit
                                      obtain ⟨_, _, rd2004⟩ :=
                                        amm4MintX_supplyAdded rd1981 hperm
                                          (by simpa [supplyE] using hfitSupply)
                                      let evmE2 : EVM.State :=
                                        { evmE with
                                          accountMap := σE2
                                          substate := A2
                                          createdAccounts := cA2 }
                                      have hσCall : EVMStateEquiv evmE2 evmS2 := by
                                        refine ⟨?_, ?_, ?_⟩
                                        · rfl
                                        · rfl
                                        · simpa [evmE2, evmS2] using hσ2
                                      have hnewSupply :
                                          supplyE + q1 =
                                            amm4MintNewSupplyWord evmS2 q1.toNat := by
                                        apply u256_inj
                                        rw [uadd_toNat, Nat.mod_eq_of_lt hfitSupply]
                                        unfold amm4MintNewSupplyWord
                                        rw [show (Solm.EVM.storageLoad evmS2
                                          evmS2.executionEnv.codeOwner ⟨0⟩) =
                                          solcSlotWord σS2 I ⟨0⟩ from rfl,
                                          ← hslotSupply]
                                        exact (ulit_toNat' _ hfitSupply).symm
                                      let evmE3 := Solm.EVM.storageStore evmE2
                                        evmE2.executionEnv.codeOwner ⟨0⟩
                                        (supplyE + q1)
                                      let evmS3 := amm4MintAfterSupply evmS2 q1.toNat
                                      have hσSupply : EVMStateEquiv evmE3 evmS3 := by
                                        simpa [evmE3, evmS3, amm4MintAfterSupply]
                                          using hσCall.storageStore_codeOwner ⟨0⟩ hnewSupply
                                      have hmapE3 : evmE3.accountMap =
                                          sstoreAccountMap I.codeOwner σE2 ⟨0⟩
                                            (supplyE + q1) := by
                                        simp [evmE3, evmE2, storageStore_accountMap,
                                          evmE, initState]
                                      have hmem : 64 ≤
                                          (amm4MintToken1DecodeMem I o1 o2).size := by
                                        have hsz := amm4MintToken1DecodeMem_size_ge
                                          I hlo1 ho1bound (by
                                            norm_num [UInt256.size] at *
                                            omega)
                                        have hptr :=
                                          (show 160 ≤ (amm4MintToken0FreePtr o1).toNat from
                                            by simpa only [amm4MintToken0FreePtr] using
                                              (amm4MintToken0FreePtr_bounds o1 hlo1 ho1bound).1)
                                        omega
                                      have ⟨hawlo, _, _⟩ :=
                                        amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                                      obtain ⟨_, _, rd2070⟩ :=
                                        amm4MintX_recipientLoad rd2004 hcanon hmem
                                          (by omega)
                                      have hrecipientSlot :=
                                        amm4MintRecipientSlot_eq_solc I hcanon
                                      have hbalance :
                                          solcSlotWord
                                            (sstoreAccountMap I.codeOwner σE2 ⟨0⟩
                                              (supplyE + q1)) I
                                            (solcMappingSlot ⟨1⟩ (amm4MintToWord I)) =
                                          Solm.EVM.storageLoad evmS3
                                            evmS3.executionEnv.codeOwner
                                            (amm4MintRecipientSlot I) := by
                                        rw [← hmapE3, hrecipientSlot]
                                        change Solm.EVM.storageLoad evmE3 I.codeOwner
                                          (amm4MintRecipientSlot I) = _
                                        have howner : evmE3.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          simp [evmE3, storageStore_executionEnv,
                                            evmE2, evmE, initState]
                                        rw [← howner]
                                        exact hσSupply.storageLoad_codeOwner
                                          (amm4MintRecipientSlot I)
                                      have hliqSourceEq :
                                          amm4MintLiq1Value o2
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩) =
                                            q1.toNat := by
                                        change amm4MintLiq1Value o2
                                          (solcSlotWord σS2 I ⟨6⟩)
                                          (solcSlotWord σS2 I ⟨0⟩)
                                          (solcSlotWord σS2 I ⟨6⟩) = _
                                        exact hq1S.symm
                                      have hprefixSupply' := by
                                        simpa only [hliqSourceEq] using hprefixSupply
                                      let σE3 := sstoreAccountMap I.codeOwner σE2
                                        ⟨0⟩ (supplyE + q1)
                                      let recipientSlot :=
                                        solcMappingSlot ⟨1⟩ (amm4MintToWord I)
                                      let recipientE := solcSlotWord σE3 I recipientSlot
                                      by_cases hfitRecipient :
                                          recipientE.toNat + q1.toNat < UInt256.size
                                      · have hsourceFit :
                                            (Solm.EVM.storageLoad evmS3
                                              evmS3.executionEnv.codeOwner
                                              (amm4MintRecipientSlot I)).toNat +
                                            q1.toNat < UInt256.size := by
                                          rw [← hbalance]
                                          exact hfitRecipient
                                        have hprefixRecipient :=
                                          amm4MintSourceRecipientOk
                                            hprefixSupply' hsourceFit
                                        obtain ⟨_, _, rd2087⟩ :=
                                          amm4MintX_recipientAdded rd2070 hperm
                                            (by simpa [recipientE, recipientSlot,
                                              σE3] using hfitRecipient)
                                        have hnewRecipient :
                                            recipientE + q1 =
                                              amm4MintNewRecipientWord evmS3 I
                                                q1.toNat := by
                                          apply u256_inj
                                          rw [uadd_toNat,
                                            Nat.mod_eq_of_lt hfitRecipient]
                                          unfold amm4MintNewRecipientWord
                                          rw [← hbalance]
                                          exact (ulit_toNat' _ hfitRecipient).symm
                                        let evmE4 := Solm.EVM.storageStore evmE3
                                          evmE3.executionEnv.codeOwner
                                          (amm4MintRecipientSlot I)
                                          (recipientE + q1)
                                        let evmS4 :=
                                          amm4MintAfterRecipient evmS3 I q1.toNat
                                        have hσRecipient :
                                            EVMStateEquiv evmE4 evmS4 := by
                                          simpa [evmE4, evmS4, amm4MintAfterRecipient]
                                            using hσSupply.storageStore_codeOwner
                                              (amm4MintRecipientSlot I) hnewRecipient
                                        have howner3 : evmE3.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          simp [evmE3, storageStore_executionEnv,
                                            evmE2, evmE, initState]
                                        have hmapE4 : evmE4.accountMap =
                                            sstoreAccountMap I.codeOwner σE3
                                              recipientSlot (recipientE + q1) := by
                                          simp [evmE4, storageStore_accountMap,
                                            howner3, hmapE3, hrecipientSlot,
                                            σE3, recipientSlot]
                                        obtain ⟨_, _, rd2110⟩ :=
                                          amm4MintX_reservesStored rd2087 hperm
                                        have hprefixReserve0 :=
                                          amm4MintSourceReserve0Ok
                                            hprefixRecipient hlo1
                                        have hprefixReserve1 :=
                                          amm4MintSourceReserve1Ok
                                            hprefixReserve0 hlo2
                                        have hreserveWord0 :
                                            v0 = amm4MintReserve0Word o1 := by
                                          rfl
                                        have hreserveWord1 :
                                            v1 = amm4MintReserve1Word o2 := by
                                          rfl
                                        let evmE5 := Solm.EVM.storageStore evmE4
                                          evmE4.executionEnv.codeOwner ⟨5⟩ v0
                                        let evmS5 := amm4MintAfterReserve0 evmS4 o1
                                        have hσReserve0 :
                                            EVMStateEquiv evmE5 evmS5 := by
                                          simpa [evmE5, evmS5, amm4MintAfterReserve0]
                                            using hσRecipient.storageStore_codeOwner
                                              ⟨5⟩ hreserveWord0
                                        let evmE6 := Solm.EVM.storageStore evmE5
                                          evmE5.executionEnv.codeOwner ⟨6⟩ v1
                                        let evmS6 := amm4MintAfterReserve1 evmS5 o2
                                        have hσReserve1 :
                                            EVMStateEquiv evmE6 evmS6 := by
                                          simpa [evmE6, evmS6, amm4MintAfterReserve1]
                                            using hσReserve0.storageStore_codeOwner
                                              ⟨6⟩ hreserveWord1
                                        have howner4 : evmE4.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          rw [storageStore_executionEnv, howner3]
                                        have howner5 : evmE5.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          rw [storageStore_executionEnv, howner4]
                                        have hmapE6 : evmE6.accountMap =
                                            sstoreAccountMap I.codeOwner
                                              (sstoreAccountMap I.codeOwner
                                                (sstoreAccountMap I.codeOwner σE3
                                                  recipientSlot (recipientE + q1))
                                                ⟨5⟩ v0) ⟨6⟩ v1 := by
                                          rw [show evmE6.accountMap =
                                            sstoreAccountMap evmE5.executionEnv.codeOwner
                                              evmE5.accountMap ⟨6⟩ v1 from
                                            storageStore_accountMap _ _ _ _]
                                          rw [howner5]
                                          rw [show evmE5.accountMap =
                                            sstoreAccountMap evmE4.executionEnv.codeOwner
                                              evmE4.accountMap ⟨5⟩ v0 from
                                            storageStore_accountMap _ _ _ _]
                                          rw [howner4, hmapE4]
                                        have hbody := amm4MintSourceReturn hprefixReserve1
                                        have hret := amm4MintX_returnAfterStores
                                          rd2110 hlo1 ho1bound ho2bound
                                        have henc : returnEquiv
                                            (UInt256.toByteArray q1)
                                            (some [(.int (Int.ofNat q1.toNat))])
                                            mintTransition.returnType := by
                                          simpa [mintTransition] using
                                            (returnEquiv_of_encode (by
                                              simpa [uint256, uint256Int] using
                                                uint256ReturnEncoding q1))
                                        exact hret.reEquivExecutionGenEVMStateEquiv
                                          hcode hdispatch
                                          (amm4Decode_mint_ok hsz36 hbig hcanon)
                                          hbody
                                          (by simp [evmE6, evmE5, evmE4, evmE3,
                                            evmE2, storageStore_createdAccounts])
                                          (accountMapEquiv.of_eq (by
                                            simpa [σE3, recipientSlot, recipientE]
                                              using hmapE6.symm))
                                          hσReserve1 henc
                                      · have hoverRecipient : UInt256.size ≤
                                            recipientE.toNat + q1.toNat := by omega
                                        have hsourceOver : UInt256.size ≤
                                            (Solm.EVM.storageLoad evmS3
                                              evmS3.executionEnv.codeOwner
                                              (amm4MintRecipientSlot I)).toNat +
                                            q1.toNat := by
                                          rw [← hbalance]
                                          exact hoverRecipient
                                        have hrev := amm4MintX_recipientOverflow
                                          rd2070 (by simpa [recipientE, recipientSlot,
                                            σE3] using hoverRecipient) (by omega)
                                        have hbody := amm4MintSourceRecipientOverflow
                                          hprefixSupply' hsourceOver
                                        exact hrev.reEquivExecutionRevert hcode hdispatch
                                          (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                                    · have hoverSupply : UInt256.size ≤
                                          supplyE.toNat + q1.toNat := by omega
                                      have ⟨hawlo, _, _⟩ :=
                                        amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                                      have hrev := amm4MintX_supplyOverflow
                                        rd1981 hoverSupply (by omega)
                                      have hsourceOver : UInt256.size ≤
                                          (Solm.EVM.storageLoad evmS2
                                            evmS2.executionEnv.codeOwner ⟨0⟩).toNat +
                                          amm4MintLiq1Value o2
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨0⟩)
                                            (Solm.EVM.storageLoad evmS2
                                              evmS2.executionEnv.codeOwner ⟨6⟩) := by
                                        change UInt256.size ≤
                                          (solcSlotWord σS2 I ⟨0⟩).toNat +
                                          amm4MintLiq1Value o2
                                            (solcSlotWord σS2 I ⟨6⟩)
                                            (solcSlotWord σS2 I ⟨0⟩)
                                            (solcSlotWord σS2 I ⟨6⟩)
                                        rw [← hq1S, ← hslotSupply]
                                        exact hoverSupply
                                      have hbody := amm4MintSourceSupplyOverflow
                                        hprefixGuarded hsourceOver
                                      exact hrev.reEquivExecutionRevert hcode hdispatch
                                        (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                            · have hover1 : UInt256.size ≤
                                  (UInt256.sub v1 (solcSlotWord σE2 I ⟨6⟩)).toNat *
                                    (solcSlotWord σE2 I ⟨0⟩).toNat := by omega
                              have ⟨hawlo, _, _⟩ :=
                                amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                              have hrev := amm4MintX_liq1NumeratorOverflow
                                rd1867 hover1 (by omega)
                              have hsourceOver : UInt256.size ≤
                                  (fromByteArrayBigEndian (o2.extract 0 32) -
                                    (Solm.EVM.storageLoad evmS2
                                      evmS2.executionEnv.codeOwner ⟨6⟩).toNat) *
                                  (Solm.EVM.storageLoad evmS2
                                    evmS2.executionEnv.codeOwner ⟨0⟩).toNat := by
                                change UInt256.size ≤
                                  (fromByteArrayBigEndian (o2.extract 0 32) -
                                    (solcSlotWord σS2 I ⟨6⟩).toNat) *
                                  (solcSlotWord σS2 I ⟨0⟩).toNat
                                rw [← hslot6, ← hslotSupply, ← ha1nat]
                                exact hover1
                              have hbody := amm4MintSourceLiq1NumeratorOverflow
                                hprefixLiq0 hsourceOver
                              exact hrev.reEquivExecutionRevert hcode hdispatch
                                (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                        · have hover0 : UInt256.size ≤
                              (UInt256.sub v0 (solcSlotWord σE2 I ⟨5⟩)).toNat *
                                (solcSlotWord σE2 I ⟨0⟩).toNat := by omega
                          have ⟨hawlo, _, _⟩ :=
                            amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                          have hrev := amm4MintX_liq0NumeratorOverflow
                            rd1838 hover0 (by omega)
                          have hsourceOver : UInt256.size ≤
                              (fromByteArrayBigEndian (o1.extract 0 32) -
                                (Solm.EVM.storageLoad evmS2
                                  evmS2.executionEnv.codeOwner ⟨5⟩).toNat) *
                              (Solm.EVM.storageLoad evmS2
                                evmS2.executionEnv.codeOwner ⟨0⟩).toNat := by
                            change UInt256.size ≤
                              (fromByteArrayBigEndian (o1.extract 0 32) -
                                (solcSlotWord σS2 I ⟨5⟩).toNat) *
                              (solcSlotWord σS2 I ⟨0⟩).toNat
                            rw [← hslot5, ← hslotSupply, ← ha0nat]
                            exact hover0
                          have hbody := amm4MintSourceLiq0NumeratorOverflow
                            hprefixA1 hsourceOver
                          exact hrev.reEquivExecutionRevert hcode hdispatch
                            (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                      · have hunder1 : v1.toNat <
                            (solcSlotWord σE2 I ⟨6⟩).toNat := by omega
                        have ⟨hawlo, _, _⟩ :=
                          amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                        have hrev := amm4MintX_amount1Underflow rd1821 hunder1
                          (by omega)
                        have hsourceUnder :
                            fromByteArrayBigEndian (o2.extract 0 32) <
                            (Solm.EVM.storageLoad evmS2
                              evmS2.executionEnv.codeOwner ⟨6⟩).toNat := by
                          change _ < (solcSlotWord σS2 I ⟨6⟩).toNat
                          rw [← hslot6, ← hv1nat]
                          exact hunder1
                        have hbody := amm4MintSourceAmount1Underflow
                          hprefixA0 hsourceUnder
                        exact hrev.reEquivExecutionRevert hcode hdispatch
                          (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
                    · have hunder : v0.toNat <
                          (solcSlotWord σE2 I ⟨5⟩).toNat := by omega
                      have ⟨hawlo, _, _⟩ :=
                        amm4MintToken1ActiveWords_bounds o1 hlo1 ho1bound
                      have hrev := amm4MintX_amount0Underflow rd1804 hunder
                        (by omega)
                      have hsourceUnder :
                          fromByteArrayBigEndian (o1.extract 0 32) <
                          (Solm.EVM.storageLoad evmS2
                            evmS2.executionEnv.codeOwner ⟨5⟩).toNat := by
                        have hload : Solm.EVM.storageLoad evmS2
                            evmS2.executionEnv.codeOwner ⟨5⟩ =
                            solcSlotWord σS2 I ⟨5⟩ := by
                          rfl
                        rw [hload, ← hslot5, ← hv0nat]
                        exact hunder
                      have hbody := amm4MintSourceAmount0Underflow hprefix hsourceUnder
                      exact hrev.reEquivExecutionRevert hcode hdispatch
                        (amm4Decode_mint_ok hsz36 hbig hcanon) hbody
      · exact (amm4MintX_noncanon (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hcanon hreach).reEquivDecodingFailed
            hcode hdispatch (amm4Decode_mint_none_noncanon hsz36 hbig hcanon)
    · have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (amm4MintX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hhuge hreach).reEquivDecodingFailed
          hcode hdispatch (amm4Decode_mint_none_huge hhuge)
  · have hshort : I.calldata.size < 36 := by omega
    exact (amm4MintX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach).reEquivDecodingFailed
        hcode hdispatch (amm4Decode_mint_none_short hsz4 hshort)

end Benchmarks.ActAmm4
