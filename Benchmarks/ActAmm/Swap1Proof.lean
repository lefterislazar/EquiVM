import Benchmarks.ActAmm.Swap1InputError
import Benchmarks.ActAmm.Swap1EarlyRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

/-- The swap1 wrapper, entered at PC 314, refines its Solm transition. -/
theorem ammSwap1BodyCoreProof
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammSwap1Selector_size hsel
  have hdispatch := ammDispatch_swap1 hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon :
        (ammSwap1ToWord I).toNat < EVM.addressModulus
      · by_cases hzero : (ammSwap1AmountWord I).toNat = 0
        · exact ammSwap1ZeroOutputBody hcode hsize hwv hsel hreach
            hsz68 hbig hcanon hzero
        · have hpos : 0 < (ammSwap1AmountWord I).toNat := by omega
          by_cases hliq : (ammSwap1AmountWord I).toNat <
              (solcSlotWord σ_evm I ⟨5⟩).toNat
          · by_cases heq0 :
                ammSwap1ToWord I = ammMintToken0Word σ_evm I
            · exact ammSwap1Recipient0Body hcode hsize hwv hsel hreach
                hAccounts hsz68 hbig hcanon hpos hliq heq0
            · by_cases heq1 :
                  ammSwap1ToWord I = ammMintToken1Word σ_evm I
              · exact ammSwap1Recipient1Body hcode hsize hwv hsel hreach
                  hAccounts hsz68 hbig hcanon hpos hliq heq0 heq1
              · by_cases hdepth : I.depth = 1024
                · exact ammSwap1TransferDepthBody hcode hsize hwv hsel
                    hreach hAccounts hsz68 hbig hcanon hpos hliq
                    heq0 heq1 hdepth
                · have hdepthLt : I.depth.val < 1024 := by
                    have hlt := I.depth.isLt
                    omega
                  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
                    hsz68 hsize hbig hcanon hreach
                  obtain ⟨_, _, rd816⟩ :=
                    ammSwap1X_amountPositive rd750 hpos
                  obtain ⟨_, _, rd884⟩ :=
                    ammSwap1X_liquidityAvailable rd816 hliq
                  obtain ⟨_, _, rd941⟩ := ammSwap1X_token0Address rd884
                  obtain ⟨_, _, rd973⟩ :=
                    ammSwap1X_token0Distinct rd941 hcanon heq0
                  obtain ⟨_, _, rd1029⟩ := ammSwap1X_token1Address rd973
                  obtain ⟨_, _, rd1117⟩ :=
                    ammSwap1X_token1Distinct rd1029 hcanon heq1
                  obtain ⟨_, _, rd1174⟩ :=
                    ammSwap1X_transferTokenAddress rd1117
                  obtain ⟨_, _, rd1196⟩ :=
                    ammSwap1X_transferSelectorMem rd1174
                  obtain ⟨_, _, rd1209⟩ :=
                    ammSwap1X_transferArgs rd1196 hcanon
                  obtain ⟨gasWord, k1222, C1222, rd1222⟩ :=
                    ammSwap1X_transferCallFrame rd1209
                  obtain ⟨cA1, σE1, z, out, A1, k1223, C1223,
                    rd1223, hcallE, houtSize, houtBound⟩ :=
                    ammSwap1X_transferCall hperm hdepthLt hcanon
                      ⟨gasWord, k1222, C1222, rd1222⟩
                  by_cases hz : z = false
                  · have rdFail := by simpa [hz] using rd1223
                    have hrev := ammSwap1X_transferCallFailed
                      rdFail houtSize
                      (by simp only [List.length_cons, List.length_nil]; omega)
                    have hcallEFail := by simpa only [hz] using hcallE
                    exact ammSwap1TransferCallFailureBody
                      hcode hwv hsel hAccounts hsz68 hbig hcanon hpos
                      hliq heq0 heq1 hcallEFail hrev
                  · have hzTrue : z = true := by cases z <;> simp_all
                    have rdSuccess := by
                      simpa [hzTrue, ammSwap1TransferPostCallMem]
                        using rd1223
                    obtain ⟨_, _, rd1242⟩ :=
                      ammSwap1X_transferCallSucceeded rdSuccess
                    obtain ⟨_, _, rd6365⟩ :=
                      ammSwap1X_transferToDecoder houtSize rd1242
                    have hcallETrue := by simpa only [hzTrue] using hcallE
                    by_cases hshort : out.size < 32
                    · have hrev :=
                        ammSwap1X_transferDecodeShortReverts
                          hshort rd6365
                      exact ammSwap1TransferDecodeRevertBody
                        hcode hwv hsel hAccounts hsz68 hbig hcanon
                        hpos hliq heq0 heq1 hcallETrue
                        (ammBurnDecodeTransfer_short hshort) hrev
                    · have hlo : 32 ≤ out.size := by omega
                      obtain ⟨_, _, rd6323⟩ :=
                        ammSwap1X_transferDecodeWord hlo houtBound rd6365
                      let v : UInt256 := UInt256.ofNat
                        (fromByteArrayBigEndian (out.extract 0 32))
                      by_cases hcanonBool : v = ⟨0⟩ ∨ v = ⟨1⟩
                      · obtain ⟨_, _, rd1275⟩ :=
                          ammSwap1X_transferDecodeOk hcanonBool rd6323
                        obtain ⟨b, hdec⟩ :=
                          ammSwap1DecodeTransferCanonical hlo houtBound
                            hcanonBool
                        obtain ⟨σS', b', hσ', hsourcePrefix⟩ :=
                          ammSwap1SourceTransferPrefix hwv hAccounts
                            hcanon hpos hliq heq0 heq1 hcallETrue
                            ⟨b, hdec⟩
                        obtain ⟨_, _, rd1332⟩ :=
                          ammSwap1X_balance0Address rd1275
                        obtain ⟨_, _, rd1353⟩ :=
                          ammSwap1X_balance0SelectorMem hlo houtBound
                            rd1332
                        obtain ⟨_, _, rd1365⟩ :=
                          ammSwap1X_balance0ArgMem hlo houtBound rd1353
                        obtain ⟨gasBalance0, _, _, rd1377⟩ :=
                          ammSwap1X_balance0CallFrame hlo houtBound
                            rd1365
                        obtain ⟨cA2, σE2, zBalance0, retBalance0, A2,
                          k1378, C1378, rd1378, hcallBalance0,
                          hretBalance0Size, hretBalance0Bound⟩ :=
                          ammSwap1X_balance0Staticcall
                            (cA := cA1) (σ := σE1) (Apre := A1)
                            hlo houtBound hdepthLt
                            ⟨gasBalance0, _, _, rd1377⟩
                        by_cases hzBalance0 : zBalance0 = false
                        · have rdFail := by simpa [hzBalance0] using rd1378
                          have hrev := ammSwap1X_balance0CallFailed
                            rdFail hretBalance0Size
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          have hcallFail := by
                            simpa only [hzBalance0] using hcallBalance0
                          exact ammSwap1Balance0CallFailureBody
                            hcode hsel hsz68 hbig hcanon hsourcePrefix
                            hσ' hcallFail hrev
                        · have hzBalance0True : zBalance0 = true := by
                            cases zBalance0 <;> simp_all
                          have rdSuccess := by
                            simpa [hzBalance0True,
                              ammSwap1Balance0PostCallMem] using rd1378
                          obtain ⟨_, _, rd1397⟩ :=
                            ammSwap1X_balance0CallSucceeded rdSuccess
                          obtain ⟨_, _, rd6453⟩ :=
                            ammSwap1X_balance0ToDecoder hlo houtBound
                              hretBalance0Size rd1397
                          have hcallBalance0True := by
                            simpa only [hzBalance0True] using hcallBalance0
                          by_cases hshortBalance0 : retBalance0.size < 32
                          · have hrev :=
                              ammSwap1X_balance0DecodeShortReverts
                                hlo houtBound hshortBalance0 rd6453
                            exact ammSwap1Balance0DecodeRevertBody
                              hcode hsel hsz68 hbig hcanon
                              hsourcePrefix hσ' hcallBalance0True
                              (ammMintDecodeBalance_short hshortBalance0)
                              hrev
                          · have hretBalance0Lo : 32 ≤ retBalance0.size := by
                              omega
                            obtain ⟨_, _, rd1431⟩ :=
                              ammSwap1X_balance0DecodeOk hlo houtBound
                                hretBalance0Lo hretBalance0Bound rd6453
                            obtain ⟨σS2, hσ2, hsourceBalance0⟩ :=
                              ammSwap1SourceBalance0Prefix
                                hsourcePrefix hσ' hretBalance0Lo
                                hretBalance0Bound hcallBalance0True
                            obtain ⟨_, _, rd1488⟩ :=
                              ammSwap1X_balance1Address rd1431
                            obtain ⟨_, _, rd1509⟩ :=
                              ammSwap1X_balance1SelectorMem hlo houtBound
                                hretBalance0Bound rd1488
                            obtain ⟨_, _, rd1521⟩ :=
                              ammSwap1X_balance1ArgMem rd1509
                            obtain ⟨gasBalance1, _, _, rd1533⟩ :=
                              ammSwap1X_balance1CallFrame
                                hlo houtBound hretBalance0Lo
                                hretBalance0Bound rd1521
                            obtain ⟨cA3, σE3, zBalance1, retBalance1, A3,
                              k1534, C1534, rd1534, hcallBalance1,
                              hretBalance1Size, hretBalance1Bound⟩ :=
                              ammSwap1X_balance1Staticcall
                                (cA := cA2) (σ := σE2) (Apre := A2)
                                hlo houtBound hretBalance0Lo
                                hretBalance0Bound hdepthLt
                                ⟨gasBalance1, _, _, rd1533⟩
                            by_cases hzBalance1 : zBalance1 = false
                            · have rdFail := by
                                simpa [hzBalance1] using rd1534
                              have hrev := ammSwap1X_balance1CallFailed
                                rdFail hretBalance1Size
                                (by simp only [List.length_cons,
                                    List.length_nil]; omega)
                              have hcallFail := by
                                simpa only [hzBalance1] using hcallBalance1
                              obtain ⟨σS3, hcallS, hσ3⟩ :=
                                ammSwap1TransportBalance1Call
                                  (cA := cA) (σ_solm := σ_solm) (A := A)
                                  hσ2 hcallFail
                              have hbody := ammSwap1SourceBalance1CallFailed
                                I b' retBalance0 retBalance1
                                (by simpa [initState] using hsourceBalance0)
                                (by simpa [initState] using hcallS)
                              exact hrev.reEquivExecutionRevert hcode
                                (ammDispatch_swap1 hsel)
                                (ammDecode_swap1_ok hsz68 hbig hcanon)
                                hbody
                            · have hzBalance1True : zBalance1 = true := by
                                cases zBalance1 <;> simp_all
                              have rdSuccess := by
                                simpa [hzBalance1True,
                                  ammSwap1Balance1PostCallMem]
                                  using rd1534
                              obtain ⟨_, _, rd1553⟩ :=
                                ammSwap1X_balance1CallSucceeded rdSuccess
                              obtain ⟨_, _, rd6453_1⟩ :=
                                ammSwap1X_balance1ToDecoder
                                  hlo houtBound hretBalance0Lo
                                  hretBalance0Bound hretBalance1Size
                                  rd1553
                              have hcallBalance1True := by
                                simpa only [hzBalance1True] using
                                  hcallBalance1
                              by_cases hshortBalance1 :
                                  retBalance1.size < 32
                              · have hrev :=
                                  ammSwap1X_balance1DecodeShortReverts
                                    hlo houtBound hretBalance0Bound
                                    hshortBalance1 rd6453_1
                                obtain ⟨σS3, hcallS, hσ3⟩ :=
                                  ammSwap1TransportBalance1Call
                                    (cA := cA) (σ_solm := σ_solm) (A := A)
                                    hσ2 hcallBalance1True
                                have hbody :=
                                  ammSwap1SourceBalance1DecodeRevert
                                    I b' retBalance0 retBalance1
                                    (by simpa [initState] using hsourceBalance0)
                                    (by simpa [initState] using hcallS)
                                    (ammMintDecodeBalance_short
                                      hshortBalance1)
                                exact hrev.reEquivExecutionRevert hcode
                                  (ammDispatch_swap1 hsel)
                                  (ammDecode_swap1_ok hsz68 hbig hcanon)
                                  hbody
                              · have hretBalance1Lo :
                                    32 ≤ retBalance1.size := by omega
                                obtain ⟨_, _, rd1587⟩ :=
                                  ammSwap1X_balance1DecodeOk
                                    hlo houtBound hretBalance0Lo
                                    hretBalance0Bound hretBalance1Lo
                                    hretBalance1Bound rd6453_1
                                obtain ⟨σS3, hcallS, hσ3⟩ :=
                                  ammSwap1TransportBalance1Call
                                    (cA := cA) (σ_solm := σ_solm) (A := A)
                                    hσ2 hcallBalance1True
                                have hsourceBalance1 :=
                                  ammSwap1SourceBalance1CallOk
                                    I b' retBalance0 retBalance1
                                    (by simpa [initState]
                                      using hsourceBalance0)
                                    hretBalance1Lo hretBalance1Bound
                                    (by simpa [initState] using hcallS)
                                let q0 : UInt256 := UInt256.ofNat
                                  (fromByteArrayBigEndian
                                    (retBalance0.extract 0 32))
                                let q1 : UInt256 := UInt256.ofNat
                                  (fromByteArrayBigEndian
                                    (retBalance1.extract 0 32))
                                by_cases hInput :
                                    (solcSlotWord σE3 I ⟨6⟩).toNat < q1.toNat
                                · obtain ⟨_, _, rd1654⟩ :=
                                    ammSwap1X_inputGuardOk rd1587 hInput
                                  have hslot5 :
                                      solcSlotWord σE3 I ⟨6⟩ =
                                      solcSlotWord σS3 I ⟨6⟩ := by
                                    simpa [solcSlotWord, codeOwnerStorageWord]
                                      using accountMapEquiv_storage_findD
                                        hσ3 I.codeOwner ⟨6⟩ ⟨0⟩
                                  have hq1 : q1.toNat =
                                      fromByteArrayBigEndian
                                        (retBalance1.extract 0 32) := by
                                    apply UInt256.toNat_ofNat_of_lt
                                    exact fromByteArrayBigEndian_extract0_32_lt
                                      hretBalance1Lo
                                  have hgtS :
                                      (Solm.EVM.storageLoad
                                        { initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σS3,
                                          substate := A3,
                                          createdAccounts := cA3 }
                                        I.codeOwner ⟨6⟩).toNat <
                                      fromByteArrayBigEndian
                                        (retBalance1.extract 0 32) := by
                                    simpa [Solm.EVM.storageLoad,
                                      Ethereum.State.lookupAccount,
                                      Ethereum.Account.lookupStorage, initState,
                                      solcSlotWord, codeOwnerStorageWord,
                                      ← hslot5, ← hq1] using hInput
                                  have hsourceInputGuard :=
                                    ammSwap1SourceInputGuardOk
                                      I b' retBalance0 retBalance1
                                      hsourceBalance1 hgtS
                                  obtain ⟨_, _, rd1672⟩ :=
                                    ammSwap1X_amount1In rd1654 hInput
                                  have hsourceAmount1In :=
                                    ammSwap1SourceAmount1InOk
                                      I b' retBalance0 retBalance1
                                      hsourceInputGuard hretBalance1Lo
                                      (Nat.le_of_lt hgtS)
                                  have hfitE :
                                      (solcSlotWord σE3 I ⟨6⟩).toNat +
                                        (UInt256.sub q1
                                          (solcSlotWord σE3 I ⟨6⟩)).toNat <
                                        UInt256.size := by
                                    rw [usub_toNat (Nat.le_of_lt hInput)]
                                    have hq1fit :=
                                      fromByteArrayBigEndian_extract0_32_lt
                                        hretBalance1Lo
                                    rw [hq1]
                                    omega
                                  obtain ⟨_, _, rd1685⟩ :=
                                    ammSwap1X_denominator rd1672 hfitE
                                  have hfitS :
                                      (Solm.EVM.storageLoad
                                        { initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σS3,
                                          substate := A3,
                                          createdAccounts := cA3 }
                                        I.codeOwner ⟨6⟩).toNat +
                                        (fromByteArrayBigEndian
                                          (retBalance1.extract 0 32) -
                                          (Solm.EVM.storageLoad
                                            { initState cA gh bl σ_solm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σS3,
                                              substate := A3,
                                              createdAccounts := cA3 }
                                            I.codeOwner ⟨6⟩).toNat) <
                                        UInt256.size := by
                                    have hbalFit :=
                                      fromByteArrayBigEndian_extract0_32_lt
                                        hretBalance1Lo
                                    omega
                                  have hsourceDenominator :=
                                    ammSwap1SourceDenominatorOk
                                      I b' retBalance0 retBalance1
                                      hsourceAmount1In hfitS
                                  by_cases hmulFitE :
                                      (solcSlotWord σE3 I ⟨5⟩).toNat *
                                        (UInt256.sub q1
                                          (solcSlotWord σE3 I ⟨6⟩)).toNat <
                                        UInt256.size
                                  · obtain ⟨_, _, rd1699⟩ :=
                                      ammSwap1X_numerator rd1685 hmulFitE
                                    have hslot6 :
                                        solcSlotWord σE3 I ⟨5⟩ =
                                        solcSlotWord σS3 I ⟨5⟩ := by
                                      simpa [solcSlotWord, codeOwnerStorageWord]
                                        using accountMapEquiv_storage_findD
                                          hσ3 I.codeOwner ⟨5⟩ ⟨0⟩
                                    have hr0S :
                                        (Solm.EVM.storageLoad
                                          { initState cA gh bl σ_solm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σS3,
                                            substate := A3,
                                            createdAccounts := cA3 }
                                          I.codeOwner ⟨6⟩).toNat =
                                        (solcSlotWord σE3 I ⟨6⟩).toNat := by
                                      simpa [Solm.EVM.storageLoad,
                                        Ethereum.State.lookupAccount,
                                        Ethereum.Account.lookupStorage, initState,
                                        solcSlotWord, codeOwnerStorageWord,
                                        ← hslot5]
                                    have hr1S :
                                        (Solm.EVM.storageLoad
                                          { initState cA gh bl σ_solm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σS3,
                                            substate := A3,
                                            createdAccounts := cA3 }
                                          I.codeOwner ⟨5⟩).toNat =
                                        (solcSlotWord σE3 I ⟨5⟩).toNat := by
                                      simpa [Solm.EVM.storageLoad,
                                        Ethereum.State.lookupAccount,
                                        Ethereum.Account.lookupStorage, initState,
                                        solcSlotWord, codeOwnerStorageWord,
                                        ← hslot6]
                                    have hmulFitS :
                                        (Solm.EVM.storageLoad
                                          { initState cA gh bl σ_solm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σS3,
                                            substate := A3,
                                            createdAccounts := cA3 }
                                          I.codeOwner ⟨5⟩).toNat *
                                          (fromByteArrayBigEndian
                                            (retBalance1.extract 0 32) -
                                            (Solm.EVM.storageLoad
                                              { initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I with
                                                accountMap := σS3,
                                                substate := A3,
                                                createdAccounts := cA3 }
                                              I.codeOwner ⟨6⟩).toNat) <
                                          UInt256.size := by
                                      rw [hr0S, hr1S, ← hq1,
                                        ← usub_toNat (Nat.le_of_lt hInput)]
                                      exact hmulFitE
                                    have hsourceNumerator :=
                                      ammSwap1SourceNumeratorOk
                                        I b' retBalance0 retBalance1
                                        hsourceDenominator hmulFitS
                                    have hdenomNat :
                                        ((solcSlotWord σE3 I ⟨6⟩) +
                                          UInt256.sub q1
                                            (solcSlotWord σE3 I ⟨6⟩)).toNat =
                                        q1.toNat := by
                                      rw [uadd_toNat,
                                        Nat.mod_eq_of_lt hfitE,
                                        usub_toNat (Nat.le_of_lt hInput)]
                                      omega
                                    have hdenom :
                                        (solcSlotWord σE3 I ⟨6⟩) +
                                          UInt256.sub q1
                                            (solcSlotWord σE3 I ⟨6⟩) ≠
                                        ⟨0⟩ := by
                                      intro hz
                                      have hzNat := congrArg UInt256.toNat hz
                                      rw [hdenomNat] at hzNat
                                      norm_num at hzNat
                                      omega
                                    obtain ⟨_, _, rd1709⟩ :=
                                      ammSwap1X_kQuotient rd1699 hdenom
                                    have hsourceQuotient :=
                                      ammSwap1SourceQuotientOk
                                        I b' retBalance0 retBalance1
                                        hsourceNumerator (by omega)
                                    have hquotNat :=
                                      ammSwap1Quotient_toNat
                                        (solcSlotWord σE3 I ⟨6⟩)
                                        (solcSlotWord σE3 I ⟨5⟩) q1
                                        (Nat.le_of_lt hInput) hfitE hmulFitE
                                    by_cases hK :
                                        (ammSwap1AmountWord I).toNat ≤
                                          (UInt256.div
                                            (UInt256.mul
                                              (solcSlotWord σE3 I ⟨5⟩)
                                              (UInt256.sub q1
                                                (solcSlotWord σE3 I ⟨6⟩)))
                                            ((solcSlotWord σE3 I ⟨6⟩) +
                                              UInt256.sub q1
                                                (solcSlotWord σE3 I ⟨6⟩))).toNat
                                    · obtain ⟨_, _, rd1775⟩ :=
                                        ammSwap1X_kGuardOk rd1709 hK
                                      have hKS :
                                          (ammSwap1AmountWord I).toNat ≤
                                            ((Solm.EVM.storageLoad
                                              { initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I with
                                                accountMap := σS3,
                                                substate := A3,
                                                createdAccounts := cA3 }
                                              I.codeOwner ⟨5⟩).toNat *
                                              (fromByteArrayBigEndian
                                                (retBalance1.extract 0 32) -
                                                (Solm.EVM.storageLoad
                                                  { initState cA gh bl σ_solm σ₀
                                                      (Sat256.ofUInt256 g) A I with
                                                    accountMap := σS3,
                                                    substate := A3,
                                                    createdAccounts := cA3 }
                                                  I.codeOwner ⟨6⟩).toNat)) /
                                            ((Solm.EVM.storageLoad
                                              { initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I with
                                                accountMap := σS3,
                                                substate := A3,
                                                createdAccounts := cA3 }
                                              I.codeOwner ⟨6⟩).toNat +
                                              (fromByteArrayBigEndian
                                                (retBalance1.extract 0 32) -
                                                (Solm.EVM.storageLoad
                                                  { initState cA gh bl σ_solm σ₀
                                                      (Sat256.ofUInt256 g) A I with
                                                    accountMap := σS3,
                                                    substate := A3,
                                                    createdAccounts := cA3 }
                                                  I.codeOwner ⟨6⟩).toNat)) := by
                                        rw [hr0S, hr1S, ← hq1, ← hquotNat]
                                        exact hK
                                      have hsourceK :=
                                        ammSwap1SourceKGuardOk
                                          I b' retBalance0 retBalance1
                                          hsourceQuotient hKS
                                      obtain ⟨_, _, rd1783⟩ :=
                                        ammSwap1X_reserve0Stored rd1775 hperm
                                      obtain ⟨_, _, rd1790⟩ :=
                                        ammSwap1X_reserve1Stored rd1783 hperm
                                      have hret := ammSwap1X_swapStop rd1790
                                      have hbody := ammSwap1SourceSuccess
                                        I b' retBalance0 retBalance1
                                        hsourceK hretBalance0Lo hretBalance1Lo
                                      let evmE3 : EVM.State :=
                                        { initState cA3 gh bl σE3 σ₀
                                            (Sat256.ofUInt256 g) A3 I with
                                          accountMap := σE3,
                                          substate := A3,
                                          createdAccounts := cA3 }
                                      let evmS3 : EVM.State :=
                                        { initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σS3,
                                          substate := A3,
                                          createdAccounts := cA3 }
                                      have hState3 : EVMStateEquiv
                                          evmE3 evmS3 := by
                                        refine ⟨?_, ?_, ?_⟩
                                        · simp [evmE3, evmS3, initState]
                                        · simp [evmE3, evmS3]
                                        · simpa [evmE3, evmS3] using hσ3
                                      let evmE4 := ammSwap1AfterReserve0
                                        evmE3 retBalance0
                                      let evmS4 := ammSwap1AfterReserve0
                                        evmS3 retBalance0
                                      have hState4 : EVMStateEquiv
                                          evmE4 evmS4 := by
                                        simpa [evmE4, evmS4,
                                          ammSwap1AfterReserve0] using
                                          hState3.storageStore_codeOwner
                                            ⟨5⟩ rfl
                                      let evmE5 := ammSwap1AfterReserve1
                                        evmE4 retBalance1
                                      let evmS5 := ammSwap1AfterReserve1
                                        evmS4 retBalance1
                                      have hState5 : EVMStateEquiv
                                          evmE5 evmS5 := by
                                        simpa [evmE5, evmS5,
                                          ammSwap1AfterReserve1] using
                                          hState4.storageStore_codeOwner
                                            ⟨6⟩ rfl
                                      have hmapE5 : evmE5.accountMap =
                                          sstoreAccountMap I.codeOwner
                                            (sstoreAccountMap I.codeOwner
                                              σE3 ⟨5⟩ q0) ⟨6⟩ q1 := by
                                        simp [evmE5, evmE4, evmE3,
                                          ammSwap1AfterReserve0,
                                          ammSwap1AfterReserve1,
                                          storageStore_accountMap,
                                          storageStore_executionEnv,
                                          initState, q0, q1]
                                      have hcreated5 : cA3 =
                                          evmE5.createdAccounts := by
                                        simp [evmE5, evmE4, evmE3,
                                          ammSwap1AfterReserve0,
                                          ammSwap1AfterReserve1,
                                          storageStore_createdAccounts]
                                      have henc : returnEquiv
                                          ByteArray.empty none
                                          swap1Transition.returnType := by
                                        rw [show swap1Transition.returnType =
                                          [] by rfl]
                                        exact returnEquiv.fallthrough rfl
                                          (by rfl) (by native_decide)
                                      exact hret
                                        |>.reEquivExecutionGenEVMStateEquiv
                                          hcode (ammDispatch_swap1 hsel)
                                          (ammDecode_swap1_ok
                                            hsz68 hbig hcanon)
                                          (by simpa [evmS3, evmS4, evmS5]
                                            using hbody)
                                          hcreated5
                                          (accountMapEquiv.of_eq hmapE5.symm)
                                          hState5 henc
                                    · have hbadE :
                                          (UInt256.div
                                            (UInt256.mul
                                              (solcSlotWord σE3 I ⟨5⟩)
                                              (UInt256.sub q1
                                                (solcSlotWord σE3 I ⟨6⟩)))
                                            ((solcSlotWord σE3 I ⟨6⟩) +
                                              UInt256.sub q1
                                                (solcSlotWord σE3 I ⟨6⟩))).toNat <
                                          (ammSwap1AmountWord I).toNat :=
                                        Nat.lt_of_not_ge hK
                                      have hrev :=
                                        ammSwap1X_kGuardRevertsDecoded
                                          hlo houtBound hretBalance0Lo
                                          hretBalance0Bound (by
                                            have hcap : 2 ^ 138 <
                                                UInt256.size := by
                                              norm_num [UInt256.size]
                                            omega)
                                          rd1709 hbadE
                                      have hbadS :
                                          ((Solm.EVM.storageLoad
                                            { initState cA gh bl σ_solm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σS3,
                                              substate := A3,
                                              createdAccounts := cA3 }
                                            I.codeOwner ⟨5⟩).toNat *
                                            (fromByteArrayBigEndian
                                              (retBalance1.extract 0 32) -
                                              (Solm.EVM.storageLoad
                                                { initState cA gh bl σ_solm σ₀
                                                    (Sat256.ofUInt256 g) A I with
                                                  accountMap := σS3,
                                                  substate := A3,
                                                  createdAccounts := cA3 }
                                                I.codeOwner ⟨6⟩).toNat)) /
                                          ((Solm.EVM.storageLoad
                                            { initState cA gh bl σ_solm σ₀
                                                (Sat256.ofUInt256 g) A I with
                                              accountMap := σS3,
                                              substate := A3,
                                              createdAccounts := cA3 }
                                            I.codeOwner ⟨6⟩).toNat +
                                            (fromByteArrayBigEndian
                                              (retBalance1.extract 0 32) -
                                              (Solm.EVM.storageLoad
                                                { initState cA gh bl σ_solm σ₀
                                                    (Sat256.ofUInt256 g) A I with
                                                  accountMap := σS3,
                                                  substate := A3,
                                                  createdAccounts := cA3 }
                                                I.codeOwner ⟨6⟩).toNat)) <
                                          (ammSwap1AmountWord I).toNat := by
                                        rw [hr0S, hr1S, ← hq1, ← hquotNat]
                                        exact hbadE
                                      have hbody :=
                                        ammSwap1SourceKGuardRevert
                                          I b' retBalance0 retBalance1
                                          hsourceQuotient hbadS
                                      exact hrev.reEquivExecutionRevert hcode
                                        (ammDispatch_swap1 hsel)
                                        (ammDecode_swap1_ok hsz68 hbig hcanon)
                                        hbody
                                  · have hmulOverE : UInt256.size ≤
                                        (solcSlotWord σE3 I ⟨5⟩).toNat *
                                          (UInt256.sub q1
                                            (solcSlotWord σE3 I ⟨6⟩)).toNat :=
                                      Nat.le_of_not_lt hmulFitE
                                    have haw : 3 ≤
                                        (ammSwap1Balance1CalldataWords
                                          out retBalance0).toNat := by
                                      rw [ammSwap1Balance1CalldataWords_toNat
                                        out retBalance0 hlo houtBound
                                        hretBalance0Lo hretBalance0Bound]
                                      omega
                                    have hrev :=
                                      ammSwap1X_numeratorOverflow
                                        rd1685 hmulOverE haw
                                    have hslot6 :
                                        solcSlotWord σE3 I ⟨5⟩ =
                                        solcSlotWord σS3 I ⟨5⟩ := by
                                      simpa [solcSlotWord, codeOwnerStorageWord]
                                        using accountMapEquiv_storage_findD
                                          hσ3 I.codeOwner ⟨5⟩ ⟨0⟩
                                    have hmulOverS : UInt256.size ≤
                                        (Solm.EVM.storageLoad
                                          { initState cA gh bl σ_solm σ₀
                                              (Sat256.ofUInt256 g) A I with
                                            accountMap := σS3,
                                            substate := A3,
                                            createdAccounts := cA3 }
                                          I.codeOwner ⟨5⟩).toNat *
                                          (fromByteArrayBigEndian
                                            (retBalance1.extract 0 32) -
                                            (Solm.EVM.storageLoad
                                              { initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I with
                                                accountMap := σS3,
                                                substate := A3,
                                                createdAccounts := cA3 }
                                              I.codeOwner ⟨6⟩).toNat) := by
                                      simpa [Solm.EVM.storageLoad,
                                        Ethereum.State.lookupAccount,
                                        Ethereum.Account.lookupStorage, initState,
                                        solcSlotWord, codeOwnerStorageWord,
                                        ← hslot5, ← hslot6, ← hq1,
                                        usub_toNat (Nat.le_of_lt hInput)]
                                        using hmulOverE
                                    have hbody :=
                                      ammSwap1SourceNumeratorOverflow
                                        I b' retBalance0 retBalance1
                                        hsourceDenominator hmulOverS
                                    exact hrev.reEquivExecutionRevert hcode
                                      (ammDispatch_swap1 hsel)
                                      (ammDecode_swap1_ok hsz68 hbig hcanon)
                                      hbody
                                · have hbadE : q1.toNat ≤
                                      (solcSlotWord σE3 I ⟨6⟩).toNat :=
                                    Nat.le_of_not_gt hInput
                                  have hrev :=
                                    ammSwap1X_inputGuardRevertsDecoded
                                      hlo houtBound hretBalance0Lo
                                      hretBalance0Bound (by
                                        have hcap : 2 ^ 138 <
                                            UInt256.size := by
                                          norm_num [UInt256.size]
                                        omega)
                                      rd1587 hbadE
                                  have hslot5 :
                                      solcSlotWord σE3 I ⟨6⟩ =
                                      solcSlotWord σS3 I ⟨6⟩ := by
                                    simpa [solcSlotWord, codeOwnerStorageWord]
                                      using accountMapEquiv_storage_findD
                                        hσ3 I.codeOwner ⟨6⟩ ⟨0⟩
                                  have hq1 : q1.toNat =
                                      fromByteArrayBigEndian
                                        (retBalance1.extract 0 32) := by
                                    apply UInt256.toNat_ofNat_of_lt
                                    exact fromByteArrayBigEndian_extract0_32_lt
                                      hretBalance1Lo
                                  have hbadS :
                                      fromByteArrayBigEndian
                                        (retBalance1.extract 0 32) ≤
                                      (Solm.EVM.storageLoad
                                        { initState cA gh bl σ_solm σ₀
                                            (Sat256.ofUInt256 g) A I with
                                          accountMap := σS3,
                                          substate := A3,
                                          createdAccounts := cA3 }
                                        I.codeOwner ⟨6⟩).toNat := by
                                    simpa [Solm.EVM.storageLoad,
                                      Ethereum.State.lookupAccount,
                                      Ethereum.Account.lookupStorage, initState,
                                      solcSlotWord, codeOwnerStorageWord,
                                      ← hslot5, ← hq1] using hbadE
                                  have hbody :=
                                    ammSwap1SourceInputGuardRevert
                                      I b' retBalance0 retBalance1
                                      hsourceBalance1 hbadS
                                  exact hrev.reEquivExecutionRevert hcode
                                    (ammDispatch_swap1 hsel)
                                    (ammDecode_swap1_ok hsz68 hbig hcanon)
                                    hbody
                      · have hbad : v ≠
                            UInt256.isZero (UInt256.isZero v) := by
                          intro hnorm
                          exact hcanonBool
                            ((ammBoolNormalized_canonical v).mp hnorm)
                        have hrev :=
                          ammSwap1X_transferDecodeInvalidReverts hbad
                            rd6323
                        have hnot0 : v ≠ ⟨0⟩ := by
                          intro h; exact hcanonBool (Or.inl h)
                        have hnot1 : v ≠ ⟨1⟩ := by
                          intro h; exact hcanonBool (Or.inr h)
                        have hdec : config.externalABI.decode?
                            "transfer" out = none := by
                          rw [ammBurnDecodeTransfer_word hlo
                            (by omega : out.size < 2 ^ 255)]
                          simp [v, hnot0, hnot1]
                        exact ammSwap1TransferDecodeRevertBody
                          hcode hwv hsel hAccounts hsz68 hbig hcanon
                          hpos hliq heq0 heq1 hcallETrue hdec hrev
          · have hliqBad : (solcSlotWord σ_evm I ⟨5⟩).toNat ≤
                (ammSwap1AmountWord I).toNat := by omega
            exact ammSwap1InsufficientLiquidityBody hcode hsize hwv hsel
              hreach hAccounts hsz68 hbig hcanon hpos hliqBad
      · exact (ammSwap1X_noncanon (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hcanon hreach).reEquivDecodingFailed
            hcode hdispatch
            (ammDecode_swap1_none_noncanon hsz68 hbig hcanon)
    · have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (ammSwap1X_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hhuge hreach).reEquivDecodingFailed
          hcode hdispatch (ammDecode_swap1_none_huge hhuge)
  · have hshort : I.calldata.size < 68 := by omega
    exact (ammSwap1X_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach).reEquivDecodingFailed
        hcode hdispatch (ammDecode_swap1_none_short hsz4 hshort)

end Benchmarks.ActAmm
