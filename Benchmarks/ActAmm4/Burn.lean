import Benchmarks.ActAmm4.BurnTrace
import Benchmarks.ActAmm4.BurnSourceCalls
import Benchmarks.ActAmm4.BurnTransfer1Call
import Benchmarks.ActAmm4.BurnTransfer1Decode
import Benchmarks.ActAmm4.BurnSourceBalances
import Benchmarks.ActAmm4.BurnBalance0Call
import Benchmarks.ActAmm4.BurnBalance0Decode
import Benchmarks.ActAmm4.BurnBalance1Decode
import Benchmarks.ActAmm4.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

/-- The burn wrapper, entered at PC 495, refines its Solm transition. -/
theorem amm4BurnBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨495⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4BurnSelector_size hsel
  have hdispatch := amm4Dispatch_burn hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus
      · by_cases hzero : solcSlotWord σ_evm I ⟨0⟩ = ⟨0⟩
        · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hσ : EVMStateEquiv evmE evmS := by
            simpa [evmE, evmS] using
              EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
          have hzeroS : Solm.EVM.storageLoad evmS
              evmS.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩ := by
            rw [show Solm.EVM.storageLoad evmS
                evmS.executionEnv.codeOwner ⟨0⟩ =
                Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨0⟩ from
              (hσ.storageLoad_codeOwner ⟨0⟩).symm]
            simpa [evmE, solcSlotWord, codeOwnerStorageWord] using hzero
          have hbody := amm4BurnSourceZeroSupply evmS I
            (by simpa [evmS, initState] using hwv) hzeroS
          exact (amm4BurnX_zeroSupply (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hcanon hzero hreach)
            |>.reEquivExecutionRevert hcode hdispatch
              (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
        · let evmS := initState cA gh bl σ_solm σ₀
            (Sat256.ofUInt256 g) A I
          have hslot0 : solcSlotWord σ_evm I ⟨0⟩ =
              solcSlotWord σ_solm I ⟨0⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
          have hnonzeroS : Solm.EVM.storageLoad evmS
              evmS.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩ := by
            change solcSlotWord σ_solm I ⟨0⟩ ≠ ⟨0⟩
            intro hz
            exact hzero (hslot0.trans hz)
          have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
              solcSlotWord σ_solm I ⟨5⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
          have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
              solcSlotWord σ_solm I ⟨6⟩ := by
            simpa [solcSlotWord, codeOwnerStorageWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
          obtain ⟨_, _, rd3781⟩ := amm4BurnX_nonzeroSupply
            hsz68 hsize hbig hcanon hzero hreach
          by_cases hfit0 : (amm4BurnLiquidityWord I).toNat *
              (solcSlotWord σ_evm I ⟨5⟩).toNat < UInt256.size
          · obtain ⟨_, _, rd3798⟩ :=
              amm4BurnX_amount0NumeratorOk rd3781 hfit0
            obtain ⟨_, _, rd3811⟩ := amm4BurnX_amount0Ok rd3798 hzero
            have hsourceFit0 : amm4BurnAmount0Numerator evmS I <
                UInt256.size := by
              change (amm4BurnLiquidityWord I).toNat *
                (solcSlotWord σ_solm I ⟨5⟩).toNat < UInt256.size
              rw [← hslot5]
              exact hfit0
            by_cases hfit1 : (amm4BurnLiquidityWord I).toNat *
                (solcSlotWord σ_evm I ⟨6⟩).toNat < UInt256.size
            · obtain ⟨_, _, rd3827⟩ :=
                amm4BurnX_amount1NumeratorOk rd3811 hfit1
              obtain ⟨_, _, rd3840⟩ :=
                amm4BurnX_amount1Ok rd3827 hzero
              have hsourceFit1 : amm4BurnAmount1Numerator evmS I <
                  UInt256.size := by
                change (amm4BurnLiquidityWord I).toNat *
                  (solcSlotWord σ_solm I ⟨6⟩).toNat < UInt256.size
                rw [← hslot6]
                exact hfit1
              by_cases hleSupply : (amm4BurnLiquidityWord I).toNat ≤
                  (solcSlotWord σ_evm I ⟨0⟩).toNat
              · obtain ⟨_, _, rd3863⟩ :=
                  amm4BurnX_supplyStored rd3840 hleSupply hperm
                have hsourceLe : (amm4BurnLiquidityWord I).toNat ≤
                    (Solm.EVM.storageLoad evmS
                      evmS.executionEnv.codeOwner ⟨0⟩).toNat := by
                  change (amm4BurnLiquidityWord I).toNat ≤
                    (solcSlotWord σ_solm I ⟨0⟩).toNat
                  rw [← hslot0]
                  exact hleSupply
                have hprefixSupply := amm4BurnSourceSupplyOk evmS I
                  (by simpa [evmS, initState] using hwv)
                  hnonzeroS hsourceFit0 hsourceFit1 hsourceLe
                let evmE := initState cA gh bl σ_evm σ₀
                  (Sat256.ofUInt256 g) A I
                have hσ : EVMStateEquiv evmE evmS := by
                  simpa [evmE, evmS] using
                    EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
                let supplyE := solcSlotWord σ_evm I ⟨0⟩
                let liq := amm4BurnLiquidityWord I
                have hnewSupply : UInt256.sub supplyE liq =
                    amm4BurnSupplyWord evmS I := by
                  apply u256_inj
                  rw [usub_toNat hleSupply]
                  unfold amm4BurnSupplyWord
                  rw [show Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨0⟩ =
                    solcSlotWord σ_solm I ⟨0⟩ from rfl, ← hslot0]
                  change supplyE.toNat - liq.toNat =
                    (UInt256.ofNat (supplyE.toNat - liq.toNat)).toNat
                  exact (ulit_toNat' _
                    (lt_of_le_of_lt (Nat.sub_le _ _) supplyE.val.isLt)).symm
                let evmE3 := Solm.EVM.storageStore evmE
                  evmE.executionEnv.codeOwner ⟨0⟩
                  (UInt256.sub supplyE liq)
                let evmS3 := amm4BurnAfterSupply evmS I
                have hσSupply : EVMStateEquiv evmE3 evmS3 := by
                  simpa [evmE3, evmS3, amm4BurnAfterSupply] using
                    hσ.storageStore_codeOwner ⟨0⟩ hnewSupply
                have hmapE3 : evmE3.accountMap =
                    sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                      (UInt256.sub supplyE liq) := by
                  simp [evmE3, evmE, storageStore_accountMap, initState]
                obtain ⟨_, _, rd3929⟩ := amm4BurnX_senderLoad rd3863
                have hbalance : solcSlotWord
                    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                      (UInt256.sub supplyE liq)) I
                    (amm4TransferSenderSlot I) =
                    Solm.EVM.storageLoad evmS3
                      evmS3.executionEnv.codeOwner
                      (amm4TransferSenderSlot I) := by
                  rw [← hmapE3]
                  change Solm.EVM.storageLoad evmE3 I.codeOwner
                    (amm4TransferSenderSlot I) = _
                  have howner : evmE3.executionEnv.codeOwner =
                      I.codeOwner := by
                    simp [evmE3, storageStore_executionEnv,
                      evmE, initState]
                  rw [← howner]
                  exact hσSupply.storageLoad_codeOwner
                    (amm4TransferSenderSlot I)
                have hprefixSupply' : ExecBlock config
                    { contract := contract, locals := amm4BurnStore I } evmS
                    amm4BurnSourcePrefixSupply
                    (.ok { contract := contract, locals :=
                      (amm4BurnAfterAmount1Store evmS I) } evmS3) := by
                  simpa [amm4BurnSourcePrefixSupply, evmS3] using hprefixSupply
                let σE3 := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
                  (UInt256.sub supplyE liq)
                by_cases hleSender : liq.toNat ≤
                    (solcSlotWord σE3 I (amm4TransferSenderSlot I)).toNat
                · obtain ⟨_, _, rd3946⟩ :=
                    amm4BurnX_senderStored rd3929
                      (by simpa [σE3, liq] using hleSender) hperm
                  have hsrcS3 : evmS3.executionEnv.source = I.source := by
                    simp [evmS3, amm4BurnAfterSupply,
                      storageStore_executionEnv, evmS, initState]
                  have hsourceLeSender : liq.toNat ≤
                      (Solm.EVM.storageLoad evmS3
                        evmS3.executionEnv.codeOwner
                        (amm4TransferSenderSlot I)).toNat := by
                    rw [← hbalance]
                    exact hleSender
                  have hprefixSender := amm4BurnSourceSenderOk I
                    hprefixSupply' hsrcS3 hsourceLeSender
                  have hnewSender :
                      UInt256.sub
                        (solcSlotWord σE3 I (amm4TransferSenderSlot I)) liq =
                      amm4BurnSenderDebitWord evmS3 I := by
                    apply u256_inj
                    rw [usub_toNat hleSender]
                    unfold amm4BurnSenderDebitWord
                    rw [← hbalance]
                    exact (ulit_toNat' _ (lt_of_le_of_lt
                      (Nat.sub_le _ _)
                      (solcSlotWord σE3 I
                        (amm4TransferSenderSlot I)).val.isLt)).symm
                  let evmE4 := Solm.EVM.storageStore evmE3
                    evmE3.executionEnv.codeOwner
                    (amm4TransferSenderSlot I)
                    (UInt256.sub
                      (solcSlotWord σE3 I (amm4TransferSenderSlot I)) liq)
                  let evmS4 := amm4BurnAfterSender evmS3 I
                  have hσSender : EVMStateEquiv evmE4 evmS4 := by
                    simpa [evmE4, evmS4, amm4BurnAfterSender] using
                      hσSupply.storageStore_codeOwner
                        (amm4TransferSenderSlot I) hnewSender
                  let q0 := UInt256.div
                    (UInt256.mul liq (solcSlotWord σ_evm I ⟨5⟩)) supplyE
                  let q1 := UInt256.div
                    (UInt256.mul liq (solcSlotWord σ_evm I ⟨6⟩)) supplyE
                  let σE4 := sstoreAccountMap I.codeOwner σE3
                    (amm4TransferSenderSlot I)
                    (UInt256.sub
                      (solcSlotWord σE3 I (amm4TransferSenderSlot I)) liq)
                  have hmapE4 : evmE4.accountMap = σE4 := by
                    simp [evmE4, evmE3, evmE, σE4, σE3,
                      storageStore_accountMap, storageStore_executionEnv,
                      initState]
                  have hq0 : q0.toNat = amm4BurnAmount0Value evmS I := by
                    change (UInt256.div
                      (UInt256.mul liq (solcSlotWord σ_evm I ⟨5⟩))
                      supplyE).toNat = _
                    rw [udiv_toNat, u256_mul_toNat,
                      Nat.mod_eq_of_lt (by simpa [liq] using hfit0)]
                    change (amm4BurnLiquidityWord I).toNat *
                      (solcSlotWord σ_evm I ⟨5⟩).toNat /
                      (solcSlotWord σ_evm I ⟨0⟩).toNat =
                      (amm4BurnLiquidityWord I).toNat *
                      (solcSlotWord σ_solm I ⟨5⟩).toNat /
                      (solcSlotWord σ_solm I ⟨0⟩).toNat
                    rw [← hslot5, ← hslot0]
                  have hq1 : q1.toNat = amm4BurnAmount1Value evmS I := by
                    change (UInt256.div
                      (UInt256.mul liq (solcSlotWord σ_evm I ⟨6⟩))
                      supplyE).toNat = _
                    rw [udiv_toNat, u256_mul_toNat,
                      Nat.mod_eq_of_lt (by simpa [liq] using hfit1)]
                    change (amm4BurnLiquidityWord I).toNat *
                      (solcSlotWord σ_evm I ⟨6⟩).toNat /
                      (solcSlotWord σ_evm I ⟨0⟩).toNat =
                      (amm4BurnLiquidityWord I).toNat *
                      (solcSlotWord σ_solm I ⟨6⟩).toNat /
                      (solcSlotWord σ_solm I ⟨0⟩).toNat
                    rw [← hslot6, ← hslot0]
                  obtain ⟨_, _, rd4002⟩ :=
                    amm4BurnX_token0Address rd3946
                  obtain ⟨_, _, rd4024⟩ :=
                    amm4BurnX_token0SelectorMem rd4002
                  obtain ⟨_, _, rd4037⟩ :=
                    amm4BurnX_token0TransferArgs rd4024 hcanon
                  obtain ⟨gasWord, k4050, C4050, rd4050⟩ :=
                    amm4BurnX_token0CallFrame rd4037
                  by_cases hdepth : I.depth = 1024
                  · have hprefixSender' : ExecBlock config
                        { contract := contract, locals := amm4BurnStore I }
                        evmS amm4BurnSourcePrefixSender
                        (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evmS I } evmS4) := by
                      simpa [amm4BurnSourcePrefixSender, evmS4]
                        using hprefixSender
                    have hdepthS4 : evmS4.executionEnv.depth = 1024 := by
                      simpa [evmS4, evmS3, evmS,
                        amm4BurnAfterSender, amm4BurnAfterSupply,
                        storageStore_executionEnv, initState] using hdepth
                    have hbody := amm4BurnSourceToken0DepthRevert
                      I q0 hprefixSender' hdepthS4 hq0 hcanon
                    have hrev := amm4BurnX_token0DepthRevert hdepth rd4050
                    exact hrev.reEquivExecutionRevert hcode hdispatch
                      (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                  · have hdepthLt : I.depth.val < 1024 := by
                      have hlt := I.depth.isLt
                      omega
                    obtain ⟨cA5, σE5, z0, o0, A5, k5, C5,
                      rd4051, hcallE0, ho0size, ho0bound⟩ :=
                      amm4BurnX_token0Call hperm hdepthLt hcanon
                        ⟨gasWord, k4050, C4050, rd4050⟩
                    let evmEcall : EVM.State :=
                      { initState cA gh bl σE4 σ₀
                          (Sat256.ofUInt256 g) A I with accountMap := σE4 }
                    have haccCall : accountMapEquiv evmEcall.accountMap
                        evmS4.accountMap := by
                      change accountMapEquiv σE4 evmS4.accountMap
                      rw [← hmapE4]
                      exact hσSender.accountMap
                    have hσ₀Call : evmEcall.σ₀ = evmS4.σ₀ := by
                      simpa [evmEcall, evmS4, evmS3, evmS, initState]
                        using (amm4BurnPostDebitContext evmS I).1.symm
                    have hcreatedCall : evmS4.createdAccounts =
                        evmEcall.createdAccounts := by
                      simp [evmEcall, evmS4, evmS3, evmS,
                        amm4BurnAfterSender, amm4BurnAfterSupply,
                        storageStore_createdAccounts, initState]
                    have hgenesisCall : evmS4.genesisBlockHeader =
                        evmEcall.genesisBlockHeader := by
                      simpa [evmEcall, evmS4, evmS3, evmS, initState]
                        using (amm4BurnPostDebitContext evmS I).2.1
                    have hblocksCall : evmS4.blocks = evmEcall.blocks := by
                      simpa [evmEcall, evmS4, evmS3, evmS, initState]
                        using (amm4BurnPostDebitContext evmS I).2.2.1
                    have hsubstateCall : evmS4.substate =
                        evmEcall.substate := by
                      simpa [evmEcall, evmS4, evmS3, evmS, initState]
                        using (amm4BurnPostDebitContext evmS I).2.2.2
                    have henvCall : evmS4.executionEnv =
                        evmEcall.executionEnv := by
                      simp [evmEcall, evmS4, evmS3, evmS,
                        amm4BurnAfterSender, amm4BurnAfterSupply,
                        storageStore_executionEnv, initState]
                    obtain ⟨σS5, hcallS0, hσ5⟩ :=
                      amm4TypedCallTransport (evmS := evmS4)
                        hcallE0 haccCall hσ₀Call hcreatedCall
                        hgenesisCall hblocksCall hsubstateCall henvCall
                    have hownerE4 : evmE4.executionEnv.codeOwner =
                        I.codeOwner := by
                      simp [evmE4, evmE3, evmE,
                        storageStore_executionEnv, initState]
                    have hloadE4 : Solm.EVM.storageLoad evmE4
                        evmE4.executionEnv.codeOwner ⟨3⟩ =
                        solcSlotWord σE4 I ⟨3⟩ := by
                      rw [hownerE4]
                      change codeOwnerStorageWord I evmE4.accountMap ⟨3⟩ = _
                      rw [hmapE4]
                    have hword0 : amm4MintToken0Word σE4 I =
                        UInt256.land (Solm.EVM.storageLoad evmS4
                          evmS4.executionEnv.codeOwner ⟨3⟩)
                          solcAddrMask := by
                      change UInt256.land (solcSlotWord σE4 I ⟨3⟩)
                        solcAddrMask = _
                      rw [← hloadE4,
                        hσSender.storageLoad_codeOwner ⟨3⟩]
                    have htarget0 :
                        (EVM.address (AccountAddress.ofUInt256
                          (UInt256.land (Solm.EVM.storageLoad evmS4
                            evmS4.executionEnv.codeOwner ⟨3⟩)
                            solcAddrMask)).val) =
                        AccountAddress.ofUInt256 (amm4MintToken0Word σE4 I) := by
                      rw [hword0]
                      change EVM.address (AccountAddress.ofUInt256
                        (UInt256.land (Solm.EVM.storageLoad evmS4
                          evmS4.executionEnv.codeOwner ⟨3⟩)
                          solcAddrMask)).val = _
                      apply Fin.ext
                      change (AccountAddress.ofUInt256
                        (UInt256.land (Solm.EVM.storageLoad evmS4
                          evmS4.executionEnv.codeOwner ⟨3⟩)
                          solcAddrMask)).val % EVM.twoPow 160 = _
                      exact Nat.mod_eq_of_lt
                        (AccountAddress.ofUInt256
                          (UInt256.land (Solm.EVM.storageLoad evmS4
                            evmS4.executionEnv.codeOwner ⟨3⟩)
                            solcAddrMask)).isLt
                    let evmS5 : EVM.State := { evmS4 with
                      accountMap := σS5, substate := A5,
                      createdAccounts := cA5 }
                    have hcallS0' : typedCallViaEVM config evmS4
                        (EVM.address (AccountAddress.ofUInt256
                          (UInt256.land (Solm.EVM.storageLoad evmS4
                            evmS4.executionEnv.codeOwner ⟨3⟩)
                            solcAddrMask)).val)
                        "transfer" 0
                        [.int (Int.ofNat (amm4BurnAmount0Value evmS I)),
                          .address (AccountAddress.ofUInt256
                            (amm4BurnToWord I))]
                        (z0, evmS5, o0) true := by
                      rw [htarget0, ← hq0]
                      simpa [evmS5] using hcallS0
                    have hprefixSender' : ExecBlock config
                        { contract := contract, locals := amm4BurnStore I }
                        evmS amm4BurnSourcePrefixSender
                        (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evmS I } evmS4) := by
                      simpa [amm4BurnSourcePrefixSender, evmS4]
                        using hprefixSender
                    by_cases hz0 : z0 = false
                    · have rdFail := by simpa [hz0] using rd4051
                      have hrev := amm4BurnX_token0CallFailed rdFail ho0size
                        (by simp only [List.length_cons, List.length_nil]; omega)
                      have hcallSFail := by simpa only [hz0] using hcallS0'
                      have hbody := amm4BurnSourceToken0CallFailed
                        I o0 hprefixSender' hcallSFail
                      exact hrev.reEquivExecutionRevert hcode hdispatch
                        (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                    · have hz0true : z0 = true := by cases z0 <;> simp_all
                      have rdSuccess := by
                        simpa [hz0true, amm4BurnToken0PostCallMem]
                          using rd4051
                      obtain ⟨_, _, rd4070⟩ :=
                        amm4BurnX_token0CallSucceeded rdSuccess
                      obtain ⟨_, _, rd6025⟩ :=
                        amm4BurnX_token0ToDecoder ho0size rd4070
                      have hcallSTrue := by
                        simpa only [hz0true] using hcallS0'
                      by_cases hshort0 : o0.size < 32
                      · have hrev :=
                          amm4BurnX_token0DecodeShortReverts hshort0 rd6025
                        have hbody := amm4BurnSourceToken0DecodeRevert
                          I o0 hprefixSender' hcallSTrue
                          (amm4BurnDecodeTransfer_short hshort0)
                        exact hrev.reEquivExecutionRevert hcode hdispatch
                          (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                      · have hlo0 : 32 ≤ o0.size := by omega
                        obtain ⟨_, _, rd5983⟩ :=
                          amm4BurnX_token0DecodeWord hlo0 ho0bound rd6025
                        let v0 := UInt256.ofNat
                          (fromByteArrayBigEndian (o0.extract 0 32))
                        by_cases hbool0 : v0 = ⟨0⟩ ∨ v0 = ⟨1⟩
                        · obtain ⟨_, _, rd4103⟩ :=
                            amm4BurnX_token0DecodeOk hbool0 rd5983
                          let b0 : Bool := if v0 = ⟨0⟩ then false else true
                          have hdecSome :
                              config.externalABI.decode? "transfer" o0 =
                                some [.bool b0] := by
                            rw [amm4BurnDecodeTransfer_word hlo0
                              (by omega : o0.size < 2 ^ 255)]
                            rcases hbool0 with hv0 | hv1
                            · simp [v0, b0, hv0]
                            · have hne : v0 ≠ ⟨0⟩ := by
                                rw [hv1]
                                decide
                              simp [v0, b0, hv1, hne, UInt256.size]
                          have hprefix0 := amm4BurnSourceToken0CallOk
                            I o0 b0 hprefixSender' hcallSTrue hdecSome
                          obtain ⟨_, _, rd4159⟩ :=
                            amm4BurnX_token1Address rd4103
                          obtain ⟨_, _, rd4181⟩ :=
                            amm4BurnX_token1SelectorMem hlo0 ho0bound rd4159
                          obtain ⟨_, _, rd4194⟩ :=
                            amm4BurnX_token1TransferArgs hlo0 ho0bound hcanon rd4181
                          obtain ⟨gasWord1, k4207, C4207, rd4207⟩ :=
                            amm4BurnX_token1CallFrame hlo0 ho0bound rd4194
                          obtain ⟨cA6, σE6, z1, o1, A6, k6, C6,
                            rd4208, hcallE1, ho1size, ho1bound⟩ :=
                            amm4BurnX_token1Call (Apre := A5)
                              hperm hdepthLt hlo0 ho0bound
                              hcanon ⟨gasWord1, k4207, C4207, rd4207⟩
                          let evmEcall1 : EVM.State :=
                            { initState cA5 gh bl σE5 σ₀
                                (Sat256.ofUInt256 g) A5 I with
                              accountMap := σE5, substate := A5,
                              createdAccounts := cA5 }
                          have haccCall1 : accountMapEquiv evmEcall1.accountMap
                              evmS5.accountMap := by
                            simpa [evmEcall1, evmS5] using hσ5
                          have hσ₀Call1 : evmEcall1.σ₀ = evmS5.σ₀ := by
                            simpa [evmEcall1, evmS5, evmEcall] using
                              hσ₀Call
                          have hcreatedCall1 : evmS5.createdAccounts =
                              evmEcall1.createdAccounts := by
                            simp [evmEcall1, evmS5]
                          have hgenesisCall1 : evmS5.genesisBlockHeader =
                              evmEcall1.genesisBlockHeader := by
                            simpa [evmEcall1, evmS5, evmEcall] using
                              hgenesisCall
                          have hblocksCall1 : evmS5.blocks =
                              evmEcall1.blocks := by
                            simpa [evmEcall1, evmS5, evmEcall] using
                              hblocksCall
                          have hsubstateCall1 : evmS5.substate =
                              evmEcall1.substate := by
                            simp [evmEcall1, evmS5]
                          have henvCall1 : evmS5.executionEnv =
                              evmEcall1.executionEnv := by
                            simpa [evmEcall1, evmS5, evmEcall] using
                              henvCall
                          obtain ⟨σS6, hcallS1, hσ6⟩ :=
                            amm4TypedCallTransport (evmS := evmS5)
                              hcallE1 haccCall1 hσ₀Call1 hcreatedCall1
                              hgenesisCall1 hblocksCall1 hsubstateCall1
                              henvCall1
                          have hslot4 : solcSlotWord σE5 I ⟨4⟩ =
                              solcSlotWord σS5 I ⟨4⟩ := by
                            simpa [solcSlotWord, codeOwnerStorageWord,
                              evmS5] using
                              accountMapEquiv_storage_findD hσ5
                                I.codeOwner ⟨4⟩ ⟨0⟩
                          have hword1 : amm4MintToken1Word σE5 I =
                              amm4MintToken1Word σS5 I :=
                            congrArg (fun w => UInt256.land w solcAddrMask)
                              hslot4
                          have hloadS5 : Solm.EVM.storageLoad evmS5
                              evmS5.executionEnv.codeOwner ⟨4⟩ =
                              solcSlotWord σS5 I ⟨4⟩ := by
                            have hownerS5 : evmS5.executionEnv.codeOwner =
                                I.codeOwner := by
                              simpa [evmS5] using
                                (show evmS4.executionEnv.codeOwner =
                                  I.codeOwner by
                                  simp [evmS4, evmS3, evmS,
                                    amm4BurnAfterSender, amm4BurnAfterSupply,
                                    storageStore_executionEnv, initState])
                            rw [hownerS5]
                            change codeOwnerStorageWord I evmS5.accountMap ⟨4⟩ = _
                            rfl
                          have htarget1 :
                              (EVM.address (AccountAddress.ofUInt256
                                (UInt256.land (Solm.EVM.storageLoad evmS5
                                  evmS5.executionEnv.codeOwner ⟨4⟩)
                                  solcAddrMask)).val) =
                              AccountAddress.ofUInt256
                                (amm4MintToken1Word σE5 I) := by
                            rw [hloadS5, ← amm4MintToken1Word, hword1]
                            change EVM.address (AccountAddress.ofUInt256
                              (amm4MintToken1Word σS5 I)).val = _
                            apply Fin.ext
                            change (AccountAddress.ofUInt256
                              (amm4MintToken1Word σS5 I)).val %
                              EVM.twoPow 160 = _
                            exact Nat.mod_eq_of_lt
                              (AccountAddress.ofUInt256
                                (amm4MintToken1Word σS5 I)).isLt
                          let evmS6 : EVM.State := { evmS5 with
                            accountMap := σS6, substate := A6,
                            createdAccounts := cA6 }
                          have hcallS1' : typedCallViaEVM config evmS5
                              (EVM.address (AccountAddress.ofUInt256
                                (UInt256.land (Solm.EVM.storageLoad evmS5
                                  evmS5.executionEnv.codeOwner ⟨4⟩)
                                  solcAddrMask)).val)
                              "transfer" 0
                              [.int (Int.ofNat (amm4BurnAmount1Value evmS I)),
                                .address (AccountAddress.ofUInt256
                                  (amm4BurnToWord I))]
                              (z1, evmS6, o1) true := by
                            rw [htarget1, ← hq1]
                            simpa [evmS6, evmEcall1] using hcallS1
                          by_cases hz1 : z1 = false
                          · have rdFail := by simpa [hz1] using rd4208
                            have hrev := amm4BurnX_token1CallFailed rdFail
                              ho1size
                              (by simp only [List.length_cons, List.length_nil]; omega)
                            have hcallSFail := by
                              simpa only [hz1] using hcallS1'
                            have hbody := amm4BurnSourceToken1CallFailed
                              I o0 o1 b0 hprefix0 hcallSFail
                            exact hrev.reEquivExecutionRevert hcode hdispatch
                              (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                          · have hz1true : z1 = true := by
                              cases z1 <;> simp_all
                            have rdSuccess1 := by
                              simpa [hz1true, amm4BurnToken1PostCallMem]
                                using rd4208
                            obtain ⟨_, _, rd4227⟩ :=
                              amm4BurnX_token1CallSucceeded rdSuccess1
                            obtain ⟨_, _, rd6025b⟩ :=
                              amm4BurnX_token1ToDecoder hlo0 ho0bound
                                ho1size rd4227
                            have hcallS1True := by
                              simpa only [hz1true] using hcallS1'
                            by_cases hshort1 : o1.size < 32
                            · have hrev :=
                                amm4BurnX_token1DecodeShortReverts
                                  hlo0 ho0bound hshort1 rd6025b
                              have hbody :=
                                amm4BurnSourceToken1DecodeRevert
                                  I o1 b0 hprefix0 hcallS1True
                                  (amm4BurnDecodeTransfer_short hshort1)
                              exact hrev.reEquivExecutionRevert hcode hdispatch
                                (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                            · have hlo1 : 32 ≤ o1.size := by omega
                              obtain ⟨_, _, rd5983b⟩ :=
                                amm4BurnX_token1DecodeWord hlo0 ho0bound
                                  hlo1 ho1bound rd6025b
                              let v1 := UInt256.ofNat
                                (fromByteArrayBigEndian (o1.extract 0 32))
                              by_cases hbool1 : v1 = ⟨0⟩ ∨ v1 = ⟨1⟩
                              · obtain ⟨_, _, rd4260⟩ :=
                                  amm4BurnX_token1DecodeOk hbool1 rd5983b
                                let b1 : Bool := if v1 = ⟨0⟩ then false else true
                                have hdecSome1 :
                                    config.externalABI.decode? "transfer" o1 =
                                      some [.bool b1] := by
                                  rw [amm4BurnDecodeTransfer_word hlo1
                                    (by omega : o1.size < 2 ^ 255)]
                                  rcases hbool1 with hv0 | hv1
                                  · simp [v1, b1, hv0]
                                  · have hne : v1 ≠ ⟨0⟩ := by
                                      rw [hv1]
                                      decide
                                    simp [v1, b1, hv1, hne, UInt256.size]
                                have hprefix1 := amm4BurnSourceToken1CallOk
                                  I o1 b0 b1 hprefix0 hcallS1True hdecSome1
                                have hprefixTransfers : ExecBlock config
                                    { contract := contract,
                                      locals := amm4BurnStore I }
                                    evmS amm4BurnSourcePrefixTransfers
                                    (.ok { contract := contract, locals :=
                                      amm4BurnAfterTransfer1Store evmS I b0 b1 }
                                      evmS6) := by
                                  simpa [amm4BurnSourcePrefixTransfers] using hprefix1
                                obtain ⟨_, _, rd4316⟩ :=
                                  amm4BurnX_balance0Address rd4260
                                obtain ⟨_, _, rd4337⟩ :=
                                  amm4BurnX_balance0SelectorMem
                                    hlo0 ho0bound ho1bound rd4316
                                obtain ⟨_, _, rd4349⟩ :=
                                  amm4BurnX_balance0ArgMem rd4337
                                obtain ⟨gasWord2, k4361, C4361, rd4361⟩ :=
                                  amm4BurnX_balance0CallFrame
                                    hlo0 ho0bound hlo1 ho1bound rd4349
                                obtain ⟨cA7, σE7, z2, o2, A7, k7, C7,
                                  rd4362, hcallE2, ho2size, ho2bound⟩ :=
                                  amm4BurnX_balance0Staticcall (Apre := A6)
                                    hlo0 ho0bound hlo1 ho1bound hdepthLt
                                    ⟨gasWord2, k4361, C4361, rd4361⟩
                                let evmEcall2 : EVM.State :=
                                  { initState cA6 gh bl σE6 σ₀
                                      (Sat256.ofUInt256 g) A6 I with
                                    accountMap := σE6, substate := A6,
                                    createdAccounts := cA6 }
                                have haccCall2 : accountMapEquiv
                                    evmEcall2.accountMap evmS6.accountMap := by
                                  simpa [evmEcall2, evmS6] using hσ6
                                have hσ₀Call2 : evmEcall2.σ₀ = evmS6.σ₀ := by
                                  simpa [evmEcall2, evmS6, evmEcall1, evmS5]
                                    using hσ₀Call1
                                have hcreatedCall2 : evmS6.createdAccounts =
                                    evmEcall2.createdAccounts := by
                                  simp [evmEcall2, evmS6]
                                have hgenesisCall2 :
                                    evmS6.genesisBlockHeader =
                                    evmEcall2.genesisBlockHeader := by
                                  simpa [evmEcall2, evmS6, evmEcall1, evmS5]
                                    using hgenesisCall1
                                have hblocksCall2 : evmS6.blocks =
                                    evmEcall2.blocks := by
                                  simpa [evmEcall2, evmS6, evmEcall1, evmS5]
                                    using hblocksCall1
                                have hsubstateCall2 : evmS6.substate =
                                    evmEcall2.substate := by
                                  simp [evmEcall2, evmS6]
                                have henvCall2 : evmS6.executionEnv =
                                    evmEcall2.executionEnv := by
                                  simpa [evmEcall2, evmS6, evmEcall1, evmS5]
                                    using henvCall1
                                obtain ⟨σS7, hcallS2, hσ7⟩ :=
                                  amm4TypedCallStaticTransport (evmS := evmS6)
                                    hcallE2 haccCall2 hσ₀Call2
                                    hcreatedCall2 hgenesisCall2 hblocksCall2
                                    hsubstateCall2 henvCall2
                                have hslot3 : solcSlotWord σE6 I ⟨3⟩ =
                                    solcSlotWord σS6 I ⟨3⟩ := by
                                  simpa [solcSlotWord, codeOwnerStorageWord,
                                    evmS6] using
                                    accountMapEquiv_storage_findD hσ6
                                      I.codeOwner ⟨3⟩ ⟨0⟩
                                have hword2 : amm4MintToken0Word σE6 I =
                                    amm4MintToken0Word σS6 I :=
                                  congrArg
                                    (fun w => UInt256.land w solcAddrMask)
                                    hslot3
                                have hownerS6 : evmS6.executionEnv.codeOwner =
                                    I.codeOwner := by
                                  simpa [evmS6, evmS5] using
                                    (show evmS4.executionEnv.codeOwner =
                                      I.codeOwner by
                                      simp [evmS4, evmS3, evmS,
                                        amm4BurnAfterSender, amm4BurnAfterSupply,
                                        storageStore_executionEnv, initState])
                                have hloadS6 : Solm.EVM.storageLoad evmS6
                                    evmS6.executionEnv.codeOwner ⟨3⟩ =
                                    solcSlotWord σS6 I ⟨3⟩ := by
                                  rw [hownerS6]
                                  change codeOwnerStorageWord I
                                    evmS6.accountMap ⟨3⟩ = _
                                  rfl
                                have htarget2 :
                                    (EVM.address (AccountAddress.ofUInt256
                                      (UInt256.land (Solm.EVM.storageLoad evmS6
                                        evmS6.executionEnv.codeOwner ⟨3⟩)
                                        solcAddrMask)).val) =
                                    AccountAddress.ofUInt256
                                      (amm4MintToken0Word σE6 I) := by
                                  rw [hloadS6, ← amm4MintToken0Word, hword2]
                                  change EVM.address
                                    (AccountAddress.ofUInt256
                                      (amm4MintToken0Word σS6 I)).val = _
                                  apply Fin.ext
                                  change (AccountAddress.ofUInt256
                                    (amm4MintToken0Word σS6 I)).val %
                                    EVM.twoPow 160 = _
                                  exact Nat.mod_eq_of_lt
                                    (AccountAddress.ofUInt256
                                      (amm4MintToken0Word σS6 I)).isLt
                                let evmS7 : EVM.State := { evmS6 with
                                  accountMap := σS7, substate := A7,
                                  createdAccounts := cA7 }
                                have hcallS2' : typedCallViaEVM config evmS6
                                    (EVM.address (AccountAddress.ofUInt256
                                      (UInt256.land (Solm.EVM.storageLoad evmS6
                                        evmS6.executionEnv.codeOwner ⟨3⟩)
                                        solcAddrMask)).val)
                                    "balanceOf" 0
                                    [.address evmS6.executionEnv.codeOwner]
                                    (z2, evmS7, o2) false := by
                                  rw [htarget2, hownerS6]
                                  simpa [evmS7, evmEcall2, initState]
                                    using hcallS2
                                by_cases hz2 : z2 = false
                                · have rdFail := by simpa [hz2] using rd4362
                                  have hrev := amm4BurnX_balance0CallFailed
                                    rdFail ho2size
                                    (by simp only [List.length_cons,
                                      List.length_nil]; omega)
                                  have hcallSFail := by
                                    simpa only [hz2] using hcallS2'
                                  have hbody := amm4BurnSourceBalance0CallFailed
                                    I o2 b0 b1 hprefixTransfers hcallSFail
                                  exact hrev.reEquivExecutionRevert
                                    hcode hdispatch
                                    (amm4Decode_burn_ok hsz68 hbig hcanon)
                                    hbody
                                · have hz2true : z2 = true := by
                                    cases z2 <;> simp_all
                                  have rdSuccess2 := by
                                    simpa [hz2true, amm4BurnBalance0PostCallMem]
                                      using rd4362
                                  obtain ⟨_, _, rd4381⟩ :=
                                    amm4BurnX_balance0CallSucceeded rdSuccess2
                                  obtain ⟨_, _, rd5415⟩ :=
                                    amm4BurnX_balance0ToDecoder
                                      hlo0 ho0bound hlo1 ho1bound ho2size
                                      rd4381
                                  have hcallS2True := by
                                    simpa only [hz2true] using hcallS2'
                                  by_cases hshort2 : o2.size < 32
                                  · have hrev :=
                                      amm4BurnX_balance0DecodeShortReverts
                                        hlo0 ho0bound ho1bound hshort2 rd5415
                                    have hbody :=
                                      amm4BurnSourceBalance0DecodeRevert
                                        I o2 b0 b1 hprefixTransfers hcallS2True
                                        (amm4MintDecodeBalance_short hshort2)
                                    exact hrev.reEquivExecutionRevert
                                      hcode hdispatch
                                      (amm4Decode_burn_ok hsz68 hbig hcanon)
                                      hbody
                                  · have hlo2 : 32 ≤ o2.size := by omega
                                    obtain ⟨_, _, rd4412⟩ :=
                                      amm4BurnX_balance0DecodeOk
                                        hlo0 ho0bound hlo1 ho1bound
                                        hlo2 ho2bound rd5415
                                    have hprefixBalance0 :=
                                      amm4BurnSourceBalance0CallOk I o2 b0 b1
                                        hprefixTransfers hcallS2True
                                        hlo2 ho2bound
                                    have hprefixReserve0 :=
                                      amm4BurnSourceReserve0Ok I o2 b0 b1
                                        hprefixBalance0 hlo2
                                    obtain ⟨_, _, rd4419⟩ :=
                                      amm4BurnX_balance0ReserveStored
                                        rd4412 hperm
                                    let σE8 := sstoreAccountMap I.codeOwner
                                      σE7 ⟨5⟩ (amm4BurnReserve0Word o2)
                                    let evmS8 := amm4BurnAfterReserve0 evmS7 o2
                                    have hownerS7 : evmS7.executionEnv.codeOwner =
                                        I.codeOwner := by
                                      simpa [evmS7] using hownerS6
                                    have hσ8 : accountMapEquiv σE8
                                        evmS8.accountMap := by
                                      simpa [σE8, evmS8, amm4BurnAfterReserve0,
                                        storageStore_accountMap, hownerS7,
                                        hownerS6,
                                        evmS7] using
                                        accountMapEquiv_sstoreAccountMap
                                          I.codeOwner ⟨5⟩
                                          (amm4BurnReserve0Word o2) hσ7
                                    obtain ⟨_, _, rd4475⟩ :=
                                      amm4BurnX_balance1Address rd4419
                                    obtain ⟨_, _, rd4496⟩ :=
                                      amm4BurnX_balance1SelectorMem
                                        hlo0 ho0bound hlo1 ho1bound
                                        ho2bound rd4475
                                    obtain ⟨_, _, rd4508⟩ :=
                                      amm4BurnX_balance1ArgMem rd4496
                                    obtain ⟨gasWord3, k4520, C4520,
                                      rd4520⟩ :=
                                      amm4BurnX_balance1CallFrame
                                        hlo0 ho0bound hlo1 ho1bound
                                        hlo2 ho2bound rd4508
                                    obtain ⟨cA9, σE9, z3, o3, A9, k9, C9,
                                      rd4521, hcallE3, ho3size, ho3bound⟩ :=
                                      amm4BurnX_balance1Staticcall (Apre := A7)
                                        hlo0 ho0bound hlo1 ho1bound
                                        hlo2 ho2bound hdepthLt
                                        ⟨gasWord3, k4520, C4520, rd4520⟩
                                    let evmEcall3 : EVM.State :=
                                      { initState cA7 gh bl σE8 σ₀
                                          (Sat256.ofUInt256 g) A7 I with
                                        accountMap := σE8, substate := A7,
                                        createdAccounts := cA7 }
                                    have haccCall3 : accountMapEquiv
                                        evmEcall3.accountMap
                                        evmS8.accountMap := by
                                      simpa [evmEcall3] using hσ8
                                    have hσ₀Call3 : evmEcall3.σ₀ =
                                        evmS8.σ₀ := by
                                      have hbase : evmS6.σ₀ = σ₀ := by
                                        simpa [evmEcall2, initState] using
                                          hσ₀Call2.symm
                                      have hstore : evmS8.σ₀ =
                                          evmS7.σ₀ := by
                                        simpa [evmS8, amm4BurnAfterReserve0]
                                          using
                                            (amm4StorageStore_preserves_call_context
                                              evmS7 evmS7.executionEnv.codeOwner
                                              ⟨5⟩ (amm4BurnReserve0Word o2)).1
                                      simp [evmEcall3, hstore, evmS7, hbase,
                                        initState]
                                    have hcreatedCall3 :
                                        evmS8.createdAccounts =
                                        evmEcall3.createdAccounts := by
                                      simp [evmEcall3, evmS8,
                                        amm4BurnAfterReserve0, evmS7,
                                        storageStore_createdAccounts]
                                    have hgenesisCall3 :
                                        evmS8.genesisBlockHeader =
                                        evmEcall3.genesisBlockHeader := by
                                      have hbase : evmS6.genesisBlockHeader =
                                          gh := by
                                        simpa [evmEcall2, initState] using
                                          hgenesisCall2
                                      have hstore : evmS8.genesisBlockHeader =
                                          evmS7.genesisBlockHeader := by
                                        simpa [evmS8, amm4BurnAfterReserve0]
                                          using
                                            (amm4StorageStore_preserves_call_context
                                              evmS7 evmS7.executionEnv.codeOwner
                                              ⟨5⟩ (amm4BurnReserve0Word o2)).2.1
                                      simp [evmEcall3, hstore, evmS7, hbase,
                                        initState]
                                    have hblocksCall3 : evmS8.blocks =
                                        evmEcall3.blocks := by
                                      have hbase : evmS6.blocks = bl := by
                                        simpa [evmEcall2, initState] using
                                          hblocksCall2
                                      have hstore : evmS8.blocks =
                                          evmS7.blocks := by
                                        simpa [evmS8, amm4BurnAfterReserve0]
                                          using
                                            (amm4StorageStore_preserves_call_context
                                              evmS7 evmS7.executionEnv.codeOwner
                                              ⟨5⟩ (amm4BurnReserve0Word o2)).2.2.1
                                      simp [evmEcall3, hstore, evmS7, hbase,
                                        initState]
                                    have hsubstateCall3 : evmS8.substate =
                                        evmEcall3.substate := by
                                      have hstore : evmS8.substate =
                                          evmS7.substate := by
                                        simpa [evmS8, amm4BurnAfterReserve0]
                                          using
                                            (amm4StorageStore_preserves_call_context
                                              evmS7 evmS7.executionEnv.codeOwner
                                              ⟨5⟩ (amm4BurnReserve0Word o2)).2.2.2
                                      simp [evmEcall3, hstore, evmS7]
                                    have henvCall3 : evmS8.executionEnv =
                                        evmEcall3.executionEnv := by
                                      have hbase : evmS6.executionEnv = I := by
                                        simpa [evmEcall2, initState] using
                                          henvCall2
                                      simp [evmEcall3, evmS8,
                                        amm4BurnAfterReserve0, evmS7,
                                        storageStore_executionEnv, hbase,
                                        initState]
                                    obtain ⟨σS9, hcallS3, hσ9⟩ :=
                                      amm4TypedCallStaticTransport
                                        (evmS := evmS8)
                                        hcallE3 haccCall3 hσ₀Call3
                                        hcreatedCall3 hgenesisCall3
                                        hblocksCall3 hsubstateCall3 henvCall3
                                    have hslot4 : solcSlotWord σE8 I ⟨4⟩ =
                                        solcSlotWord evmS8.accountMap I ⟨4⟩ := by
                                      simpa [solcSlotWord,
                                        codeOwnerStorageWord] using
                                        accountMapEquiv_storage_findD hσ8
                                          I.codeOwner ⟨4⟩ ⟨0⟩
                                    have hword3 : amm4MintToken1Word σE8 I =
                                        amm4MintToken1Word
                                          evmS8.accountMap I :=
                                      congrArg
                                        (fun w => UInt256.land w solcAddrMask)
                                        hslot4
                                    have hownerS8 :
                                        evmS8.executionEnv.codeOwner =
                                        I.codeOwner := by
                                      simpa [evmS8, amm4BurnAfterReserve0,
                                        storageStore_executionEnv]
                                        using hownerS7
                                    have hloadS8 : Solm.EVM.storageLoad evmS8
                                        evmS8.executionEnv.codeOwner ⟨4⟩ =
                                        solcSlotWord evmS8.accountMap I ⟨4⟩ := by
                                      rw [hownerS8]
                                      change codeOwnerStorageWord I
                                        evmS8.accountMap ⟨4⟩ = _
                                      rfl
                                    have htarget3 :
                                        (EVM.address (AccountAddress.ofUInt256
                                          (UInt256.land (Solm.EVM.storageLoad
                                            evmS8
                                            evmS8.executionEnv.codeOwner ⟨4⟩)
                                            solcAddrMask)).val) =
                                        AccountAddress.ofUInt256
                                          (amm4MintToken1Word σE8 I) := by
                                      rw [hloadS8, ← amm4MintToken1Word,
                                        hword3]
                                      change EVM.address
                                        (AccountAddress.ofUInt256
                                          (amm4MintToken1Word
                                            evmS8.accountMap I)).val = _
                                      apply Fin.ext
                                      change (AccountAddress.ofUInt256
                                        (amm4MintToken1Word
                                          evmS8.accountMap I)).val %
                                        EVM.twoPow 160 = _
                                      exact Nat.mod_eq_of_lt
                                        (AccountAddress.ofUInt256
                                          (amm4MintToken1Word
                                            evmS8.accountMap I)).isLt
                                    let evmS9 : EVM.State := { evmS8 with
                                      accountMap := σS9, substate := A9,
                                      createdAccounts := cA9 }
                                    have hcallS3' : typedCallViaEVM config
                                        evmS8
                                        (EVM.address (AccountAddress.ofUInt256
                                          (UInt256.land (Solm.EVM.storageLoad
                                            evmS8
                                            evmS8.executionEnv.codeOwner ⟨4⟩)
                                            solcAddrMask)).val)
                                        "balanceOf" 0
                                        [.address evmS8.executionEnv.codeOwner]
                                        (z3, evmS9, o3) false := by
                                      rw [htarget3, hownerS8]
                                      simpa [evmS9, evmEcall3, initState]
                                        using hcallS3
                                    have hprefixReserve0' : ExecBlock config
                                        { contract := contract, locals := amm4BurnStore I }
                                        evmS amm4BurnSourcePrefixReserve0
                                        (.ok { contract := contract, locals :=
                                          amm4BurnAfterBalance0Store evmS I b0 b1 o2 }
                                          evmS8) := by
                                      simpa [amm4BurnSourcePrefixReserve0,
                                        evmS8] using hprefixReserve0
                                    by_cases hz3 : z3 = false
                                    · have rdFail := by
                                        simpa [hz3] using rd4521
                                      have hrev :=
                                        amm4BurnX_balance1CallFailed
                                          rdFail ho3size
                                          (by simp only [List.length_cons,
                                            List.length_nil]; omega)
                                      have hcallSFail := by
                                        simpa only [hz3] using hcallS3'
                                      have hbody :=
                                        amm4BurnSourceBalance1CallFailed
                                          I o2 o3 b0 b1 hprefixReserve0'
                                          hcallSFail
                                      exact hrev.reEquivExecutionRevert
                                        hcode hdispatch
                                        (amm4Decode_burn_ok hsz68 hbig hcanon)
                                        hbody
                                    · have hz3true : z3 = true := by
                                        cases z3 <;> simp_all
                                      have rdSuccess3 := by
                                        simpa [hz3true,
                                          amm4BurnBalance1PostCallMem]
                                          using rd4521
                                      obtain ⟨_, _, rd4540⟩ :=
                                        amm4BurnX_balance1CallSucceeded
                                          rdSuccess3
                                      obtain ⟨_, _, rd5415c⟩ :=
                                        amm4BurnX_balance1ToDecoder
                                          hlo0 ho0bound hlo1 ho1bound
                                          hlo2 ho2bound ho3size rd4540
                                      have hcallS3True := by
                                        simpa only [hz3true] using hcallS3'
                                      by_cases hshort3 : o3.size < 32
                                      · have hrev :=
                                          amm4BurnX_balance1DecodeShortReverts
                                            hlo0 ho0bound ho1bound ho2bound
                                            hshort3 rd5415c
                                        have hbody :=
                                          amm4BurnSourceBalance1DecodeRevert
                                            I o2 o3 b0 b1 hprefixReserve0'
                                            hcallS3True
                                            (amm4MintDecodeBalance_short hshort3)
                                        exact hrev.reEquivExecutionRevert
                                          hcode hdispatch
                                          (amm4Decode_burn_ok hsz68 hbig hcanon)
                                          hbody
                                      · have hlo3 : 32 ≤ o3.size := by omega
                                        obtain ⟨_, _, rd4571⟩ :=
                                          amm4BurnX_balance1DecodeOk
                                            hlo0 ho0bound hlo1 ho1bound
                                            hlo2 ho2bound hlo3 ho3bound rd5415c
                                        have hprefixBalance1 :=
                                          amm4BurnSourceBalance1CallOk
                                            I o2 o3 b0 b1 hprefixReserve0'
                                            hcallS3True hlo3 ho3bound
                                        have hbody :=
                                          amm4BurnSourceReserve1Ok
                                            I o2 o3 b0 b1 hprefixBalance1 hlo3
                                        obtain ⟨_, _, rd4582⟩ :=
                                          amm4BurnX_balance1ReserveStored
                                            rd4571 hperm
                                        have hret :=
                                          amm4BurnX_returnAfterBalances rd4582
                                        let evmE9 : EVM.State :=
                                          { initState cA9 gh bl σE9 σ₀
                                              (Sat256.ofUInt256 g) A9 I with
                                            accountMap := σE9, substate := A9,
                                            createdAccounts := cA9 }
                                        have hState9 : EVMStateEquiv
                                            evmE9 evmS9 := by
                                          refine ⟨?_, ?_, ?_⟩
                                          · simpa [evmE9, evmS9, initState]
                                              using henvCall3.symm
                                          · simp [evmE9, evmS9]
                                          · simpa [evmE9, evmS9] using hσ9
                                        let evmE10 :=
                                          amm4BurnAfterReserve1 evmE9 o3
                                        let evmS10 :=
                                          amm4BurnAfterReserve1 evmS9 o3
                                        have hState10 : EVMStateEquiv
                                            evmE10 evmS10 := by
                                          simpa [evmE10, evmS10,
                                            amm4BurnAfterReserve1] using
                                            hState9.storageStore_codeOwner
                                              ⟨6⟩ rfl
                                        have hownerE9 :
                                            evmE9.executionEnv.codeOwner =
                                            I.codeOwner := by
                                          simp [evmE9, initState]
                                        have hmapE10 : evmE10.accountMap =
                                            sstoreAccountMap I.codeOwner σE9
                                              ⟨6⟩
                                              (amm4BurnReserve1Word o3) := by
                                          simp [evmE10,
                                            amm4BurnAfterReserve1,
                                            storageStore_accountMap,
                                            hownerE9, evmE9, initState]
                                        have hcreated10 : cA9 =
                                            evmE10.createdAccounts := by
                                          simp [evmE10,
                                            amm4BurnAfterReserve1,
                                            storageStore_createdAccounts,
                                            evmE9]
                                        have henc : returnEquiv
                                            ByteArray.empty none
                                            burnTransition.returnType := by
                                          rw [show burnTransition.returnType =
                                            [] by rfl]
                                          exact returnEquiv.fallthrough rfl
                                            (by rfl) (by native_decide)
                                        exact hret
                                          |>.reEquivExecutionGenEVMStateEquiv
                                            hcode hdispatch
                                            (amm4Decode_burn_ok
                                              hsz68 hbig hcanon)
                                            hbody hcreated10
                                            (accountMapEquiv.of_eq
                                              hmapE10.symm)
                                            hState10 henc
                              · have hbad1 : v1 ≠
                                    UInt256.isZero (UInt256.isZero v1) := by
                                  intro heq
                                  exact hbool1
                                    ((amm4BoolNormalized_canonical v1).mp heq)
                                have hrev :=
                                  amm4BurnX_token1DecodeInvalidReverts
                                    hbad1 rd5983b
                                have hnot0 : v1 ≠ ⟨0⟩ :=
                                  fun h => hbool1 (Or.inl h)
                                have hnot1 : v1 ≠ ⟨1⟩ :=
                                  fun h => hbool1 (Or.inr h)
                                have hdecNone :
                                    config.externalABI.decode? "transfer" o1 =
                                      none := by
                                  rw [amm4BurnDecodeTransfer_word hlo1
                                    (by omega : o1.size < 2 ^ 255)]
                                  simpa [v1, hnot0, hnot1]
                                have hbody :=
                                  amm4BurnSourceToken1DecodeRevert
                                    I o1 b0 hprefix0 hcallS1True hdecNone
                                exact hrev.reEquivExecutionRevert hcode hdispatch
                                  (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                        · have hbad0 : v0 ≠
                            UInt256.isZero (UInt256.isZero v0) := by
                            intro heq
                            exact hbool0 ((amm4BoolNormalized_canonical v0).mp heq)
                          have hrev := amm4BurnX_token0DecodeInvalidReverts
                            hbad0 rd5983
                          have hnot0 : v0 ≠ ⟨0⟩ :=
                            fun h => hbool0 (Or.inl h)
                          have hnot1 : v0 ≠ ⟨1⟩ :=
                            fun h => hbool0 (Or.inr h)
                          have hdecNone :
                              config.externalABI.decode? "transfer" o0 =
                                none := by
                            rw [amm4BurnDecodeTransfer_word hlo0
                              (by omega : o0.size < 2 ^ 255)]
                            simpa [v0, hnot0, hnot1]
                          have hbody := amm4BurnSourceToken0DecodeRevert
                            I o0 hprefixSender' hcallSTrue hdecNone
                          exact hrev.reEquivExecutionRevert hcode hdispatch
                            (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
                · have hunder :
                      (solcSlotWord σE3 I (amm4TransferSenderSlot I)).toNat <
                      liq.toNat := by omega
                  have hsourceUnder :
                      (Solm.EVM.storageLoad evmS3
                        evmS3.executionEnv.codeOwner
                        (amm4TransferSenderSlot I)).toNat < liq.toNat := by
                    rw [← hbalance]
                    exact hunder
                  have hsrcS3 : evmS3.executionEnv.source = I.source := by
                    simp [evmS3, amm4BurnAfterSupply,
                      storageStore_executionEnv, evmS, initState]
                  have hbody := amm4BurnSourceSenderUnderflow I
                    hprefixSupply' hsrcS3 hsourceUnder
                  exact (amm4BurnX_senderUnderflow rd3929
                    (by simpa [σE3, liq] using hunder))
                    |>.reEquivExecutionRevert hcode hdispatch
                      (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
              · have hunder : (solcSlotWord σ_evm I ⟨0⟩).toNat <
                    (amm4BurnLiquidityWord I).toNat := by omega
                have hsourceUnder :
                    (Solm.EVM.storageLoad evmS
                      evmS.executionEnv.codeOwner ⟨0⟩).toNat <
                    (amm4BurnLiquidityWord I).toNat := by
                  change (solcSlotWord σ_solm I ⟨0⟩).toNat < _
                  rw [← hslot0]
                  exact hunder
                have hbody := amm4BurnSourceSupplyUnderflow evmS I
                  (by simpa [evmS, initState] using hwv)
                  hnonzeroS hsourceFit0 hsourceFit1 hsourceUnder
                exact (amm4BurnX_supplyUnderflow rd3840 hunder)
                  |>.reEquivExecutionRevert hcode hdispatch
                    (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
            · have hover1 : UInt256.size ≤
                  (amm4BurnLiquidityWord I).toNat *
                    (solcSlotWord σ_evm I ⟨6⟩).toNat := by omega
              have hsourceOver : UInt256.size ≤
                  amm4BurnAmount1Numerator evmS I := by
                change UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
                  (solcSlotWord σ_solm I ⟨6⟩).toNat
                rw [← hslot6]
                exact hover1
              have hbody := amm4BurnSourceNum1Overflow evmS I
                (by simpa [evmS, initState] using hwv)
                hnonzeroS hsourceFit0 hsourceOver
              exact (amm4BurnX_amount1NumeratorOverflow rd3811 hover1)
                |>.reEquivExecutionRevert hcode hdispatch
                  (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
          · have hover0 : UInt256.size ≤
                (amm4BurnLiquidityWord I).toNat *
                  (solcSlotWord σ_evm I ⟨5⟩).toNat := by omega
            have hsourceOver : UInt256.size ≤
                (amm4BurnLiquidityWord I).toNat *
                  (Solm.EVM.storageLoad evmS
                    evmS.executionEnv.codeOwner ⟨5⟩).toNat := by
              change UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
                (solcSlotWord σ_solm I ⟨5⟩).toNat
              rw [← hslot5]
              exact hover0
            have hbody := amm4BurnSourceAmount0NumeratorOverflow evmS I
              (by simpa [evmS, initState] using hwv) hnonzeroS hsourceOver
            exact (amm4BurnX_amount0NumeratorOverflow rd3781 hover0)
              |>.reEquivExecutionRevert hcode hdispatch
                (amm4Decode_burn_ok hsz68 hbig hcanon) hbody
      · exact (amm4BurnX_noncanon (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hcanon hreach).reEquivDecodingFailed
            hcode hdispatch (amm4Decode_burn_none_noncanon hsz68 hbig hcanon)
    · have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (amm4BurnX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hhuge hreach).reEquivDecodingFailed
          hcode hdispatch (amm4Decode_burn_none_huge hhuge)
  · have hshort : I.calldata.size < 68 := by omega
    exact (amm4BurnX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach).reEquivDecodingFailed
        hcode hdispatch (amm4Decode_burn_none_short hsz4 hshort)

end Benchmarks.ActAmm4
