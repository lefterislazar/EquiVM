import Benchmarks.ActAmm4.SwapEarlyBridge
import Benchmarks.ActAmm4.SwapDecodeRevert
import Benchmarks.ActAmm4.SwapFirstCallDepth
import Benchmarks.ActAmm4.SwapFirstCallFailure
import Benchmarks.ActAmm4.SwapCallFrames
import Benchmarks.ActAmm4.BurnSourceCalls
import Benchmarks.ActAmm4.SwapSecondCallTransport
import Benchmarks.ActAmm4.SwapSourceCallReverts
import Benchmarks.ActAmm4.SwapThirdCallTransport
import Benchmarks.ActAmm4.SwapSourceBalanceReverts
import Benchmarks.ActAmm4.SwapFourthCallTransport
import Benchmarks.ActAmm4.SwapArithmeticCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 10000000 in
/-- Swap wrapper reached from the checked-in runtime dispatcher at PC 323. -/
theorem amm4SwapBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨323⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4SwapSelector_size hsel
  have hdispatch := amm4Dispatch_swap hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon :
        (amm4SwapToWord I).toNat < EVM.addressModulus
      · rcases amm4SwapEarlyGuardOrValid hcode hsize hwv hsel
          hsz100 hbig hcanon hreach hAccounts with hguard | hvalid
        · exact hguard
        · rcases hvalid with
            ⟨hpos, hliq0, hliq1, hne0, hne1⟩
          by_cases hdepth : I.depth = 1024
          · exact amm4SwapFirstCallDepthEquiv hcode hsize hwv hsel
              hsz100 hbig hcanon hpos hliq0 hliq1 hne0 hne1
              hdepth hreach hAccounts
          · have hdepthLt : I.depth.val < 1024 := by
              have hlt := I.depth.isLt
              omega
            have hframe := amm4SwapX_transfer0FrameFromEntry
              hsz100 hsize hbig hcanon hpos hliq0 hliq1
              hne0 hne1 hreach
            obtain ⟨cA1, σE1, z0, ret0, A1, k1, C1,
              rd2607, hcallE0, hretSize, hretBound⟩ :=
              amm4SwapX_transfer0Call hperm hdepthLt hcanon hframe
            by_cases hz0 : z0 = false
            · have rdFailed := by simpa [hz0] using rd2607
              have hcallFailed := by simpa [hz0] using hcallE0
              exact amm4SwapFirstCallFailedEquiv hcode hwv hsel
                hsz100 hbig hcanon hpos hliq0 hliq1 hne0 hne1
                hAccounts hcallFailed hretSize rdFailed
            · have hz0true : z0 = true := by cases z0 <;> simp_all
              have rdSuccess := by
                simpa [hz0true, amm4SwapTransfer0PostCallMem] using rd2607
              have hcallSuccess := by simpa [hz0true] using hcallE0
              by_cases hshort0 : ret0.size < 32
              · obtain ⟨_, _, rd2626⟩ :=
                  amm4SwapX_transfer0CallSucceeded rdSuccess
                obtain ⟨_, _, rd6025⟩ :=
                  amm4SwapX_transfer0ToDecoder hretSize rd2626
                have hrev := amm4SwapX_transfer0DecodeShortReverts
                  hshort0 rd6025
                exact amm4SwapFirstCallDecodeFailedEquiv hcode hwv hsel
                  hsz100 hbig hcanon hpos hliq0 hliq1 hne0 hne1
                  hAccounts hcallSuccess
                  (amm4BurnDecodeTransfer_short hshort0) hrev
              · have hlo0 : 32 ≤ ret0.size := by omega
                obtain ⟨_, _, rd2626⟩ :=
                  amm4SwapX_transfer0CallSucceeded rdSuccess
                obtain ⟨_, _, rd6025⟩ :=
                  amm4SwapX_transfer0ToDecoder hretSize rd2626
                obtain ⟨_, _, rd5983⟩ :=
                  amm4SwapX_transfer0DecodeWord hlo0 hretBound rd6025
                let v0 : UInt256 := UInt256.ofNat
                  (fromByteArrayBigEndian (ret0.extract 0 32))
                by_cases hbool0 : v0 = ⟨0⟩ ∨ v0 = ⟨1⟩
                · let b0 : Bool := v0 = ⟨1⟩
                  have hdec0 :
                      config.externalABI.decode? "transfer" ret0 =
                        some [.bool b0] := by
                    rw [amm4BurnDecodeTransfer_word hlo0
                      (by omega : ret0.size < 2 ^ 255)]
                    rcases hbool0 with hzero | hone
                    · simp [v0, b0, hzero, UInt256.size]
                    · simp [v0, b0, hone, UInt256.size]
                  obtain ⟨σS1, hσ1, hprefix0⟩ :=
                    amm4SwapTransfer0SourcePrefix hAccounts hwv
                      hpos hliq0 hliq1 hcanon hne0 hne1
                      hcallSuccess hdec0
                  have hframe1 := amm4SwapX_transfer1FrameAfterFirst
                    hlo0 hretBound hcanon hbool0 rdSuccess
                  obtain ⟨cA2, σE2, z1, ret1, A2, k2, C2,
                    rd2764, hcallE1, hretSize1, hretBound1⟩ :=
                    amm4SwapX_transfer1Call (Apre := A1)
                      hperm hdepthLt hlo0 hretBound hcanon hframe1
                  obtain ⟨σS2, hσ2, hcallS1⟩ :=
                    amm4SwapSecondCallRawTransport
                      (cA := cA1) (σ_evm := σE1)
                      (σ_solm := σS1) (A := A1)
                      hσ1 hcallE1
                  by_cases hz1 : z1 = false
                  · have rdFailed := by simpa [hz1] using rd2764
                    have hcallFailed := by simpa [hz1] using hcallS1
                    have hbody := amm4SwapSourceTransfer1CallFailed
                      I ret1 b0 hprefix0
                      (by simpa [initState] using hcallFailed)
                    have hrev := amm4SwapX_transfer1CallFailed
                      rdFailed hretSize1
                      (by simp only [List.length_cons, List.length_nil];
                          omega)
                    exact hrev.reEquivExecutionRevert hcode hdispatch
                      (amm4Decode_swap_ok hsz100 hbig hcanon) hbody
                  · have hz1true : z1 = true := by cases z1 <;> simp_all
                    have rdSuccess1 := by
                      simpa [hz1true] using rd2764
                    have hcallSuccess1 := by
                      simpa [hz1true] using hcallS1
                    by_cases hshort1 : ret1.size < 32
                    · obtain ⟨_, _, rd2783⟩ :=
                        amm4SwapX_transfer1CallSucceeded rdSuccess1
                      obtain ⟨_, _, rd6025b⟩ :=
                        amm4SwapX_transfer1ToDecoder
                          hlo0 hretBound hretSize1 rd2783
                      have hrev :=
                        amm4SwapX_transfer1DecodeShortReverts
                          hlo0 hretBound hshort1 rd6025b
                      have hbody := amm4SwapSourceTransfer1DecodeRevert
                        I ret1 b0 hprefix0
                        (by simpa [initState] using hcallSuccess1)
                        (amm4BurnDecodeTransfer_short hshort1)
                      exact hrev.reEquivExecutionRevert hcode hdispatch
                        (amm4Decode_swap_ok hsz100 hbig hcanon) hbody
                    · have hlo1 : 32 ≤ ret1.size := by omega
                      obtain ⟨_, _, rd2783⟩ :=
                        amm4SwapX_transfer1CallSucceeded rdSuccess1
                      obtain ⟨_, _, rd6025b⟩ :=
                        amm4SwapX_transfer1ToDecoder
                          hlo0 hretBound hretSize1 rd2783
                      obtain ⟨_, _, rd5983b⟩ :=
                        amm4SwapX_transfer1DecodeWord
                          hlo0 hretBound hlo1 hretBound1 rd6025b
                      let v1 : UInt256 := UInt256.ofNat
                        (fromByteArrayBigEndian (ret1.extract 0 32))
                      by_cases hbool1 : v1 = ⟨0⟩ ∨ v1 = ⟨1⟩
                      · let b1 : Bool := v1 = ⟨1⟩
                        have hdec1 :
                            config.externalABI.decode? "transfer" ret1 =
                              some [.bool b1] := by
                          rw [amm4BurnDecodeTransfer_word hlo1
                            (by omega : ret1.size < 2 ^ 255)]
                          rcases hbool1 with hzero | hone
                          · simp [v1, b1, hzero, UInt256.size]
                          · simp [v1, b1, hone, UInt256.size]
                        have hprefix1 := amm4SwapSourceTransfer1CallOk
                          I ret1 b0 b1 hprefix0
                          (by simpa [hz1true, initState] using hcallS1)
                          hdec1
                        have hframe2 :=
                          amm4SwapX_balance0FrameAfterSecond
                            hlo0 hretBound hlo1 hretBound1
                            hbool1 rdSuccess1
                        obtain ⟨cA3, σE3, z2, ret2, A3, k3, C3,
                          rd2919, hcallE2, hretSize2, hretBound2⟩ :=
                          amm4SwapX_balance0Staticcall (Apre := A2)
                            hlo0 hretBound hlo1 hretBound1
                            hdepthLt hframe2
                        obtain ⟨σS3, hσ3, hcallS2⟩ :=
                          amm4SwapThirdCallRawTransport
                            (cA := cA2) (σ_evm := σE2)
                            (σ_solm := σS2) (A := A2)
                            hσ2 hcallE2
                        by_cases hz2 : z2 = false
                        · have rdFailed := by simpa [hz2] using rd2919
                          have hcallFailed := by
                            simpa [hz2] using hcallS2
                          have hbody := amm4SwapSourceBalance0CallFailed
                            I b0 b1 ret2 hprefix1
                            (by simpa [initState] using hcallFailed)
                          have hrev := amm4SwapX_balance0CallFailed
                            rdFailed hretSize2
                            (by simp only [List.length_cons, List.length_nil];
                                omega)
                          exact hrev.reEquivExecutionRevert hcode hdispatch
                            (amm4Decode_swap_ok hsz100 hbig hcanon) hbody
                        · have hz2true : z2 = true := by
                            cases z2 <;> simp_all
                          have rdSuccess2 := by
                            simpa [hz2true] using rd2919
                          have hcallSuccess2 := by
                            simpa [hz2true] using hcallS2
                          by_cases hshort2 : ret2.size < 32
                          · obtain ⟨_, _, rd2938⟩ :=
                              amm4SwapX_balance0CallSucceeded rdSuccess2
                            obtain ⟨_, _, rd5415⟩ :=
                              amm4SwapX_balance0ToDecoder
                                hlo0 hretBound hlo1 hretBound1
                                hretSize2 rd2938
                            have hrev :=
                              amm4SwapX_balance0DecodeShortReverts
                                hlo0 hretBound hretBound1
                                hshort2 rd5415
                            have hbody :=
                              amm4SwapSourceBalance0DecodeRevert
                                I b0 b1 ret2 hprefix1
                                (by simpa [initState] using hcallSuccess2)
                                (amm4MintDecodeBalance_short hshort2)
                            exact hrev.reEquivExecutionRevert
                              hcode hdispatch
                              (amm4Decode_swap_ok hsz100 hbig hcanon) hbody
                          · have hlo2 : 32 ≤ ret2.size := by omega
                            have hprefix2 :=
                              amm4SwapSourceBalance0CallOk
                                I b0 b1 ret2 hprefix1
                                (by simpa [initState] using hcallSuccess2)
                                hlo2 hretBound2
                            have hframe3 :=
                              amm4SwapX_balance1FrameAfterThird
                                hlo0 hretBound hlo1 hretBound1
                                hlo2 hretBound2 rdSuccess2
                            obtain ⟨cA4, σE4, z3, ret3, A4, k4, C4,
                              rd3075, hcallE3, hretSize3, hretBound3⟩ :=
                              amm4SwapX_balance1Staticcall (Apre := A3)
                                hlo0 hretBound hlo1 hretBound1
                                hlo2 hretBound2 hdepthLt hframe3
                            obtain ⟨σS4, hσ4, hcallS3⟩ :=
                              amm4SwapFourthCallRawTransport
                                (cA := cA3) (σ_evm := σE3)
                                (σ_solm := σS3) (A := A3)
                                hσ3 hcallE3
                            by_cases hz3 : z3 = false
                            · have rdFailed := by
                                simpa [hz3] using rd3075
                              have hcallFailed := by
                                simpa [hz3] using hcallS3
                              have hbody :=
                                amm4SwapSourceBalance1CallFailed
                                  I b0 b1 ret2 ret3 hprefix2
                                  (by simpa [initState] using hcallFailed)
                              have hrev := amm4SwapX_balance1CallFailed
                                rdFailed hretSize3
                                (by simp only [List.length_cons,
                                    List.length_nil]; omega)
                              exact hrev.reEquivExecutionRevert
                                hcode hdispatch
                                (amm4Decode_swap_ok hsz100 hbig hcanon)
                                hbody
                            · have hz3true : z3 = true := by
                                cases z3 <;> simp_all
                              have rdSuccess3 := by
                                simpa [hz3true] using rd3075
                              have hcallSuccess3 := by
                                simpa [hz3true] using hcallS3
                              by_cases hshort3 : ret3.size < 32
                              · obtain ⟨_, _, rd3094⟩ :=
                                  amm4SwapX_balance1CallSucceeded
                                    rdSuccess3
                                obtain ⟨_, _, rd5415b⟩ :=
                                  amm4SwapX_balance1ToDecoder
                                    hlo0 hretBound hlo1 hretBound1
                                    hlo2 hretBound2 hretSize3 rd3094
                                have hrev :=
                                  amm4SwapX_balance1DecodeShortReverts
                                    hlo0 hretBound hretBound1
                                    hretBound2 hshort3 rd5415b
                                have hbody :=
                                  amm4SwapSourceBalance1DecodeRevert
                                    I b0 b1 ret2 ret3 hprefix2
                                    (by simpa [initState]
                                      using hcallSuccess3)
                                    (amm4MintDecodeBalance_short hshort3)
                                exact hrev.reEquivExecutionRevert
                                  hcode hdispatch
                                  (amm4Decode_swap_ok hsz100 hbig hcanon)
                                  hbody
                              · have hlo3 : 32 ≤ ret3.size := by omega
                                have hprefix3 :=
                                  amm4SwapSourceBalance1CallOk
                                    I b0 b1 ret2 ret3 hprefix2
                                    (by simpa [initState]
                                      using hcallSuccess3)
                                    hlo3 hretBound3
                                obtain ⟨_, _, rd3128⟩ :=
                                  amm4SwapX_arithmeticAfterFourth
                                    hlo0 hretBound hlo1 hretBound1
                                    hlo2 hretBound2 hlo3 hretBound3
                                    rdSuccess3
                                exact amm4SwapArithmeticCore hcode hdispatch
                                  (amm4Decode_swap_ok hsz100 hbig hcanon)
                                  hperm hσ4 hprefix3 hlo2 hlo3
                                  (by
                                    rw [amm4SwapBalance1CalldataWords_toNat
                                      ret0 ret1 ret2 hlo0 hretBound
                                      hlo1 hretBound1 hlo2 hretBound2]
                                    omega)
                                  rd3128
                      · have hbad : v1 ≠
                          UInt256.isZero (UInt256.isZero v1) := by
                          intro heq
                          exact hbool1
                            ((amm4BoolNormalized_canonical v1).mp heq)
                        have hrev :=
                          amm4SwapX_transfer1DecodeInvalidReverts
                            hbad rd5983b
                        have hnot0 : v1 ≠ ⟨0⟩ :=
                          fun h => hbool1 (Or.inl h)
                        have hnot1 : v1 ≠ ⟨1⟩ :=
                          fun h => hbool1 (Or.inr h)
                        have hdecNone :
                            config.externalABI.decode? "transfer" ret1 =
                              none := by
                          rw [amm4BurnDecodeTransfer_word hlo1
                            (by omega : ret1.size < 2 ^ 255)]
                          simpa [v1, hnot0, hnot1]
                        have hbody := amm4SwapSourceTransfer1DecodeRevert
                          I ret1 b0 hprefix0
                          (by simpa [hz1true, initState] using hcallS1)
                          hdecNone
                        exact hrev.reEquivExecutionRevert hcode hdispatch
                          (amm4Decode_swap_ok hsz100 hbig hcanon) hbody
                · have hbad : v0 ≠
                    UInt256.isZero (UInt256.isZero v0) := by
                    intro heq
                    exact hbool0 ((amm4BoolNormalized_canonical v0).mp heq)
                  have hrev := amm4SwapX_transfer0DecodeInvalidReverts
                    hbad rd5983
                  have hnot0 : v0 ≠ ⟨0⟩ :=
                    fun h => hbool0 (Or.inl h)
                  have hnot1 : v0 ≠ ⟨1⟩ :=
                    fun h => hbool0 (Or.inr h)
                  have hdecNone :
                      config.externalABI.decode? "transfer" ret0 =
                        none := by
                    rw [amm4BurnDecodeTransfer_word hlo0
                      (by omega : ret0.size < 2 ^ 255)]
                    simpa [v0, hnot0, hnot1]
                  exact amm4SwapFirstCallDecodeFailedEquiv hcode hwv hsel
                    hsz100 hbig hcanon hpos hliq0 hliq1 hne0 hne1
                    hAccounts hcallSuccess hdecNone hrev
      · exact (amm4SwapX_noncanon (g := Sat256.ofUInt256 g)
          hsz100 hsize hbig hcanon hreach).reEquivDecodingFailed
          hcode hdispatch
          (amm4Decode_swap_none_noncanon hsz100 hbig hcanon)
    · have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (amm4SwapX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hhuge hreach).reEquivDecodingFailed
        hcode hdispatch (amm4Decode_swap_none_huge hhuge)
  · have hshort : I.calldata.size < 100 := by omega
    exact (amm4SwapX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach).reEquivDecodingFailed
      hcode hdispatch (amm4Decode_swap_none_short hsz4 hshort)

end Benchmarks.ActAmm4
