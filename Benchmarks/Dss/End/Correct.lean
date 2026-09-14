import Benchmarks.Dss.End.Constructor
import Benchmarks.Dss.End.Admin
import Benchmarks.Dss.End.Debt
import Benchmarks.Dss.End.Dispatcher
import Benchmarks.Dss.End.Dispatcher65
import Benchmarks.Dss.End.Dispatcher114
import Benchmarks.Dss.End.Dispatcher174223
import Benchmarks.Dss.End.Dispatcher294343
import Benchmarks.Dss.End.Dispatcher403
import Benchmarks.Dss.End.CageBody
import Benchmarks.Dss.End.CageIlk
import Benchmarks.Dss.End.Cash
import Benchmarks.Dss.End.FileAddress
import Benchmarks.Dss.End.FileUint
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.NoMatch
import Benchmarks.Dss.End.ParamGetters
import Benchmarks.Dss.End.Pack
import Benchmarks.Dss.End.SimpleGetters
import Benchmarks.Dss.End.Skim
import Benchmarks.Dss.End.SkipBody
import Benchmarks.Dss.End.SnipAfterYank
import Benchmarks.Dss.End.Thaw
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.End

theorem endCorrect :
    runtimeEquivalence config endBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases hdebt : endSelectorMatches I (endSelBytes 11)
      · exact endDebtBodyCore hcode hwv hdebt
          (endReachDebt (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hdebt) hAccounts
      · by_cases hvat : endSelectorMatches I (endSelBytes 1)
        · exact endVatBodyCore hcode hwv hvat
            (endReachVat (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hvat) hAccounts
        · by_cases hcat : endSelectorMatches I (endSelBytes 2)
          · exact endCatBodyCore hcode hwv hcat
              (endReachCat (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hcat) hAccounts
          · by_cases hdog : endSelectorMatches I (endSelBytes 3)
            · exact endDogBodyCore hcode hwv hdog
                (endReachDog (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hdog) hAccounts
            · by_cases hvow : endSelectorMatches I (endSelBytes 4)
              · exact endVowBodyCore hcode hwv hvow
                  (endReachVow (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hvow) hAccounts
              · by_cases hpot : endSelectorMatches I (endSelBytes 5)
                · exact endPotBodyCore hcode hwv hpot
                    (endReachPot (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hpot) hAccounts
                · by_cases hspot : endSelectorMatches I (endSelBytes 6)
                  · exact endSpotBodyCore hcode hwv hspot
                      (endReachSpot (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hspot) hAccounts
                  · by_cases hcure : endSelectorMatches I (endSelBytes 7)
                    · exact endCureBodyCore hcode hwv hcure
                        (endReachCure (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hcure)
                        hAccounts
                    · by_cases hlive : endSelectorMatches I (endSelBytes 8)
                      · exact endLiveBodyCore hcode hwv hlive
                          (endReachLive (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hlive)
                          hAccounts
                      · by_cases hwhen : endSelectorMatches I (endSelBytes 9)
                        · exact endWhenBodyCore hcode hwv hwhen
                            (endReachWhen (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hwhen)
                            hAccounts
                        · by_cases hwait : endSelectorMatches I (endSelBytes 10)
                          · exact endWaitBodyCore hcode hwv hwait
                              (endReachWait (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hwait)
                              hAccounts
                          · by_cases htag : endSelectorMatches I (endSelBytes 12)
                            · exact endTagBodyCore hcode hsize hwv htag
                                (endReachTag (g := Sat256.ofUInt256 g) hcode hwv hsz hsize htag)
                                hAccounts
                            · by_cases hgap : endSelectorMatches I (endSelBytes 13)
                              · exact endGapBodyCore hcode hsize hwv hgap
                                  (endReachGap (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hgap)
                                  hAccounts
                              · by_cases hArt : endSelectorMatches I (endSelBytes 14)
                                · exact endArtBodyCore hcode hsize hwv hArt
                                    (endReachArt (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hArt)
                                    hAccounts
                                · by_cases hfix : endSelectorMatches I (endSelBytes 15)
                                  · exact endFixBodyCore hcode hsize hwv hfix
                                      (endReachFix (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hfix)
                                      hAccounts
                                  · by_cases hwards : endSelectorMatches I (endSelBytes 0)
                                    · exact endWardsBodyCore hcode hsize hwv hwards
                                        (endReachWards (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hwards)
                                        hAccounts
                                    · by_cases hbag : endSelectorMatches I (endSelBytes 16)
                                      · exact endBagBodyCore hcode hsize hwv hbag
                                          (endReachBag (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbag)
                                          hAccounts
                                      · by_cases hout : endSelectorMatches I (endSelBytes 17)
                                        · exact endOutBodyCore hcode hsize hwv hout
                                            (endReachOut (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hout)
                                            hAccounts
                                        · by_cases hrely : endSelectorMatches I (endSelBytes 18)
                                          · exact endRelyBodyCore hcode hsize hperm hwv hrely
                                              (endReachRely (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hrely)
                                              hAccounts
                                          · by_cases hdeny : endSelectorMatches I (endSelBytes 19)
                                            · exact endDenyBodyCore hcode hsize hperm hwv hdeny
                                                (endReachDeny (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hdeny)
                                                hAccounts
                                            · by_cases hfileUint : endSelectorMatches I (endSelBytes 21)
                                              · exact endFileUintBodyCore hcode hsize hperm hwv hfileUint
                                                  (endReachFileUint (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hfileUint)
                                                  hAccounts
                                              · by_cases hfileAddress : endSelectorMatches I (endSelBytes 20)
                                                · exact endFileAddressBodyCore hcode hsize hperm hwv hfileAddress
                                                    (endReachFileAddress (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hfileAddress)
                                                    hAccounts
                                                · by_cases hcage : endSelectorMatches I (endSelBytes 22)
                                                  · exact endCageBodyCore hcode hperm hwv hcage
                                                      (endReachCage (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hcage)
                                                      hAccounts
                                                  · by_cases hpack : endSelectorMatches I (endSelBytes 30)
                                                    · exact endPackBodyCore hcode hsize hperm hwv hpack
                                                        (endReachPack (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hpack)
                                                        hAccounts
                                                    · by_cases hcageIlk : endSelectorMatches I (endSelBytes 23)
                                                      · exact endCageIlkBodyCore hcode hsize hperm hwv hcageIlk
                                                          (endReachCageIlk (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hcageIlk)
                                                          hAccounts
                                                      · by_cases hsnip : endSelectorMatches I (endSelBytes 24)
                                                        · exact endSnipBodyCore hcode hsize hperm hwv hsnip
                                                            (endReachSnip (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsnip)
                                                            hAccounts
                                                        · by_cases hskip : endSelectorMatches I (endSelBytes 25)
                                                          · exact endSkipBodyCore hcode hsize hperm hwv hskip
                                                              (endReachSkip (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hskip)
                                                              hAccounts
                                                          · by_cases hskim : endSelectorMatches I (endSelBytes 26)
                                                            · exact endSkimBodyCore hcode hsize hperm hwv hskim
                                                                (endReachSkim (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hskim)
                                                                hAccounts
                                                            · by_cases hfree : endSelectorMatches I (endSelBytes 27)
                                                              · exact endFreeBodyCore hcode hsize hperm hwv hfree
                                                                  (endReachFree (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hfree)
                                                                  hAccounts
                                                              · by_cases hthaw : endSelectorMatches I (endSelBytes 28)
                                                                · exact endThawBodyCore hcode hsize hperm hwv hthaw
                                                                    (endReachThaw (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hthaw)
                                                                    hAccounts
                                                                · by_cases hflow : endSelectorMatches I (endSelBytes 29)
                                                                  · exact endFlowBodyCore hcode hsize hperm hwv hflow
                                                                      (endReachFlow (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hflow)
                                                                      hAccounts
                                                                  · by_cases hcash : endSelectorMatches I (endSelBytes 31)
                                                                    · exact endCashBodyCore hcode hsize hperm hwv hcash
                                                                        (endReachCash (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hcash)
                                                                        hAccounts
                                                                    · have hnm : ∀ i, i < 32 →
                                                                          (endSelBytes i == I.calldata.extract 0 4) = false := by
                                                                        intro i hi
                                                                        interval_cases i
                                                                        · exact endSelectorMiss_of_not_match hwards
                                                                        · exact endSelectorMiss_of_not_match hvat
                                                                        · exact endSelectorMiss_of_not_match hcat
                                                                        · exact endSelectorMiss_of_not_match hdog
                                                                        · exact endSelectorMiss_of_not_match hvow
                                                                        · exact endSelectorMiss_of_not_match hpot
                                                                        · exact endSelectorMiss_of_not_match hspot
                                                                        · exact endSelectorMiss_of_not_match hcure
                                                                        · exact endSelectorMiss_of_not_match hlive
                                                                        · exact endSelectorMiss_of_not_match hwhen
                                                                        · exact endSelectorMiss_of_not_match hwait
                                                                        · exact endSelectorMiss_of_not_match hdebt
                                                                        · exact endSelectorMiss_of_not_match htag
                                                                        · exact endSelectorMiss_of_not_match hgap
                                                                        · exact endSelectorMiss_of_not_match hArt
                                                                        · exact endSelectorMiss_of_not_match hfix
                                                                        · exact endSelectorMiss_of_not_match hbag
                                                                        · exact endSelectorMiss_of_not_match hout
                                                                        · exact endSelectorMiss_of_not_match hrely
                                                                        · exact endSelectorMiss_of_not_match hdeny
                                                                        · exact endSelectorMiss_of_not_match hfileAddress
                                                                        · exact endSelectorMiss_of_not_match hfileUint
                                                                        · exact endSelectorMiss_of_not_match hcage
                                                                        · exact endSelectorMiss_of_not_match hcageIlk
                                                                        · exact endSelectorMiss_of_not_match hsnip
                                                                        · exact endSelectorMiss_of_not_match hskip
                                                                        · exact endSelectorMiss_of_not_match hskim
                                                                        · exact endSelectorMiss_of_not_match hfree
                                                                        · exact endSelectorMiss_of_not_match hthaw
                                                                        · exact endSelectorMiss_of_not_match hflow
                                                                        · exact endSelectorMiss_of_not_match hpack
                                                                        · exact endSelectorMiss_of_not_match hcash
                                                                      exact endNoMatchRevert hcode hsize hperm hwv hsz hnm
    · have hshort : I.calldata.size < 4 := by omega
      exact endShortRevert hcode hsize hperm hwv hshort
  · exact endNonPayable hcode hwv

theorem endContractCorrect :
    contractEquivalence config endCreationBytecode endBytecode contract :=
  contractEquivalence.intro endConstructorCorrect endCorrect

end Benchmarks.Dss.End
