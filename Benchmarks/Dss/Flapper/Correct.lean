import Benchmarks.Dss.Flapper.Beg
import Benchmarks.Dss.Flapper.Bids
import Benchmarks.Dss.Flapper.Cage
import Benchmarks.Dss.Flapper.Constructor
import Benchmarks.Dss.Flapper.Deal
import Benchmarks.Dss.Flapper.Deny
import Benchmarks.Dss.Flapper.File
import Benchmarks.Dss.Flapper.Fill
import Benchmarks.Dss.Flapper.Gem
import Benchmarks.Dss.Flapper.Kick
import Benchmarks.Dss.Flapper.Kicks
import Benchmarks.Dss.Flapper.Lid
import Benchmarks.Dss.Flapper.Live
import Benchmarks.Dss.Flapper.Rely
import Benchmarks.Dss.Flapper.Tau
import Benchmarks.Dss.Flapper.Tend
import Benchmarks.Dss.Flapper.Tick
import Benchmarks.Dss.Flapper.Ttl
import Benchmarks.Dss.Flapper.Vat
import Benchmarks.Dss.Flapper.Wards
import Benchmarks.Dss.Flapper.Yank
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

theorem flapperCorrect :
    runtimeEquivalence config flapperBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I (flapperSelBytes 0)
      · exact flapperBegBody hcode hsize hperm hwv h0
          (flapperReachBody 0 (by omega) hcode hwv hsz hsize h0)
          hAccounts
      · by_cases h1 : selIs I (flapperSelBytes 1)
        · exact flapperBidsBody hcode hsize hperm hwv h1
            (flapperReachBody 1 (by omega) hcode hwv hsz hsize h1)
            hAccounts
        · by_cases h2 : selIs I (flapperSelBytes 2)
          · exact flapperCageBody hcode hsize hperm hwv h2
              (flapperReachBody 2 (by omega) hcode hwv hsz hsize h2)
              hAccounts
          · by_cases h3 : selIs I (flapperSelBytes 3)
            · exact flapperDealBody hcode hsize hperm hwv h3
                (flapperReachBody 3 (by omega) hcode hwv hsz hsize h3)
                hAccounts
            · by_cases h4 : selIs I (flapperSelBytes 4)
              · exact flapperDenyBody hcode hsize hperm hwv h4
                  (flapperReachBody 4 (by omega) hcode hwv hsz hsize h4)
                  hAccounts
              · by_cases h5 : selIs I (flapperSelBytes 5)
                · exact flapperFileBody hcode hsize hperm hwv h5
                    (flapperReachBody 5 (by omega) hcode hwv hsz hsize h5)
                    hAccounts
                · by_cases h6 : selIs I (flapperSelBytes 6)
                  · exact flapperFillBody hcode hsize hperm hwv h6
                      (flapperReachBody 6 (by omega) hcode hwv hsz hsize h6)
                      hAccounts
                  · by_cases h7 : selIs I (flapperSelBytes 7)
                    · exact flapperGemBody hcode hsize hperm hwv h7
                        (flapperReachBody 7 (by omega) hcode hwv hsz hsize h7)
                        hAccounts
                    · by_cases h8 : selIs I (flapperSelBytes 8)
                      · exact flapperKickBody hcode hsize hperm hwv h8
                          (flapperReachBody 8 (by omega) hcode hwv hsz hsize h8)
                          hAccounts
                      · by_cases h9 : selIs I (flapperSelBytes 9)
                        · exact flapperKicksBody hcode hsize hperm hwv h9
                            (flapperReachBody 9 (by omega) hcode hwv hsz hsize h9)
                            hAccounts
                        · by_cases h10 : selIs I (flapperSelBytes 10)
                          · exact flapperLidBody hcode hsize hperm hwv h10
                              (flapperReachBody 10 (by omega) hcode hwv hsz hsize h10)
                              hAccounts
                          · by_cases h11 : selIs I (flapperSelBytes 11)
                            · exact flapperLiveBody hcode hsize hperm hwv h11
                                (flapperReachBody 11 (by omega) hcode hwv hsz hsize h11)
                                hAccounts
                            · by_cases h12 : selIs I (flapperSelBytes 12)
                              · exact flapperRelyBody hcode hsize hperm hwv h12
                                  (flapperReachBody 12 (by omega) hcode hwv hsz hsize h12)
                                  hAccounts
                              · by_cases h13 : selIs I (flapperSelBytes 13)
                                · exact flapperTauBody hcode hsize hperm hwv h13
                                    (flapperReachBody 13 (by omega) hcode hwv hsz hsize h13)
                                    hAccounts
                                · by_cases h14 : selIs I (flapperSelBytes 14)
                                  · exact flapperTendBody hcode hsize hperm hwv h14
                                      (flapperReachBody 14 (by omega) hcode hwv hsz hsize h14)
                                      hAccounts
                                  · by_cases h15 : selIs I (flapperSelBytes 15)
                                    · exact flapperTickBody hcode hsize hperm hwv h15
                                        (flapperReachBody 15 (by omega) hcode hwv hsz hsize h15)
                                        hAccounts
                                    · by_cases h16 : selIs I (flapperSelBytes 16)
                                      · exact flapperTtlBody hcode hsize hperm hwv h16
                                          (flapperReachBody 16 (by omega) hcode hwv hsz hsize h16)
                                          hAccounts
                                      · by_cases h17 : selIs I (flapperSelBytes 17)
                                        · exact flapperVatBody hcode hsize hperm hwv h17
                                            (flapperReachBody 17 (by omega) hcode hwv hsz hsize h17)
                                            hAccounts
                                        · by_cases h18 : selIs I (flapperSelBytes 18)
                                          · exact flapperWardsBody hcode hsize hperm hwv h18
                                              (flapperReachBody 18 (by omega) hcode hwv hsz hsize h18)
                                              hAccounts
                                          · by_cases h19 : selIs I (flapperSelBytes 19)
                                            · exact flapperYankBody hcode hsize hperm hwv h19
                                                (flapperReachBody 19 (by omega) hcode hwv hsz hsize h19)
                                                hAccounts
                                            · refine flapperNoDispatch hcode hsize hperm hwv ?_
                                              intro i hi
                                              interval_cases i
                                              · simpa [selIs, flapperSelBytes] using h0
                                              · simpa [selIs, flapperSelBytes] using h1
                                              · simpa [selIs, flapperSelBytes] using h2
                                              · simpa [selIs, flapperSelBytes] using h3
                                              · simpa [selIs, flapperSelBytes] using h4
                                              · simpa [selIs, flapperSelBytes] using h5
                                              · simpa [selIs, flapperSelBytes] using h6
                                              · simpa [selIs, flapperSelBytes] using h7
                                              · simpa [selIs, flapperSelBytes] using h8
                                              · simpa [selIs, flapperSelBytes] using h9
                                              · simpa [selIs, flapperSelBytes] using h10
                                              · simpa [selIs, flapperSelBytes] using h11
                                              · simpa [selIs, flapperSelBytes] using h12
                                              · simpa [selIs, flapperSelBytes] using h13
                                              · simpa [selIs, flapperSelBytes] using h14
                                              · simpa [selIs, flapperSelBytes] using h15
                                              · simpa [selIs, flapperSelBytes] using h16
                                              · simpa [selIs, flapperSelBytes] using h17
                                              · simpa [selIs, flapperSelBytes] using h18
                                              · simpa [selIs, flapperSelBytes] using h19
    · exact flapperShortRevert hcode hsize hperm hwv (by omega)
  · exact flapperNonPayable hcode hwv

theorem flapperContractCorrect :
    contractEquivalence config flapperCreationBytecode flapperBytecode contract :=
  contractEquivalence.intro flapperConstructorCorrect flapperCorrect

end Benchmarks.Dss.Flapper
