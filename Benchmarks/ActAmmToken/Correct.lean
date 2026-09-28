import Benchmarks.ActAmmToken.Constructor
import Benchmarks.ActAmmToken.Reverts
import Benchmarks.ActAmmToken.Approve
import Benchmarks.ActAmmToken.TotalSupply
import Benchmarks.ActAmmToken.TransferFrom
import Benchmarks.ActAmmToken.Mint
import Benchmarks.ActAmmToken.Burn
import Benchmarks.ActAmmToken.BalanceOf
import Benchmarks.ActAmmToken.BurnFrom
import Benchmarks.ActAmmToken.Transfer
import Benchmarks.ActAmmToken.Allowance
import Solm.Equiv

/-! # Act AMM Token EquiVM benchmark target -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.ActAmmToken

set_option maxHeartbeats 2000000 in
theorem tokenRuntimeCorrect :
    runtimeEquivalence config tokenBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    ·
      by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · have hm : (tokenSelBytes 0 == I.calldata.extract 0 4) = true := by
          simpa [selIs, tokenSelBytes] using h0
        exact tokenApproveBodyCore hcode hsize hperm hwv h0
          (tokenReachLowBody 0 (by omega) ⟨149⟩ hcode hwv hsz hsize
            (tokenPivotTaken 0 (by omega) hsz hm)
            (tokenLowMatches 0 (by omega) hsz hm).1
            (tokenLowMatches 0 (by omega) hsz hm).2
            (by jump_dest) (by decide)) hAccounts
      ·
        by_cases h1 : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
        · have hm : (tokenSelBytes 1 == I.calldata.extract 0 4) = true := by
            simpa [selIs, tokenSelBytes] using h1
          exact tokenTotalSupplyBodyCore hcode hsize hperm hwv h1
            (tokenReachLowBody 1 (by omega) ⟨197⟩ hcode hwv hsz hsize
              (tokenPivotTaken 1 (by omega) hsz hm)
              (tokenLowMatches 1 (by omega) hsz hm).1
              (tokenLowMatches 1 (by omega) hsz hm).2
              (by jump_dest) (by decide)) hAccounts
        ·
          by_cases h2 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
          · have hm : (tokenSelBytes 2 == I.calldata.extract 0 4) = true := by
              simpa [selIs, tokenSelBytes] using h2
            exact tokenTransferFromBodyCore hcode hsize hperm hwv h2
              (tokenReachLowBody 2 (by omega) ⟨227⟩ hcode hwv hsz hsize
                (tokenPivotTaken 2 (by omega) hsz hm)
                (tokenLowMatches 2 (by omega) hsz hm).1
                (tokenLowMatches 2 (by omega) hsz hm).2
                (by jump_dest) (by decide)) hAccounts
          ·
            by_cases h3 : selIs I ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩
            · have hm : (tokenSelBytes 3 == I.calldata.extract 0 4) = true := by
                simpa [selIs, tokenSelBytes] using h3
              exact tokenMintBodyCore hcode hsize hperm hwv h3
                (tokenReachLowBody 3 (by omega) ⟨275⟩ hcode hwv hsz hsize
                  (tokenPivotTaken 3 (by omega) hsz hm)
                  (tokenLowMatches 3 (by omega) hsz hm).1
                  (tokenLowMatches 3 (by omega) hsz hm).2
                  (by jump_dest) (by decide)) hAccounts
            ·
              by_cases h4 : selIs I ⟨#[0x42, 0x96, 0x6c, 0x68]⟩
              · have hm : (tokenSelBytes 4 == I.calldata.extract 0 4) = true := by
                  simpa [selIs, tokenSelBytes] using h4
                have hm' : (tokenSelBytes (0 + 4) == I.calldata.extract 0 4) = true := by
                  simpa using hm
                exact tokenBurnBodyCore hcode hsize hperm hwv h4
                  (tokenReachHighBody 0 (by omega) ⟨323⟩ hcode hwv hsz hsize
                    (tokenPivotNotTaken 0 (by omega) hsz hm')
                    (tokenHighMatches 0 (by omega) hsz hm').1
                    (tokenHighMatches 0 (by omega) hsz hm').2
                    (by jump_dest) (by decide)) hAccounts
              ·
                by_cases h5 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
                · have hm : (tokenSelBytes 5 == I.calldata.extract 0 4) = true := by
                    simpa [selIs, tokenSelBytes] using h5
                  have hm' : (tokenSelBytes (1 + 4) == I.calldata.extract 0 4) = true := by
                    simpa using hm
                  exact tokenBalanceOfBodyCore hcode hsize hperm hwv h5
                    (tokenReachHighBody 1 (by omega) ⟨371⟩ hcode hwv hsz hsize
                      (tokenPivotNotTaken 1 (by omega) hsz hm')
                      (tokenHighMatches 1 (by omega) hsz hm').1
                      (tokenHighMatches 1 (by omega) hsz hm').2
                      (by jump_dest) (by decide)) hAccounts
                ·
                  by_cases h6 : selIs I ⟨#[0x79, 0xcc, 0x67, 0x90]⟩
                  · have hm : (tokenSelBytes 6 == I.calldata.extract 0 4) = true := by
                      simpa [selIs, tokenSelBytes] using h6
                    have hm' : (tokenSelBytes (2 + 4) == I.calldata.extract 0 4) = true := by
                      simpa using hm
                    exact tokenBurnFromBodyCore hcode hsize hperm hwv h6
                      (tokenReachHighBody 2 (by omega) ⟨419⟩ hcode hwv hsz hsize
                        (tokenPivotNotTaken 2 (by omega) hsz hm')
                        (tokenHighMatches 2 (by omega) hsz hm').1
                        (tokenHighMatches 2 (by omega) hsz hm').2
                        (by jump_dest) (by decide)) hAccounts
                  ·
                    by_cases h7 : selIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩
                    · have hm : (tokenSelBytes 7 == I.calldata.extract 0 4) = true := by
                        simpa [selIs, tokenSelBytes] using h7
                      have hm' : (tokenSelBytes (3 + 4) == I.calldata.extract 0 4) = true := by
                        simpa using hm
                      exact tokenTransferBodyCore hcode hsize hperm hwv h7
                        (tokenReachHighBody 3 (by omega) ⟨467⟩ hcode hwv hsz hsize
                          (tokenPivotNotTaken 3 (by omega) hsz hm')
                          (tokenHighMatches 3 (by omega) hsz hm').1
                          (tokenHighMatches 3 (by omega) hsz hm').2
                          (by jump_dest) (by decide)) hAccounts
                    ·
                      by_cases h8 : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                      · have hm : (tokenSelBytes 8 == I.calldata.extract 0 4) = true := by
                          simpa [selIs, tokenSelBytes] using h8
                        have hm' : (tokenSelBytes (4 + 4) == I.calldata.extract 0 4) = true := by
                          simpa using hm
                        exact tokenAllowanceBodyCore hcode hsize hperm hwv h8
                          (tokenReachHighBody 4 (by omega) ⟨515⟩ hcode hwv hsz hsize
                            (tokenPivotNotTaken 4 (by omega) hsz hm')
                            (tokenHighMatches 4 (by omega) hsz hm').1
                            (tokenHighMatches 4 (by omega) hsz hm').2
                            (by jump_dest) (by decide)) hAccounts
                      ·
                        refine tokenNoDispatch hcode hsize hperm hwv ?_
                        intro i hi
                        interval_cases i
                        · simpa [selIs, tokenSelBytes] using h0
                        · simpa [selIs, tokenSelBytes] using h1
                        · simpa [selIs, tokenSelBytes] using h2
                        · simpa [selIs, tokenSelBytes] using h3
                        · simpa [selIs, tokenSelBytes] using h4
                        · simpa [selIs, tokenSelBytes] using h5
                        · simpa [selIs, tokenSelBytes] using h6
                        · simpa [selIs, tokenSelBytes] using h7
                        · simpa [selIs, tokenSelBytes] using h8
    · exact tokenShortRevert hcode hsize hperm hwv (by omega)
  · exact tokenNonPayable hcode hwv

theorem tokenContractCorrect :
    contractEquivalence config tokenCreationBytecode tokenBytecode contract :=
  contractEquivalence.intro tokenConstructorCorrect tokenRuntimeCorrect

end Benchmarks.ActAmmToken
