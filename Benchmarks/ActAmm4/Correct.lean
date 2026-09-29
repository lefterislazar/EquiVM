import Benchmarks.ActAmm4.Constructor
import Benchmarks.ActAmm4.Reverts
import Benchmarks.ActAmm4.Approve
import Benchmarks.ActAmm4.TotalSupply
import Benchmarks.ActAmm4.TransferFrom
import Benchmarks.ActAmm4.Mint
import Benchmarks.ActAmm4.Swap
import Benchmarks.ActAmm4.BalanceOf
import Benchmarks.ActAmm4.Transfer
import Benchmarks.ActAmm4.Allowance
import Benchmarks.ActAmm4.Burn
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4RuntimeCorrect :
    runtimeEquivalence config amm4Bytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    ·
      by_cases h0 : amm4SelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · have hm : (amm4SelBytes 0 == I.calldata.extract 0 4) = true := by
          simpa [amm4SelIs, amm4SelBytes] using h0
        have hmatch := amm4LowMatches 0 (by omega) hsz hm
        have hreach := amm4ReachLowBody 0 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
          (by omega) ⟨149⟩ hcode hwv hsz hsize
          (amm4LowPivotTaken 0 (by omega) hsz hm)
          hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
        exact amm4ApproveBodyCore hcode hsize hperm hwv h0 hreach hAccounts
      ·
        by_cases h1 : amm4SelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
        · have hm : (amm4SelBytes 1 == I.calldata.extract 0 4) = true := by
            simpa [amm4SelIs, amm4SelBytes] using h1
          have hmatch := amm4LowMatches 1 (by omega) hsz hm
          have hreach := amm4ReachLowBody 1 (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (by omega) ⟨197⟩ hcode hwv hsz hsize
            (amm4LowPivotTaken 1 (by omega) hsz hm)
            hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
          exact amm4TotalSupplyBodyCore hcode hsize hperm hwv h1 hreach hAccounts
        ·
          by_cases h2 : amm4SelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
          · have hm : (amm4SelBytes 2 == I.calldata.extract 0 4) = true := by
              simpa [amm4SelIs, amm4SelBytes] using h2
            have hmatch := amm4LowMatches 2 (by omega) hsz hm
            have hreach := amm4ReachLowBody 2 (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
              (by omega) ⟨227⟩ hcode hwv hsz hsize
              (amm4LowPivotTaken 2 (by omega) hsz hm)
              hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
            exact amm4TransferFromBodyCore hcode hsize hperm hwv h2 hreach hAccounts
          ·
            by_cases h3 : amm4SelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩
            · have hm : (amm4SelBytes 3 == I.calldata.extract 0 4) = true := by
                simpa [amm4SelIs, amm4SelBytes] using h3
              have hmatch := amm4LowMatches 3 (by omega) hsz hm
              have hreach := amm4ReachLowBody 3 (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                (by omega) ⟨275⟩ hcode hwv hsz hsize
                (amm4LowPivotTaken 3 (by omega) hsz hm)
                hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
              exact amm4MintBodyCore hcode hsize hperm hwv h3 hreach hAccounts
            ·
              by_cases h4 : amm4SelIs I ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩
              · have hm : (amm4SelBytes 4 == I.calldata.extract 0 4) = true := by
                  simpa [amm4SelIs, amm4SelBytes] using h4
                have hmatch := amm4HighMatches 0 (by omega) hsz hm
                have hreach := amm4ReachHighBody 0 (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  (by omega) ⟨323⟩ hcode hwv hsz hsize
                  (amm4HighPivotNotTaken 0 (by omega) hsz hm)
                  hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                exact amm4SwapBodyCore hcode hsize hperm hwv h4 hreach hAccounts
              ·
                by_cases h5 : amm4SelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
                · have hm : (amm4SelBytes 5 == I.calldata.extract 0 4) = true := by
                    simpa [amm4SelIs, amm4SelBytes] using h5
                  have hmatch := amm4HighMatches 1 (by omega) hsz hm
                  have hreach := amm4ReachHighBody 1 (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    (by omega) ⟨351⟩ hcode hwv hsz hsize
                    (amm4HighPivotNotTaken 1 (by omega) hsz hm)
                    hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                  exact amm4BalanceOfBodyCore hcode hsize hperm hwv h5 hreach hAccounts
                ·
                  by_cases h6 : amm4SelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩
                  · have hm : (amm4SelBytes 6 == I.calldata.extract 0 4) = true := by
                      simpa [amm4SelIs, amm4SelBytes] using h6
                    have hmatch := amm4HighMatches 2 (by omega) hsz hm
                    have hreach := amm4ReachHighBody 2 (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      (by omega) ⟨399⟩ hcode hwv hsz hsize
                      (amm4HighPivotNotTaken 2 (by omega) hsz hm)
                      hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                    exact amm4TransferBodyCore hcode hsize hperm hwv h6 hreach hAccounts
                  ·
                    by_cases h7 : amm4SelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                    · have hm : (amm4SelBytes 7 == I.calldata.extract 0 4) = true := by
                        simpa [amm4SelIs, amm4SelBytes] using h7
                      have hmatch := amm4HighMatches 3 (by omega) hsz hm
                      have hreach := amm4ReachHighBody 3 (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        (by omega) ⟨447⟩ hcode hwv hsz hsize
                        (amm4HighPivotNotTaken 3 (by omega) hsz hm)
                        hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                      exact amm4AllowanceBodyCore hcode hsize hperm hwv h7 hreach hAccounts
                    ·
                      by_cases h8 : amm4SelIs I ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩
                      · have hm : (amm4SelBytes 8 == I.calldata.extract 0 4) = true := by
                          simpa [amm4SelIs, amm4SelBytes] using h8
                        have hmatch := amm4HighMatches 4 (by omega) hsz hm
                        have hreach := amm4ReachHighBody 4 (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
                          (by omega) ⟨495⟩ hcode hwv hsz hsize
                          (amm4HighPivotNotTaken 4 (by omega) hsz hm)
                          hmatch.1 hmatch.2 (by jump_dest) (by native_decide)
                        exact amm4BurnBodyCore hcode hsize hperm hwv h8 hreach hAccounts
                      ·
                        refine amm4NoDispatch hcode hsize hperm hwv ?_
                        intro i hi
                        interval_cases i
                        · simpa [amm4SelIs, amm4SelBytes] using h0
                        · simpa [amm4SelIs, amm4SelBytes] using h1
                        · simpa [amm4SelIs, amm4SelBytes] using h2
                        · simpa [amm4SelIs, amm4SelBytes] using h3
                        · simpa [amm4SelIs, amm4SelBytes] using h4
                        · simpa [amm4SelIs, amm4SelBytes] using h5
                        · simpa [amm4SelIs, amm4SelBytes] using h6
                        · simpa [amm4SelIs, amm4SelBytes] using h7
                        · simpa [amm4SelIs, amm4SelBytes] using h8
    · exact amm4ShortRevert hcode hsize hperm hwv (by omega)
  · exact amm4NonPayable hcode hwv

theorem amm4ContractCorrect :
    contractEquivalence config amm4CreationBytecode amm4Bytecode contract :=
  contractEquivalence.intro amm4ConstructorCorrect amm4RuntimeCorrect

end Benchmarks.ActAmm4
