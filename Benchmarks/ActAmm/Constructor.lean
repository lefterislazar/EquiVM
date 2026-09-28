import Benchmarks.ActAmm.ConstructorFirstCallSource
import Benchmarks.ActAmm.ConstructorFirstCallDecode
import Benchmarks.ActAmm.ConstructorSecondCallSource
import Benchmarks.ActAmm.ConstructorSecondCallDecode
import Benchmarks.ActAmm.ConstructorArithmeticTrace
import Benchmarks.ActAmm.ConstructorArithmeticSource
import Benchmarks.ActAmm.ConstructorGuardTrace
import Benchmarks.ActAmm.ConstructorPostGuardSender
import Benchmarks.ActAmm.ConstructorPostGuardSource
import Benchmarks.ActAmm.ConstructorPostGuardBridge
import Benchmarks.ActAmm.ConstructorReserve1Source
import Reasoning.Solc
import Solm.Equiv

/-!
# Act AMM constructor-equivalence target

The creation code includes the inherited `Token` constructor and the four reserve-token
`balanceOf` calls made by `Amm` construction.  The proof is intentionally the benchmark task.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

theorem ammConstructorNonpayableFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment ammCreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I ammBytecode := by
  rcases ammCtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, _h0, _hlt, hdeployed⟩
  subst args
  let tail := ammCtorArgTail t0 t1 (EVM.word liquidity.toNat)
  have hcodeTail : I.code = ammCreationBytecode ++ tail := by
    rw [hcode, hdeployed]
    simp [tail, ammCtorArgTail, ByteArray.append_assoc]
  have hrd := ammCtorNonpayableRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) tail hcodeTail hwv
  rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (ammSolmCtorExecReverts_nonpayable
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem ammConstructorUnderflowFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment ammCreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩)
    (hunder : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] →
        liquidity.toNat < 1000) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I ammBytecode := by
  rcases ammCtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
  have hunder' : liquidity.toNat < 1000 := hunder t0 t1 liquidity hargs
  subst args
  have hcodeCtor : I.code = ammCtorCode t0 t1 (EVM.word liquidity.toNat) := by
    rw [hcode, hdeployed]
    simp [ammCtorCode, ammCtorArgTail, ByteArray.append_assoc]
  have hword := constructorUInt256Word_toNat liquidity h0 hlt
  have hrd := ammCtorBaseUnderflowRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) t0 t1 (EVM.word liquidity.toNat)
    hcodeCtor hwv (by simpa [hword] using hunder')
  rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (ammSolmCtorExecReverts_underflow
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity h0 hunder' hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem ammConstructorEqualTokensFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment ammCreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] →
        1000 ≤ liquidity.toNat)
    (heq : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] → t0 = t1) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I ammBytecode := by
  rcases ammCtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
  have hle' : 1000 ≤ liquidity.toNat := hle t0 t1 liquidity hargs
  have heq' : t0 = t1 := heq t0 t1 liquidity hargs
  subst args
  have hcodeCtor : I.code = ammCtorCode t0 t1 (EVM.word liquidity.toNat) := by
    rw [hcode, hdeployed]
    simp [ammCtorCode, ammCtorArgTail, ByteArray.append_assoc]
  have hword := constructorUInt256Word_toNat liquidity h0 hlt
  have hrd := ammCtorEqualTokensRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) t0 t1 (EVM.word liquidity.toNat)
    hcodeCtor hwv hperm (by simpa [hword] using hle') heq'
  rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (ammSolmCtorExecReverts_equalTokens
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity h0 hle' (by simpa [UInt256.size] using hlt) heq' hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem ammConstructorBodyCore :
    constructorEquivalence config ammCreationBytecode contract ammBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args
    deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases ammCtorDeployment_shape hdeploy with
      ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
    subst args
    by_cases hunder : liquidity.toNat < 1000
    · apply ammConstructorUnderflowFor hdeploy hcode hwv
      intro a b l hargs'
      simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
      rcases hargs' with ⟨_, _, hl⟩
      simpa [hl] using hunder
    · have hle : 1000 ≤ liquidity.toNat := Nat.le_of_not_lt hunder
      by_cases heq : t0 = t1
      · apply ammConstructorEqualTokensFor hdeploy hcode hwv hperm
        · intro a b l hargs'
          simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
          rcases hargs' with ⟨_, _, hl⟩
          simpa [hl] using hle
        · intro a b l hargs'
          simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
          rcases hargs' with ⟨ha, hb, _⟩
          simpa [← ha, ← hb] using heq
      · have hcodeCtor : I.code = ammCtorCode t0 t1 (EVM.word liquidity.toNat) := by
          rw [hcode, hdeployed]
          simp [ammCtorCode, ammCtorArgTail, ByteArray.append_assoc]
        by_cases hdepth : I.depth.val < 1024
        · obtain ⟨createdAccounts', σ', z, ret, A', k, C,
            hrd, hcall, hretsz, hretbound⟩ :=
            ammCtorFirstStaticcall
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              t0 t1 (EVM.word liquidity.toNat) hcodeCtor hwv hperm
              (by simpa [constructorUInt256Word_toNat liquidity h0 hlt] using hle)
              heq hdepth
          cases z with
          | false =>
            have hrdrev := ammCtorFirstCallFailed hrd hretsz
              (by simp only [List.length_cons, List.length_nil]; omega)
            rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
            · exact constructorEquivalenceFor.outOfGas
                (by simpa [Sat256.ofUInt256] using hOOG)
            · obtain ⟨σ'_solm, hcallSolm, _⟩ :=
                ammCtorFirstCallSourceTransport
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  hAccounts (by simpa [initState] using hcall)
              refine constructorEquivalenceFor.execution
                (by simpa [Sat256.ofUInt256] using hrev) ?_ (ctorResultEquiv.revert rfl rfl)
              exact ammSolmCtorExecReverts_firstCallFailed
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                (σ₀ := σ₀) (g := g) (A := A) (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                heq hwv hAccounts hcallSolm
          | true =>
            obtain ⟨_, _, rd441⟩ := ammCtorFirstCallSucceeded hrd
            obtain ⟨_, _, rd444⟩ := ammCtorFirstCallFreePtr hretsz rd441
            obtain ⟨_, _, rd459⟩ := ammCtorFirstCallReturnAlloc rd444
            obtain ⟨_, _, rd1617⟩ := ammCtorFirstCallToDecoder rd459
            by_cases hshort : ret.size < 32
            · have hrdrev := ammCtorFirstCallDecodeShortReverts hshort rd1617
              rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
              · exact constructorEquivalenceFor.outOfGas
                  (by simpa [Sat256.ofUInt256] using hOOG)
              · obtain ⟨σ'_solm, hcallSolm, _⟩ :=
                  ammCtorFirstCallSourceTransport
                    (createdAccounts := createdAccounts)
                    (genesisBlockHeader := genesisBlockHeader)
                    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                    (σ₀ := σ₀) (g := g) (A := A) (I := I)
                    t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                    hAccounts (by simpa [initState] using hcall)
                refine constructorEquivalenceFor.execution
                  (by simpa [Sat256.ofUInt256] using hrev) ?_
                  (ctorResultEquiv.revert rfl rfl)
                exact ammSolmCtorExecReverts_firstCallShort
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  heq hwv hAccounts hshort hcallSolm
            · have hlo : 32 ≤ ret.size := Nat.le_of_not_lt hshort
              obtain ⟨σS1, hcallS1, hAccounts1⟩ :=
                ammCtorFirstCallSourceTransport
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  hAccounts (by simpa [initState] using hcall)
              have hpostShape := ammCtorFirstCallSourcePost_shape
                (createdAccounts := createdAccounts) (cA := createdAccounts')
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ := σ_solm) (σs := σS1)
                (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
              have hprefixRaw := ammCtorSourceInitialBalance1Success
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                (σ₀ := σ₀) (g := g) (A := A) (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                heq hwv hAccounts hlo hretbound hcallS1
              have hprefix : ExecBlock config
                  { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
                  (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                    (Sat256.ofUInt256 g) A I)
                  (ammCtorSourceStoredPrefix ++
                    [tokenBalance (.storage token1Ref) "initialBalance1"])
                  (.ok { contract := contract, locals :=
                    ammCtorAfterInitialBalance1Locals t0 t1 liquidity ret }
                    (initState createdAccounts' genesisBlockHeader blocks σS1 σ₀
                      (Sat256.ofUInt256 g) A' I)) := by
                simpa only [hpostShape] using hprefixRaw
              obtain ⟨_, _, rd1381⟩ :=
                ammCtorFirstCallDecodeToWordLoad hlo hretbound rd1617
              obtain ⟨_, _, rd472⟩ :=
                ammCtorFirstCallDecodeWord hlo hretsz rd1381
              obtain ⟨_, _, rd529⟩ := ammCtorSecondCallTarget rd472
              obtain ⟨_, _, rd538⟩ := ammCtorSecondCallFreePtrLoaded hretsz rd529
              obtain ⟨_, _, rd550⟩ := ammCtorSecondCallSelectorStored rd538
              obtain ⟨_, _, rd562⟩ := ammCtorSecondCallEncoded rd550
              obtain ⟨gasWord2, _, _, rd574⟩ :=
                ammCtorSecondCallStaticcallFrame hlo hretbound rd562
              obtain ⟨createdAccounts2, σE2, z2, ret2, A2, k2, C2,
                rd575, hcall2, hretsz2, hretbound2⟩ :=
                ammCtorSecondStaticcall (Apre := A') hlo hretbound hdepth rd574
              obtain ⟨σS2, hcallS2, hAccounts2⟩ :=
                ammCtorSecondCallSourceTransport hAccounts1 hcall2
              cases z2 with
              | false =>
                have hrdrev := ammCtorSecondCallFailed rd575 hretsz2
                  (by simp only [List.length_cons, List.length_nil]; omega)
                rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                · exact constructorEquivalenceFor.outOfGas
                    (by simpa [Sat256.ofUInt256] using hOOG)
                · refine constructorEquivalenceFor.execution
                    (by simpa [Sat256.ofUInt256] using hrev) ?_
                    (ctorResultEquiv.revert rfl rfl)
                  exact ammSolmCtorExecReverts_secondCallFailed
                    (createdAccounts := createdAccounts) (cA := createdAccounts')
                    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
                    (σstart := σ_solm) (σ_evm := σ') (σ_solm := σS1)
                    (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                    t0 t1 liquidity hAccounts1 hprefix hcallS2
              | true =>
                obtain ⟨_, _, rd594⟩ := ammCtorSecondCallSucceeded rd575
                obtain ⟨_, _, rd597⟩ :=
                  ammCtorSecondReturnFreePtrLoaded hlo hretbound hretsz2 rd594
                obtain ⟨_, _, rd612⟩ :=
                  ammCtorSecondCallReturnAlloc hlo hretbound rd597
                obtain ⟨_, _, rd1617_2⟩ := ammCtorSecondCallToDecoder rd612
                by_cases hshort2 : ret2.size < 32
                · have hrdrev := ammCtorSecondCallDecodeShortReverts
                    hretbound hshort2 rd1617_2
                  rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                  · exact constructorEquivalenceFor.outOfGas
                      (by simpa [Sat256.ofUInt256] using hOOG)
                  · refine constructorEquivalenceFor.execution
                      (by simpa [Sat256.ofUInt256] using hrev) ?_
                      (ctorResultEquiv.revert rfl rfl)
                    exact ammSolmCtorExecReverts_secondCallShort
                      (createdAccounts := createdAccounts) (cA := createdAccounts')
                      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
                      (σstart := σ_solm) (σ_evm := σ') (σ_solm := σS1)
                      (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                      t0 t1 liquidity hAccounts1 hshort2 hprefix hcallS2
                · have hlo2 : 32 ≤ ret2.size := Nat.le_of_not_lt hshort2
                  obtain ⟨_, _, rd625⟩ :=
                    ammCtorSecondCallDecodeWord hlo hretbound hlo2 hretbound2
                      rd1617_2
                  have hprefix2 := ammCtorSourceInitialBalance0Success
                    (createdAccounts := createdAccounts) (cA := createdAccounts')
                    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
                    (σstart := σ_solm) (σ_evm := σ') (σ_solm := σS1)
                    (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                    t0 t1 liquidity hAccounts1 hlo2 hretbound2 hprefix hcallS2
                  have hv0 :
                      (UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))).toNat =
                        fromByteArrayBigEndian (ret2.extract 0 32) :=
                    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo2)
                  have hv1 :
                      (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32))).toNat =
                        fromByteArrayBigEndian (ret.extract 0 32) :=
                    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
                  have haw2 : 3 ≤ (ammCtorSecondCallArgWords ret).toNat := by
                    rw [ammCtorSecondCallArgWords_toNat ret hlo hretbound]
                    omega
                  by_cases hfitProduct :
                      (fromByteArrayBigEndian (ret2.extract 0 32)) *
                        (fromByteArrayBigEndian (ret.extract 0 32)) < UInt256.size
                  · have hfitProductWord :
                        (UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))).toNat *
                          (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32))).toNat <
                            UInt256.size := by
                      simpa only [hv0, hv1] using hfitProduct
                    obtain ⟨_, _, rd635⟩ :=
                      ammCtorInitialProductOk rd625 hfitProductWord
                    have hprefixProduct :=
                      ammCtorSourceProductSuccess t0 t1 liquidity
                        hfitProduct hprefix2
                    by_cases hfitSquare : liquidity.toNat * liquidity.toNat < UInt256.size
                    · have hword := constructorUInt256Word_toNat liquidity h0 hlt
                      have hfitSquareWord :
                          (EVM.word liquidity.toNat).toNat *
                            (EVM.word liquidity.toNat).toNat < UInt256.size := by
                        simpa only [hword] using hfitSquare
                      obtain ⟨_, _, rd647⟩ :=
                        ammCtorLiquiditySquareOk rd635 hfitSquareWord
                      have hprefixSquare :=
                        ammCtorSourceSquareSuccess t0 t1 liquidity h0 hfitSquare
                          hprefixProduct
                      have hproductMul :
                          (UInt256.mul
                            (UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32)))
                            (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))).toNat =
                              (fromByteArrayBigEndian (ret2.extract 0 32)) *
                                (fromByteArrayBigEndian (ret.extract 0 32)) := by
                        rw [u256_mul_toNat, hv0, hv1, Nat.mod_eq_of_lt hfitProduct]
                      have hsquareMul :
                          (UInt256.mul (EVM.word liquidity.toNat)
                            (EVM.word liquidity.toNat)).toNat =
                              liquidity.toNat * liquidity.toNat := by
                        rw [u256_mul_toNat, hword, Nat.mod_eq_of_lt hfitSquare]
                      by_cases heqProduct : liquidity.toNat * liquidity.toNat =
                          (fromByteArrayBigEndian (ret2.extract 0 32)) *
                            (fromByteArrayBigEndian (ret.extract 0 32))
                      · have heqWord :
                            UInt256.mul (EVM.word liquidity.toNat)
                              (EVM.word liquidity.toNat) =
                                UInt256.mul
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret2.extract 0 32)))
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret.extract 0 32))) := by
                          apply u256_inj
                          rw [hsquareMul, hproductMul]
                          exact heqProduct
                        obtain ⟨_, _, rd711⟩ :=
                          ammCtorProductEqualityOk rd647 heqWord
                        obtain ⟨_, _, rd777⟩ :=
                          ammCtorPositiveLiquidityOk rd711
                            (by rw [hword]; omega)
                        have hprefixGuards :=
                          ammCtorSourceGuardsSuccess t0 t1 liquidity
                            heqProduct (by omega : 0 < liquidity) hprefixSquare
                        have hmem64 : 64 ≤
                            (ammCtorSecondCallDecodeMem I t0 t1
                              (EVM.word liquidity.toNat) ret ret2).size := by
                          rw [ammCtorSecondCallDecodeMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound (by
                              have hb := hretbound2
                              norm_num [UInt256.size] at *
                              omega)]
                          have hs := ammCtorSecondCallArgMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret hretbound
                          have hp := (ammCtorSecondCallFreePtr_bounds ret hretbound).1
                          omega
                        obtain ⟨_, _, rd784⟩ :=
                          ammCtorPostGuardSupplyStored rd777 hperm
                        obtain ⟨_, _, rd852⟩ :=
                          ammCtorPostGuardSelfBalanceStored rd784 hperm haw2 hmem64
                        obtain ⟨_, _, rd865⟩ :=
                          ammCtorPostGuardBaseSupplyRecomputed rd852
                            (by rw [hword]; exact hle)
                        have hmem64' : 64 ≤
                            (twoWordHashMem (UInt256.ofNat I.codeOwner.val) ⟨1⟩
                              (ammCtorSecondCallDecodeMem I t0 t1
                                (EVM.word liquidity.toNat) ret ret2)).size := by
                          rw [ammCtorTwoWordHashMem_size _ _ _ hmem64]
                          exact hmem64
                        obtain ⟨_, _, rd931⟩ :=
                          ammCtorPostGuardSenderBalanceStored rd865 hperm
                            haw2 hmem64'
                        have hprefixStorage :=
                          ammCtorSourcePostGuardStorageSuccess
                            t0 t1 liquidity h0
                            (by simpa [UInt256.size] using hlt)
                            (by simp [initState]) (by simp [initState])
                            hprefixGuards
                        have hAccounts3 : accountMapEquiv
                            (ammCtorPostGuardEvmMap I σE2 (EVM.word liquidity.toNat))
                            (ammCtorPostGuardEvmMap I σS2 (EVM.word liquidity.toNat)) :=
                          ammCtorPostGuardMaps_equiv I σE2 σS2
                            (EVM.word liquidity.toNat) hAccounts2
                        have hpostStorageShape := ammCtorPostGuardSourceState_shape
                          (createdAccounts := createdAccounts2)
                          (genesisBlockHeader := genesisBlockHeader)
                          (blocks := blocks) (σ := σS2) (σ₀ := σ₀)
                          (g := g) (A := A2) (I := I) liquidity h0 hle
                          (by simpa [UInt256.size] using hlt)
                        obtain ⟨_, _, rd987⟩ := ammCtorThirdCallTarget rd931
                        have hpost96 : 96 ≤
                            (ammCtorPostGuardMem I t0 t1
                              (EVM.word liquidity.toNat) ret ret2).size := by
                          rw [ammCtorPostGuardMem_baseSize I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound hretbound2]
                          rw [ammCtorSecondCallDecodeMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound (by
                              have hb := hretbound2
                              norm_num [UInt256.size] at *
                              omega)]
                          have hs := ammCtorSecondCallArgMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret hretbound
                          have hp := (ammCtorSecondCallFreePtr_bounds ret hretbound).1
                          omega
                        have hbelow64 :
                            ¬ (⟨64⟩ : UInt256) ≥
                              ammCtorSecondCallArgWords ret * ⟨32⟩ := by
                          intro hh
                          have hfp64 : (⟨64⟩ : UInt256) ≤
                              ammCtorSecondCallFreePtr ret := by
                            change 64 ≤ (ammCtorSecondCallFreePtr ret).toNat
                            exact le_trans (by decide)
                              (ammCtorSecondCallFreePtr_bounds ret hretbound).1
                          exact (ammCtorSecondCallArgWords_ptr_haw ret hlo hretbound)
                            (le_trans hh hfp64)
                        have hload3 :
                            (if (⟨64⟩ : UInt256).toNat ≥
                                  (ammCtorPostGuardMem I t0 t1
                                    (EVM.word liquidity.toNat) ret ret2).size ∨
                                (⟨64⟩ : UInt256) ≥
                                  ammCtorSecondCallArgWords ret * ⟨32⟩
                             then ⟨0⟩
                             else UInt256.ofNat (fromByteArrayBigEndian
                               ((ammCtorPostGuardMem I t0 t1
                                 (EVM.word liquidity.toNat) ret ret2).readWithPadding
                                 64 32))) =
                              ammCtorAfterSecondReturnFreePtr ret ret2 := by
                          have hmem64 :
                              ¬ (⟨64⟩ : UInt256).toNat ≥
                                (ammCtorPostGuardMem I t0 t1
                                  (EVM.word liquidity.toNat) ret ret2).size := by
                            change ¬ 64 ≥
                              (ammCtorPostGuardMem I t0 t1
                                (EVM.word liquidity.toNat) ret ret2).size
                            omega
                          rw [if_neg (not_or.mpr ⟨hmem64, hbelow64⟩)]
                          rw [ammCtorPostGuardMem_read64 I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound hretbound2,
                            fromByteArrayBigEndian_toByteArray,
                            u256_ofNat_toNat]
                        obtain ⟨_, _, rd996⟩ :=
                          ammCtorThirdCallFreePtrLoaded
                            (by simpa only [ammCtorPostGuardMem,
                              ammCtorPostGuardEvmMap] using rd987)
                            haw2 hload3
                        obtain ⟨_, _, rd1008⟩ :=
                          ammCtorThirdCallSelectorStored rd996
                        obtain ⟨_, _, rd1020⟩ :=
                          ammCtorThirdCallEncoded rd1008
                        obtain ⟨gasWord3, _, _, rd1032⟩ :=
                          ammCtorThirdCallStaticcallFrame hlo hretbound
                            hlo2 hretbound2 rd1020
                        obtain ⟨createdAccounts3, σE3, z3, ret3, A3,
                          k3, C3, rd1033, hcall3, hretsz3, hretbound3⟩ :=
                          ammCtorThirdStaticcall (Apre := A2)
                            hlo hretbound hlo2 hretbound2 hdepth rd1032
                        obtain ⟨σS3, hcallS3, hAccounts3'⟩ :=
                          ammCtorSecondCallSourceTransport hAccounts3 hcall3
                        have hprefix3 : ExecBlock config
                            ⟨contract, ammCtorLocals t0 t1 liquidity⟩
                            (initState createdAccounts genesisBlockHeader blocks
                              σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            ammCtorSourcePostGuardPrefix
                            (.ok ⟨contract,
                              ammCtorAfterSquareLocals t0 t1 liquidity ret ret2⟩
                              (initState createdAccounts2 genesisBlockHeader blocks
                                (ammCtorPostGuardEvmMap I σS2
                                  (EVM.word liquidity.toNat)) σ₀
                                (Sat256.ofUInt256 g) A2 I)) := by
                          rw [← hpostStorageShape]
                          simpa only [ammCtorSourcePostGuardPrefix,
                            initState] using hprefixStorage
                        cases z3 with
                        | false =>
                          have hrdrev := ammCtorThirdCallFailed rd1033 hretsz3
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                          · exact constructorEquivalenceFor.outOfGas
                              (by simpa [Sat256.ofUInt256] using hOOG)
                          · refine constructorEquivalenceFor.execution
                              (by simpa [Sat256.ofUInt256] using hrev) ?_
                              (ctorResultEquiv.revert rfl rfl)
                            exact ammSolmCtorExecReverts_thirdCallFailed
                              t0 t1 liquidity hAccounts3 hprefix3 hcallS3
                        | true =>
                          obtain ⟨_, _, rd1052⟩ := ammCtorThirdCallSucceeded rd1033
                          obtain ⟨_, _, rd1055⟩ :=
                            ammCtorThirdReturnFreePtrLoaded hlo hretbound
                              hlo2 hretbound2 hretsz3 rd1052
                          obtain ⟨_, _, rd1070⟩ :=
                            ammCtorThirdCallReturnAlloc hlo hretbound
                              hlo2 hretbound2 rd1055
                          obtain ⟨_, _, rd1617_3⟩ :=
                            ammCtorThirdCallToDecoder rd1070
                          by_cases hshort3 : ret3.size < 32
                          · have hrdrev := ammCtorThirdCallDecodeShortReverts
                              hretbound hretbound2 hshort3 rd1617_3
                            rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                            · exact constructorEquivalenceFor.outOfGas
                                (by simpa [Sat256.ofUInt256] using hOOG)
                            · refine constructorEquivalenceFor.execution
                                (by simpa [Sat256.ofUInt256] using hrev) ?_
                                (ctorResultEquiv.revert rfl rfl)
                              exact ammSolmCtorExecReverts_thirdCallShort
                                t0 t1 liquidity hAccounts3 hshort3 hprefix3 hcallS3
                          · have hlo3 : 32 ≤ ret3.size := Nat.le_of_not_lt hshort3
                            obtain ⟨_, _, rd1083⟩ :=
                              ammCtorThirdCallDecodeWord hlo hretbound
                                hlo2 hretbound2 hlo3 hretbound3 rd1617_3
                            obtain ⟨_, _, rd1090⟩ :=
                              ammCtorReserve0Stored rd1083 hperm
                            have hprefixReserve0 :=
                              ammCtorSourceReserveBalance0Success
                                t0 t1 liquidity hAccounts3 hlo3 hretbound3
                                hprefix3 hcallS3
                            have hprefixReserve0Store :=
                              ammCtorSourceReserve0Stored t0 t1 liquidity
                                hlo3 hprefixReserve0
                            have hAccounts4 : accountMapEquiv
                                (ammCtorReserve0Map I σE3
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret3.extract 0 32))))
                                (ammCtorReserve0Map I σS3
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret3.extract 0 32)))) :=
                              ammCtorReserve0Maps_equiv I σE3 σS3 _ hAccounts3'
                            obtain ⟨_, _, rd1146⟩ := ammCtorFourthCallTarget rd1090
                            have hmem4 : 96 ≤
                                (ammCtorThirdCallDecodeMem I t0 t1
                                  (EVM.word liquidity.toNat) ret ret2 ret3).size := by
                              rw [ammCtorThirdCallDecodeMem_size I t0 t1
                                (EVM.word liquidity.toNat) ret ret2 ret3
                                hretbound hretbound2 hretsz3]
                              have hs := ammCtorThirdCallArgMem_size I t0 t1
                                (EVM.word liquidity.toNat) ret ret2
                                hretbound hretbound2
                              have hp := (ammCtorAfterSecondReturnFreePtr_bounds
                                ret ret2 hretbound hretbound2).1
                              omega
                            have hload4 :
                                (if (⟨64⟩ : UInt256).toNat ≥
                                      (ammCtorThirdCallDecodeMem I t0 t1
                                        (EVM.word liquidity.toNat) ret ret2 ret3).size ∨
                                    (⟨64⟩ : UInt256) ≥
                                      ammCtorThirdCallArgWords ret ret2 * ⟨32⟩
                                 then ⟨0⟩
                                 else UInt256.ofNat (fromByteArrayBigEndian
                                   ((ammCtorThirdCallDecodeMem I t0 t1
                                     (EVM.word liquidity.toNat) ret ret2 ret3).readWithPadding
                                     64 32))) =
                                  ammCtorAfterThirdReturnFreePtr ret ret2 ret3 := by
                              have hmem64 : ¬ (⟨64⟩ : UInt256).toNat ≥
                                  (ammCtorThirdCallDecodeMem I t0 t1
                                    (EVM.word liquidity.toNat) ret ret2 ret3).size := by
                                change ¬ 64 ≥ _
                                omega
                              have haw64 := ammCtorThirdCallArgWords_mload64_haw
                                ret ret2 hlo hretbound hlo2 hretbound2
                              rw [if_neg (not_or.mpr ⟨hmem64, haw64⟩)]
                              rw [ammCtorThirdCallDecodeMem_read64 I t0 t1
                                (EVM.word liquidity.toNat) ret ret2 ret3
                                hretbound hretbound2 hretsz3,
                                fromByteArrayBigEndian_toByteArray,
                                u256_ofNat_toNat]
                            obtain ⟨_, _, rd1155⟩ :=
                              ammCtorFourthCallFreePtrLoaded rd1146
                                (by
                                  rw [ammCtorThirdCallArgWords_toNat ret ret2
                                    hlo hretbound hlo2 hretbound2]
                                  omega)
                                hload4
                            obtain ⟨_, _, rd1167⟩ :=
                              ammCtorFourthCallSelectorStored rd1155
                            obtain ⟨_, _, rd1179⟩ :=
                              ammCtorFourthCallEncoded rd1167
                            obtain ⟨gasWord4, _, _, rd1191⟩ :=
                              ammCtorFourthCallStaticcallFrame
                                hlo hretbound hlo2 hretbound2
                                hlo3 hretbound3 rd1179
                            obtain ⟨createdAccounts4, σE4, z4, ret4, A4,
                              k4, C4, rd1192, hcall4, hretsz4, hretbound4⟩ :=
                              ammCtorFourthStaticcall (Apre := A3)
                                hlo hretbound hlo2 hretbound2
                                hlo3 hretbound3 hdepth rd1191
                            obtain ⟨σS4, hcallS4, hAccounts4'⟩ :=
                              ammCtorFourthCallSourceTransport hAccounts4 hcall4
                            have hprefix4 : ExecBlock config
                                ⟨contract, ammCtorLocals t0 t1 liquidity⟩
                                (initState createdAccounts genesisBlockHeader blocks
                                  σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                ammCtorSourceReserve0Prefix
                                (.ok ⟨contract,
                                  ammCtorAfterReserveBalance0Locals
                                    t0 t1 liquidity ret ret2 ret3⟩
                                  (initState createdAccounts3 genesisBlockHeader blocks
                                    (ammCtorReserve0Map I σS3
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret3.extract 0 32)))) σ₀
                                    (Sat256.ofUInt256 g) A3 I)) := by
                              rw [← ammCtorAfterReserve0Store_shape]
                              simpa only [ammCtorSourceReserve0Prefix,
                                initState] using hprefixReserve0Store
                            cases z4 with
                            | false =>
                              have hrdrev := ammCtorFourthCallFailed rd1192 hretsz4
                                (by simp only [List.length_cons, List.length_nil]; omega)
                              rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                              · exact constructorEquivalenceFor.outOfGas
                                  (by simpa [Sat256.ofUInt256] using hOOG)
                              · refine constructorEquivalenceFor.execution
                                  (by simpa [Sat256.ofUInt256] using hrev) ?_
                                  (ctorResultEquiv.revert rfl rfl)
                                exact ammSolmCtorExecReverts_fourthCallFailed
                                  t0 t1 liquidity hAccounts4 hprefix4 hcallS4
                            | true =>
                              obtain ⟨_, _, rd1211⟩ :=
                                ammCtorFourthCallSucceeded rd1192
                              obtain ⟨_, _, rd1214⟩ :=
                                ammCtorFourthReturnFreePtrLoaded
                                  hlo hretbound hlo2 hretbound2
                                  hlo3 hretbound3 hretsz4 rd1211
                              obtain ⟨_, _, rd1229⟩ :=
                                ammCtorFourthCallReturnAlloc
                                  hlo hretbound hlo2 hretbound2
                                  hlo3 hretbound3 rd1214
                              obtain ⟨_, _, rd1617_4⟩ :=
                                ammCtorFourthCallToDecoder rd1229
                              by_cases hshort4 : ret4.size < 32
                              · have hrdrev := ammCtorFourthCallDecodeShortReverts
                                  hretbound hretbound2 hretbound3 hshort4
                                  rd1617_4
                                rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                                · exact constructorEquivalenceFor.outOfGas
                                    (by simpa [Sat256.ofUInt256] using hOOG)
                                · refine constructorEquivalenceFor.execution
                                    (by simpa [Sat256.ofUInt256] using hrev) ?_
                                    (ctorResultEquiv.revert rfl rfl)
                                  exact ammSolmCtorExecReverts_fourthCallShort
                                    t0 t1 liquidity hAccounts4 hshort4
                                    hprefix4 hcallS4
                              · have hlo4 : 32 ≤ ret4.size := Nat.le_of_not_lt hshort4
                                obtain ⟨_, _, rd1242⟩ :=
                                  ammCtorFourthCallDecodeWord
                                    hlo hretbound hlo2 hretbound2
                                    hlo3 hretbound3 hlo4 hretbound4
                                    rd1617_4
                                obtain ⟨_, _, rd1252⟩ :=
                                  ammCtorReserve1Stored rd1242 hperm
                                have hprefixReserve1 :=
                                  ammCtorSourceReserveBalance1Success
                                    t0 t1 liquidity hAccounts4 hlo4 hretbound4
                                    hprefix4 hcallS4
                                have hprefixReserve1Store :=
                                  ammCtorSourceReserve1Stored t0 t1 liquidity
                                    hlo4 hprefixReserve1
                                have hAccountsFinal : accountMapEquiv
                                    (ammCtorReserve1Map I σE4
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret4.extract 0 32))))
                                    (ammCtorReserve1Map I σS4
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret4.extract 0 32)))) :=
                                  ammCtorReserve1Maps_equiv I σE4 σS4 _ hAccounts4'
                                have hret := ammCtorReturnRuntime rd1252
                                have hprefixFinal : ExecBlock config
                                    ⟨contract, ammCtorLocals t0 t1 liquidity⟩
                                    (initState createdAccounts genesisBlockHeader
                                      blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    ((ammCtorSourceReserve0Prefix ++
                                      [tokenBalance (.storage token1Ref)
                                        "reserveBalance1"]) ++
                                      [.assign .storage reserve1Ref
                                        (.var "reserveBalance1")])
                                    (.ok ⟨contract,
                                      ammCtorAfterReserveBalance1Locals
                                        t0 t1 liquidity ret ret2 ret3 ret4⟩
                                      (initState createdAccounts4 genesisBlockHeader
                                        blocks (ammCtorReserve1Map I σS4
                                          (UInt256.ofNat (fromByteArrayBigEndian
                                            (ret4.extract 0 32)))) σ₀
                                        (Sat256.ofUInt256 g) A4 I)) := by
                                  rw [← ammCtorAfterReserve1Store_shape]
                                  simpa only [initState] using hprefixReserve1Store
                                have hsourceFinal :=
                                  ammSolmCtorExecSuccess_afterReserves
                                    t0 t1 liquidity hprefixFinal
                                rcases hret with hOOG | ⟨s, hX, hacc⟩
                                · exact constructorEquivalenceFor.outOfGas
                                    (Xi_error_of_X (g := g) (by
                                      rw [← hcodeCtor] at hOOG
                                      simpa [initState, Sat256.ofUInt256] using hOOG))
                                · have hcA : s.createdAccounts = createdAccounts4 :=
                                    congrArg Prod.fst hacc
                                  have hσ : s.accountMap =
                                      ammCtorReserve1Map I σE4
                                        (UInt256.ofNat (fromByteArrayBigEndian
                                          (ret4.extract 0 32))) :=
                                    congrArg Prod.snd hacc
                                  have hsuccess := Xi_success_of_X (g := g) (by
                                    rw [← hcodeCtor] at hX
                                    simpa [initState, Sat256.ofUInt256] using hX)
                                  rw [hcA, hσ] at hsuccess
                                  refine constructorEquivalenceFor.execution
                                    hsuccess hsourceFinal ?_
                                  exact ctorResultEquiv.success rfl rfl
                                    (by simp [initState]) hAccountsFinal rfl
                      · have hneWord :
                            UInt256.mul (EVM.word liquidity.toNat)
                              (EVM.word liquidity.toNat) ≠
                                UInt256.mul
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret2.extract 0 32)))
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret.extract 0 32))) := by
                          intro heq
                          have hn := congrArg UInt256.toNat heq
                          rw [hsquareMul, hproductMul] at hn
                          exact heqProduct hn
                        have hrdrev := ammCtorProductEqualityMismatchReverts
                          rd647 hneWord
                        rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                        · exact constructorEquivalenceFor.outOfGas
                            (by simpa [Sat256.ofUInt256] using hOOG)
                        · refine constructorEquivalenceFor.execution
                            (by simpa [Sat256.ofUInt256] using hrev) ?_
                            (ctorResultEquiv.revert rfl rfl)
                          exact ammSolmCtorExecReverts_productMismatch
                            t0 t1 liquidity heqProduct hprefixSquare
                    · have hoverSquare : UInt256.size ≤
                          (EVM.word liquidity.toNat).toNat *
                            (EVM.word liquidity.toNat).toNat := by
                        have hword := constructorUInt256Word_toNat liquidity h0 hlt
                        simpa only [hword] using Nat.le_of_not_lt hfitSquare
                      have hrdrev := ammCtorLiquiditySquareOverflow rd635
                        hoverSquare haw2
                      rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                      · exact constructorEquivalenceFor.outOfGas
                          (by simpa [Sat256.ofUInt256] using hOOG)
                      · refine constructorEquivalenceFor.execution
                          (by simpa [Sat256.ofUInt256] using hrev) ?_
                          (ctorResultEquiv.revert rfl rfl)
                        exact ammSolmCtorExecReverts_squareOverflow
                          t0 t1 liquidity h0 (Nat.le_of_not_lt hfitSquare)
                          hprefixProduct
                  · have hoverProduct : UInt256.size ≤
                        (UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))).toNat *
                          (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32))).toNat := by
                      simpa only [hv0, hv1] using Nat.le_of_not_lt hfitProduct
                    have hrdrev := ammCtorInitialProductOverflow rd625
                      hoverProduct haw2
                    rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                    · exact constructorEquivalenceFor.outOfGas
                        (by simpa [Sat256.ofUInt256] using hOOG)
                    · refine constructorEquivalenceFor.execution
                        (by simpa [Sat256.ofUInt256] using hrev) ?_
                        (ctorResultEquiv.revert rfl rfl)
                      exact ammSolmCtorExecReverts_productOverflow
                        t0 t1 liquidity (Nat.le_of_not_lt hfitProduct) hprefix2
        · have hdepthEq : I.depth = (1024 : Fin 1025) := by
            apply Fin.ext
            have hbound := I.depth.isLt
            omega
          obtain ⟨_, _, _, rd421⟩ :=
            ammCtorReachInitialToken1Staticcall
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              t0 t1 (EVM.word liquidity.toNat) hcodeCtor hwv hperm
              (by simpa [constructorUInt256Word_toNat liquidity h0 hlt] using hle)
              heq
          obtain ⟨_, _, rd422⟩ := RD.solcStaticcallDepthLimit rd421
            (by amm_ctor_decode) hdepthEq
            (by simp only [List.length_cons, List.length_nil]; omega)
          have hrdrev := ammCtorFirstCallFailed rd422
            (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
          rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
          · exact constructorEquivalenceFor.outOfGas
              (by simpa [Sat256.ofUInt256] using hOOG)
          · refine constructorEquivalenceFor.execution
              (by simpa [Sat256.ofUInt256] using hrev) ?_ (ctorResultEquiv.revert rfl rfl)
            exact ammSolmCtorExecReverts_firstCallDepth
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
              (σ₀ := σ₀) (g := g) (A := A) (I := I)
              t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
              heq hwv hAccounts hdepthEq
  · exact ammConstructorNonpayableFor hdeploy hcode hwv

theorem ammConstructorCorrect :
    constructorEquivalence config ammCreationBytecode contract ammBytecode :=
  ammConstructorBodyCore

end Benchmarks.ActAmm
