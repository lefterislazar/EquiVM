import Benchmarks.ActAmm4.ConstructorFirstCallSource
import Benchmarks.ActAmm4.ConstructorFirstCallDecode
import Benchmarks.ActAmm4.ConstructorSecondCallSource
import Benchmarks.ActAmm4.ConstructorSecondCallDecode
import Benchmarks.ActAmm4.ConstructorArithmeticTrace
import Benchmarks.ActAmm4.ConstructorArithmeticSource
import Benchmarks.ActAmm4.ConstructorGuardTrace
import Benchmarks.ActAmm4.ConstructorPostGuardSender
import Benchmarks.ActAmm4.ConstructorPostGuardSource
import Benchmarks.ActAmm4.ConstructorPostGuardBridge
import Benchmarks.ActAmm4.ConstructorReserve1Source
import Reasoning.Solc
import Solm.Equiv

/-!
# Act sand/amm4 constructor equivalence

The creation code includes the inherited `Token` constructor and four reserve-token
`balanceOf` calls. Its executable prefix matches the Act AMM constructor after adjusting
the embedded runtime and creation-code lengths.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

theorem amm4ConstructorNonpayableFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment amm4CreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I amm4Bytecode := by
  rcases amm4CtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, _h0, _hlt, hdeployed⟩
  subst args
  let tail := amm4CtorArgTail t0 t1 (EVM.word liquidity.toNat)
  have hcodeTail : I.code = amm4CreationBytecode ++ tail := by
    rw [hcode, hdeployed]
    simp [tail, amm4CtorArgTail, ByteArray.append_assoc]
  have hrd := amm4CtorNonpayableRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) tail hcodeTail hwv
  rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (amm4SolmCtorExecReverts_nonpayable
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem amm4ConstructorUnderflowFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment amm4CreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩)
    (hunder : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] →
        liquidity.toNat < 1000) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I amm4Bytecode := by
  rcases amm4CtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
  have hunder' : liquidity.toNat < 1000 := hunder t0 t1 liquidity hargs
  subst args
  have hcodeCtor : I.code = amm4CtorCode t0 t1 (EVM.word liquidity.toNat) := by
    rw [hcode, hdeployed]
    simp [amm4CtorCode, amm4CtorArgTail, ByteArray.append_assoc]
  have hword := constructorUInt256Word_toNat liquidity h0 hlt
  have hrd := amm4CtorBaseUnderflowRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) t0 t1 (EVM.word liquidity.toNat)
    hcodeCtor hwv (by simpa [hword] using hunder')
  rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (amm4SolmCtorExecReverts_underflow
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity h0 hunder' hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem amm4ConstructorEqualTokensFor
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment amm4CreationBytecode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] →
        1000 ≤ liquidity.toNat)
    (heq : ∀ t0 t1 liquidity,
      args = [.address t0, .address t1, .int liquidity] → t0 = t1) :
    constructorEquivalenceFor config contract args createdAccounts genesisBlockHeader
      blocks σ_evm σ_solm σ₀ g A I amm4Bytecode := by
  rcases amm4CtorDeployment_shape hdeploy with
    ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
  have hle' : 1000 ≤ liquidity.toNat := hle t0 t1 liquidity hargs
  have heq' : t0 = t1 := heq t0 t1 liquidity hargs
  subst args
  have hcodeCtor : I.code = amm4CtorCode t0 t1 (EVM.word liquidity.toNat) := by
    rw [hcode, hdeployed]
    simp [amm4CtorCode, amm4CtorArgTail, ByteArray.append_assoc]
  have hword := constructorUInt256Word_toNat liquidity h0 hlt
  have hrd := amm4CtorEqualTokensRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) t0 t1 (EVM.word liquidity.toNat)
    hcodeCtor hwv hperm (by simpa [hword] using hle') heq'
  rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (amm4SolmCtorExecReverts_equalTokens
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        t0 t1 liquidity h0 hle' (by simpa [UInt256.size] using hlt) heq' hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem amm4ConstructorBodyCore :
    constructorEquivalence config amm4CreationBytecode contract amm4Bytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args
    deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · rcases amm4CtorDeployment_shape hdeploy with
      ⟨t0, t1, liquidity, hargs, h0, hlt, hdeployed⟩
    subst args
    by_cases hunder : liquidity.toNat < 1000
    · apply amm4ConstructorUnderflowFor hdeploy hcode hwv
      intro a b l hargs'
      simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
      rcases hargs' with ⟨_, _, hl⟩
      simpa [hl] using hunder
    · have hle : 1000 ≤ liquidity.toNat := Nat.le_of_not_lt hunder
      by_cases heq : t0 = t1
      · apply amm4ConstructorEqualTokensFor hdeploy hcode hwv hperm
        · intro a b l hargs'
          simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
          rcases hargs' with ⟨_, _, hl⟩
          simpa [hl] using hle
        · intro a b l hargs'
          simp only [List.cons.injEq, Value.address.injEq, Value.int.injEq] at hargs'
          rcases hargs' with ⟨ha, hb, _⟩
          simpa [← ha, ← hb] using heq
      · have hcodeCtor : I.code = amm4CtorCode t0 t1 (EVM.word liquidity.toNat) := by
          rw [hcode, hdeployed]
          simp [amm4CtorCode, amm4CtorArgTail, ByteArray.append_assoc]
        by_cases hdepth : I.depth.val < 1024
        · obtain ⟨createdAccounts', σ', z, ret, A', k, C,
            hrd, hcall, hretsz, hretbound⟩ :=
            amm4CtorFirstStaticcall
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              t0 t1 (EVM.word liquidity.toNat) hcodeCtor hwv hperm
              (by simpa [constructorUInt256Word_toNat liquidity h0 hlt] using hle)
              heq hdepth
          cases z with
          | false =>
            have hrdrev := amm4CtorFirstCallFailed hrd hretsz
              (by simp only [List.length_cons, List.length_nil]; omega)
            rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
            · exact constructorEquivalenceFor.outOfGas
                (by simpa [Sat256.ofUInt256] using hOOG)
            · obtain ⟨σ'_solm, hcallSolm, _⟩ :=
                amm4CtorFirstCallSourceTransport
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  hAccounts (by simpa [initState] using hcall)
              refine constructorEquivalenceFor.execution
                (by simpa [Sat256.ofUInt256] using hrev) ?_ (ctorResultEquiv.revert rfl rfl)
              exact amm4SolmCtorExecReverts_firstCallFailed
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                (σ₀ := σ₀) (g := g) (A := A) (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                heq hwv hAccounts hcallSolm
          | true =>
            obtain ⟨_, _, rd441⟩ := amm4CtorFirstCallSucceeded hrd
            obtain ⟨_, _, rd444⟩ := amm4CtorFirstCallFreePtr hretsz rd441
            obtain ⟨_, _, rd459⟩ := amm4CtorFirstCallReturnAlloc rd444
            obtain ⟨_, _, rd1617⟩ := amm4CtorFirstCallToDecoder rd459
            by_cases hshort : ret.size < 32
            · have hrdrev := amm4CtorFirstCallDecodeShortReverts hshort rd1617
              rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
              · exact constructorEquivalenceFor.outOfGas
                  (by simpa [Sat256.ofUInt256] using hOOG)
              · obtain ⟨σ'_solm, hcallSolm, _⟩ :=
                  amm4CtorFirstCallSourceTransport
                    (createdAccounts := createdAccounts)
                    (genesisBlockHeader := genesisBlockHeader)
                    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                    (σ₀ := σ₀) (g := g) (A := A) (I := I)
                    t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                    hAccounts (by simpa [initState] using hcall)
                refine constructorEquivalenceFor.execution
                  (by simpa [Sat256.ofUInt256] using hrev) ?_
                  (ctorResultEquiv.revert rfl rfl)
                exact amm4SolmCtorExecReverts_firstCallShort
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  heq hwv hAccounts hshort hcallSolm
            · have hlo : 32 ≤ ret.size := Nat.le_of_not_lt hshort
              obtain ⟨σS1, hcallS1, hAccounts1⟩ :=
                amm4CtorFirstCallSourceTransport
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (σ₀ := σ₀) (g := g) (A := A) (I := I)
                  t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                  hAccounts (by simpa [initState] using hcall)
              have hpostShape := amm4CtorFirstCallSourcePost_shape
                (createdAccounts := createdAccounts) (cA := createdAccounts')
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ := σ_solm) (σs := σS1)
                (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
              have hprefixRaw := amm4CtorSourceInitialBalance1Success
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
                (σ₀ := σ₀) (g := g) (A := A) (I := I)
                t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
                heq hwv hAccounts hlo hretbound hcallS1
              have hprefix : ExecBlock config
                  { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
                  (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                    (Sat256.ofUInt256 g) A I)
                  (amm4CtorSourceStoredPrefix ++
                    [tokenBalance (.storage token1Ref) "initialBalance1"])
                  (.ok { contract := contract, locals :=
                    amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret }
                    (initState createdAccounts' genesisBlockHeader blocks σS1 σ₀
                      (Sat256.ofUInt256 g) A' I)) := by
                simpa only [hpostShape] using hprefixRaw
              obtain ⟨_, _, rd1381⟩ :=
                amm4CtorFirstCallDecodeToWordLoad hlo hretbound rd1617
              obtain ⟨_, _, rd472⟩ :=
                amm4CtorFirstCallDecodeWord hlo hretsz rd1381
              obtain ⟨_, _, rd529⟩ := amm4CtorSecondCallTarget rd472
              obtain ⟨_, _, rd538⟩ := amm4CtorSecondCallFreePtrLoaded hretsz rd529
              obtain ⟨_, _, rd550⟩ := amm4CtorSecondCallSelectorStored rd538
              obtain ⟨_, _, rd562⟩ := amm4CtorSecondCallEncoded rd550
              obtain ⟨gasWord2, _, _, rd574⟩ :=
                amm4CtorSecondCallStaticcallFrame hlo hretbound rd562
              obtain ⟨createdAccounts2, σE2, z2, ret2, A2, k2, C2,
                rd575, hcall2, hretsz2, hretbound2⟩ :=
                amm4CtorSecondStaticcall (Apre := A') hlo hretbound hdepth rd574
              obtain ⟨σS2, hcallS2, hAccounts2⟩ :=
                amm4CtorSecondCallSourceTransport hAccounts1 hcall2
              cases z2 with
              | false =>
                have hrdrev := amm4CtorSecondCallFailed rd575 hretsz2
                  (by simp only [List.length_cons, List.length_nil]; omega)
                rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                · exact constructorEquivalenceFor.outOfGas
                    (by simpa [Sat256.ofUInt256] using hOOG)
                · refine constructorEquivalenceFor.execution
                    (by simpa [Sat256.ofUInt256] using hrev) ?_
                    (ctorResultEquiv.revert rfl rfl)
                  exact amm4SolmCtorExecReverts_secondCallFailed
                    (createdAccounts := createdAccounts) (cA := createdAccounts')
                    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
                    (σstart := σ_solm) (σ_evm := σ') (σ_solm := σS1)
                    (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                    t0 t1 liquidity hAccounts1 hprefix hcallS2
              | true =>
                obtain ⟨_, _, rd594⟩ := amm4CtorSecondCallSucceeded rd575
                obtain ⟨_, _, rd597⟩ :=
                  amm4CtorSecondReturnFreePtrLoaded hlo hretbound hretsz2 rd594
                obtain ⟨_, _, rd612⟩ :=
                  amm4CtorSecondCallReturnAlloc hlo hretbound rd597
                obtain ⟨_, _, rd1617_2⟩ := amm4CtorSecondCallToDecoder rd612
                by_cases hshort2 : ret2.size < 32
                · have hrdrev := amm4CtorSecondCallDecodeShortReverts
                    hretbound hshort2 rd1617_2
                  rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                  · exact constructorEquivalenceFor.outOfGas
                      (by simpa [Sat256.ofUInt256] using hOOG)
                  · refine constructorEquivalenceFor.execution
                      (by simpa [Sat256.ofUInt256] using hrev) ?_
                      (ctorResultEquiv.revert rfl rfl)
                    exact amm4SolmCtorExecReverts_secondCallShort
                      (createdAccounts := createdAccounts) (cA := createdAccounts')
                      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
                      (σstart := σ_solm) (σ_evm := σ') (σ_solm := σS1)
                      (σ₀ := σ₀) (g := g) (A := A) (A1 := A') (I := I)
                      t0 t1 liquidity hAccounts1 hshort2 hprefix hcallS2
                · have hlo2 : 32 ≤ ret2.size := Nat.le_of_not_lt hshort2
                  obtain ⟨_, _, rd625⟩ :=
                    amm4CtorSecondCallDecodeWord hlo hretbound hlo2 hretbound2
                      rd1617_2
                  have hprefix2 := amm4CtorSourceInitialBalance0Success
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
                  have haw2 : 3 ≤ (amm4CtorSecondCallArgWords ret).toNat := by
                    rw [amm4CtorSecondCallArgWords_toNat ret hlo hretbound]
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
                      amm4CtorInitialProductOk rd625 hfitProductWord
                    have hprefixProduct :=
                      amm4CtorSourceProductSuccess t0 t1 liquidity
                        hfitProduct hprefix2
                    by_cases hfitSquare : liquidity.toNat * liquidity.toNat < UInt256.size
                    · have hword := constructorUInt256Word_toNat liquidity h0 hlt
                      have hfitSquareWord :
                          (EVM.word liquidity.toNat).toNat *
                            (EVM.word liquidity.toNat).toNat < UInt256.size := by
                        simpa only [hword] using hfitSquare
                      obtain ⟨_, _, rd647⟩ :=
                        amm4CtorLiquiditySquareOk rd635 hfitSquareWord
                      have hprefixSquare :=
                        amm4CtorSourceSquareSuccess t0 t1 liquidity h0 hfitSquare
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
                          amm4CtorProductEqualityOk rd647 heqWord
                        obtain ⟨_, _, rd777⟩ :=
                          amm4CtorPositiveLiquidityOk rd711
                            (by rw [hword]; omega)
                        have hprefixGuards :=
                          amm4CtorSourceGuardsSuccess t0 t1 liquidity
                            heqProduct (by omega : 0 < liquidity) hprefixSquare
                        have hmem64 : 64 ≤
                            (amm4CtorSecondCallDecodeMem I t0 t1
                              (EVM.word liquidity.toNat) ret ret2).size := by
                          rw [amm4CtorSecondCallDecodeMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound (by
                              have hb := hretbound2
                              norm_num [UInt256.size] at *
                              omega)]
                          have hs := amm4CtorSecondCallArgMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret hretbound
                          have hp := (amm4CtorSecondCallFreePtr_bounds ret hretbound).1
                          omega
                        obtain ⟨_, _, rd784⟩ :=
                          amm4CtorPostGuardSupplyStored rd777 hperm
                        obtain ⟨_, _, rd852⟩ :=
                          amm4CtorPostGuardSelfBalanceStored rd784 hperm haw2 hmem64
                        obtain ⟨_, _, rd865⟩ :=
                          amm4CtorPostGuardBaseSupplyRecomputed rd852
                            (by rw [hword]; exact hle)
                        have hmem64' : 64 ≤
                            (twoWordHashMem (UInt256.ofNat I.codeOwner.val) ⟨1⟩
                              (amm4CtorSecondCallDecodeMem I t0 t1
                                (EVM.word liquidity.toNat) ret ret2)).size := by
                          rw [amm4CtorTwoWordHashMem_size _ _ _ hmem64]
                          exact hmem64
                        obtain ⟨_, _, rd931⟩ :=
                          amm4CtorPostGuardSenderBalanceStored rd865 hperm
                            haw2 hmem64'
                        have hprefixStorage :=
                          amm4CtorSourcePostGuardStorageSuccess
                            t0 t1 liquidity h0
                            (by simpa [UInt256.size] using hlt)
                            (by simp [initState]) (by simp [initState])
                            hprefixGuards
                        have hAccounts3 : accountMapEquiv
                            (amm4CtorPostGuardEvmMap I σE2 (EVM.word liquidity.toNat))
                            (amm4CtorPostGuardEvmMap I σS2 (EVM.word liquidity.toNat)) :=
                          amm4CtorPostGuardMaps_equiv I σE2 σS2
                            (EVM.word liquidity.toNat) hAccounts2
                        have hpostStorageShape := amm4CtorPostGuardSourceState_shape
                          (createdAccounts := createdAccounts2)
                          (genesisBlockHeader := genesisBlockHeader)
                          (blocks := blocks) (σ := σS2) (σ₀ := σ₀)
                          (g := g) (A := A2) (I := I) liquidity h0 hle
                          (by simpa [UInt256.size] using hlt)
                        obtain ⟨_, _, rd987⟩ := amm4CtorThirdCallTarget rd931
                        have hpost96 : 96 ≤
                            (amm4CtorPostGuardMem I t0 t1
                              (EVM.word liquidity.toNat) ret ret2).size := by
                          rw [amm4CtorPostGuardMem_baseSize I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound hretbound2]
                          rw [amm4CtorSecondCallDecodeMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound (by
                              have hb := hretbound2
                              norm_num [UInt256.size] at *
                              omega)]
                          have hs := amm4CtorSecondCallArgMem_size I t0 t1
                            (EVM.word liquidity.toNat) ret hretbound
                          have hp := (amm4CtorSecondCallFreePtr_bounds ret hretbound).1
                          omega
                        have hbelow64 :
                            ¬ (⟨64⟩ : UInt256) ≥
                              amm4CtorSecondCallArgWords ret * ⟨32⟩ := by
                          intro hh
                          have hfp64 : (⟨64⟩ : UInt256) ≤
                              amm4CtorSecondCallFreePtr ret := by
                            change 64 ≤ (amm4CtorSecondCallFreePtr ret).toNat
                            exact le_trans (by decide)
                              (amm4CtorSecondCallFreePtr_bounds ret hretbound).1
                          exact (amm4CtorSecondCallArgWords_ptr_haw ret hlo hretbound)
                            (le_trans hh hfp64)
                        have hload3 :
                            (if (⟨64⟩ : UInt256).toNat ≥
                                  (amm4CtorPostGuardMem I t0 t1
                                    (EVM.word liquidity.toNat) ret ret2).size ∨
                                (⟨64⟩ : UInt256) ≥
                                  amm4CtorSecondCallArgWords ret * ⟨32⟩
                             then ⟨0⟩
                             else UInt256.ofNat (fromByteArrayBigEndian
                               ((amm4CtorPostGuardMem I t0 t1
                                 (EVM.word liquidity.toNat) ret ret2).readWithPadding
                                 64 32))) =
                              amm4CtorAfterSecondReturnFreePtr ret ret2 := by
                          have hmem64 :
                              ¬ (⟨64⟩ : UInt256).toNat ≥
                                (amm4CtorPostGuardMem I t0 t1
                                  (EVM.word liquidity.toNat) ret ret2).size := by
                            change ¬ 64 ≥
                              (amm4CtorPostGuardMem I t0 t1
                                (EVM.word liquidity.toNat) ret ret2).size
                            omega
                          rw [if_neg (not_or.mpr ⟨hmem64, hbelow64⟩)]
                          rw [amm4CtorPostGuardMem_read64 I t0 t1
                            (EVM.word liquidity.toNat) ret ret2
                            hretbound hretbound2,
                            fromByteArrayBigEndian_toByteArray,
                            u256_ofNat_toNat]
                        obtain ⟨_, _, rd996⟩ :=
                          amm4CtorThirdCallFreePtrLoaded
                            (by simpa only [amm4CtorPostGuardMem,
                              amm4CtorPostGuardEvmMap] using rd987)
                            haw2 hload3
                        obtain ⟨_, _, rd1008⟩ :=
                          amm4CtorThirdCallSelectorStored rd996
                        obtain ⟨_, _, rd1020⟩ :=
                          amm4CtorThirdCallEncoded rd1008
                        obtain ⟨gasWord3, _, _, rd1032⟩ :=
                          amm4CtorThirdCallStaticcallFrame hlo hretbound
                            hlo2 hretbound2 rd1020
                        obtain ⟨createdAccounts3, σE3, z3, ret3, A3,
                          k3, C3, rd1033, hcall3, hretsz3, hretbound3⟩ :=
                          amm4CtorThirdStaticcall (Apre := A2)
                            hlo hretbound hlo2 hretbound2 hdepth rd1032
                        obtain ⟨σS3, hcallS3, hAccounts3'⟩ :=
                          amm4CtorSecondCallSourceTransport hAccounts3 hcall3
                        have hprefix3 : ExecBlock config
                            ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
                            (initState createdAccounts genesisBlockHeader blocks
                              σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            amm4CtorSourcePostGuardPrefix
                            (.ok ⟨contract,
                              amm4CtorAfterSquareLocals t0 t1 liquidity ret ret2⟩
                              (initState createdAccounts2 genesisBlockHeader blocks
                                (amm4CtorPostGuardEvmMap I σS2
                                  (EVM.word liquidity.toNat)) σ₀
                                (Sat256.ofUInt256 g) A2 I)) := by
                          rw [← hpostStorageShape]
                          simpa only [amm4CtorSourcePostGuardPrefix,
                            initState] using hprefixStorage
                        cases z3 with
                        | false =>
                          have hrdrev := amm4CtorThirdCallFailed rd1033 hretsz3
                            (by simp only [List.length_cons, List.length_nil]; omega)
                          rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                          · exact constructorEquivalenceFor.outOfGas
                              (by simpa [Sat256.ofUInt256] using hOOG)
                          · refine constructorEquivalenceFor.execution
                              (by simpa [Sat256.ofUInt256] using hrev) ?_
                              (ctorResultEquiv.revert rfl rfl)
                            exact amm4SolmCtorExecReverts_thirdCallFailed
                              t0 t1 liquidity hAccounts3 hprefix3 hcallS3
                        | true =>
                          obtain ⟨_, _, rd1052⟩ := amm4CtorThirdCallSucceeded rd1033
                          obtain ⟨_, _, rd1055⟩ :=
                            amm4CtorThirdReturnFreePtrLoaded hlo hretbound
                              hlo2 hretbound2 hretsz3 rd1052
                          obtain ⟨_, _, rd1070⟩ :=
                            amm4CtorThirdCallReturnAlloc hlo hretbound
                              hlo2 hretbound2 rd1055
                          obtain ⟨_, _, rd1617_3⟩ :=
                            amm4CtorThirdCallToDecoder rd1070
                          by_cases hshort3 : ret3.size < 32
                          · have hrdrev := amm4CtorThirdCallDecodeShortReverts
                              hretbound hretbound2 hshort3 rd1617_3
                            rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                            · exact constructorEquivalenceFor.outOfGas
                                (by simpa [Sat256.ofUInt256] using hOOG)
                            · refine constructorEquivalenceFor.execution
                                (by simpa [Sat256.ofUInt256] using hrev) ?_
                                (ctorResultEquiv.revert rfl rfl)
                              exact amm4SolmCtorExecReverts_thirdCallShort
                                t0 t1 liquidity hAccounts3 hshort3 hprefix3 hcallS3
                          · have hlo3 : 32 ≤ ret3.size := Nat.le_of_not_lt hshort3
                            obtain ⟨_, _, rd1083⟩ :=
                              amm4CtorThirdCallDecodeWord hlo hretbound
                                hlo2 hretbound2 hlo3 hretbound3 rd1617_3
                            obtain ⟨_, _, rd1090⟩ :=
                              amm4CtorReserve0Stored rd1083 hperm
                            have hprefixReserve0 :=
                              amm4CtorSourceReserveBalance0Success
                                t0 t1 liquidity hAccounts3 hlo3 hretbound3
                                hprefix3 hcallS3
                            have hprefixReserve0Store :=
                              amm4CtorSourceReserve0Stored t0 t1 liquidity
                                hlo3 hprefixReserve0
                            have hAccounts4 : accountMapEquiv
                                (amm4CtorReserve0Map I σE3
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret3.extract 0 32))))
                                (amm4CtorReserve0Map I σS3
                                  (UInt256.ofNat (fromByteArrayBigEndian
                                    (ret3.extract 0 32)))) :=
                              amm4CtorReserve0Maps_equiv I σE3 σS3 _ hAccounts3'
                            obtain ⟨_, _, rd1146⟩ := amm4CtorFourthCallTarget rd1090
                            have hmem4 : 96 ≤
                                (amm4CtorThirdCallDecodeMem I t0 t1
                                  (EVM.word liquidity.toNat) ret ret2 ret3).size := by
                              rw [amm4CtorThirdCallDecodeMem_size I t0 t1
                                (EVM.word liquidity.toNat) ret ret2 ret3
                                hretbound hretbound2 hretsz3]
                              have hs := amm4CtorThirdCallArgMem_size I t0 t1
                                (EVM.word liquidity.toNat) ret ret2
                                hretbound hretbound2
                              have hp := (amm4CtorAfterSecondReturnFreePtr_bounds
                                ret ret2 hretbound hretbound2).1
                              omega
                            have hload4 :
                                (if (⟨64⟩ : UInt256).toNat ≥
                                      (amm4CtorThirdCallDecodeMem I t0 t1
                                        (EVM.word liquidity.toNat) ret ret2 ret3).size ∨
                                    (⟨64⟩ : UInt256) ≥
                                      amm4CtorThirdCallArgWords ret ret2 * ⟨32⟩
                                 then ⟨0⟩
                                 else UInt256.ofNat (fromByteArrayBigEndian
                                   ((amm4CtorThirdCallDecodeMem I t0 t1
                                     (EVM.word liquidity.toNat) ret ret2 ret3).readWithPadding
                                     64 32))) =
                                  amm4CtorAfterThirdReturnFreePtr ret ret2 ret3 := by
                              have hmem64 : ¬ (⟨64⟩ : UInt256).toNat ≥
                                  (amm4CtorThirdCallDecodeMem I t0 t1
                                    (EVM.word liquidity.toNat) ret ret2 ret3).size := by
                                change ¬ 64 ≥ _
                                omega
                              have haw64 := amm4CtorThirdCallArgWords_mload64_haw
                                ret ret2 hlo hretbound hlo2 hretbound2
                              rw [if_neg (not_or.mpr ⟨hmem64, haw64⟩)]
                              rw [amm4CtorThirdCallDecodeMem_read64 I t0 t1
                                (EVM.word liquidity.toNat) ret ret2 ret3
                                hretbound hretbound2 hretsz3,
                                fromByteArrayBigEndian_toByteArray,
                                u256_ofNat_toNat]
                            obtain ⟨_, _, rd1155⟩ :=
                              amm4CtorFourthCallFreePtrLoaded rd1146
                                (by
                                  rw [amm4CtorThirdCallArgWords_toNat ret ret2
                                    hlo hretbound hlo2 hretbound2]
                                  omega)
                                hload4
                            obtain ⟨_, _, rd1167⟩ :=
                              amm4CtorFourthCallSelectorStored rd1155
                            obtain ⟨_, _, rd1179⟩ :=
                              amm4CtorFourthCallEncoded rd1167
                            obtain ⟨gasWord4, _, _, rd1191⟩ :=
                              amm4CtorFourthCallStaticcallFrame
                                hlo hretbound hlo2 hretbound2
                                hlo3 hretbound3 rd1179
                            obtain ⟨createdAccounts4, σE4, z4, ret4, A4,
                              k4, C4, rd1192, hcall4, hretsz4, hretbound4⟩ :=
                              amm4CtorFourthStaticcall (Apre := A3)
                                hlo hretbound hlo2 hretbound2
                                hlo3 hretbound3 hdepth rd1191
                            obtain ⟨σS4, hcallS4, hAccounts4'⟩ :=
                              amm4CtorFourthCallSourceTransport hAccounts4 hcall4
                            have hprefix4 : ExecBlock config
                                ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
                                (initState createdAccounts genesisBlockHeader blocks
                                  σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                amm4CtorSourceReserve0Prefix
                                (.ok ⟨contract,
                                  amm4CtorAfterReserveBalance0Locals
                                    t0 t1 liquidity ret ret2 ret3⟩
                                  (initState createdAccounts3 genesisBlockHeader blocks
                                    (amm4CtorReserve0Map I σS3
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret3.extract 0 32)))) σ₀
                                    (Sat256.ofUInt256 g) A3 I)) := by
                              rw [← amm4CtorAfterReserve0Store_shape]
                              simpa only [amm4CtorSourceReserve0Prefix,
                                initState] using hprefixReserve0Store
                            cases z4 with
                            | false =>
                              have hrdrev := amm4CtorFourthCallFailed rd1192 hretsz4
                                (by simp only [List.length_cons, List.length_nil]; omega)
                              rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                              · exact constructorEquivalenceFor.outOfGas
                                  (by simpa [Sat256.ofUInt256] using hOOG)
                              · refine constructorEquivalenceFor.execution
                                  (by simpa [Sat256.ofUInt256] using hrev) ?_
                                  (ctorResultEquiv.revert rfl rfl)
                                exact amm4SolmCtorExecReverts_fourthCallFailed
                                  t0 t1 liquidity hAccounts4 hprefix4 hcallS4
                            | true =>
                              obtain ⟨_, _, rd1211⟩ :=
                                amm4CtorFourthCallSucceeded rd1192
                              obtain ⟨_, _, rd1214⟩ :=
                                amm4CtorFourthReturnFreePtrLoaded
                                  hlo hretbound hlo2 hretbound2
                                  hlo3 hretbound3 hretsz4 rd1211
                              obtain ⟨_, _, rd1229⟩ :=
                                amm4CtorFourthCallReturnAlloc
                                  hlo hretbound hlo2 hretbound2
                                  hlo3 hretbound3 rd1214
                              obtain ⟨_, _, rd1617_4⟩ :=
                                amm4CtorFourthCallToDecoder rd1229
                              by_cases hshort4 : ret4.size < 32
                              · have hrdrev := amm4CtorFourthCallDecodeShortReverts
                                  hretbound hretbound2 hretbound3 hshort4
                                  rd1617_4
                                rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                                · exact constructorEquivalenceFor.outOfGas
                                    (by simpa [Sat256.ofUInt256] using hOOG)
                                · refine constructorEquivalenceFor.execution
                                    (by simpa [Sat256.ofUInt256] using hrev) ?_
                                    (ctorResultEquiv.revert rfl rfl)
                                  exact amm4SolmCtorExecReverts_fourthCallShort
                                    t0 t1 liquidity hAccounts4 hshort4
                                    hprefix4 hcallS4
                              · have hlo4 : 32 ≤ ret4.size := Nat.le_of_not_lt hshort4
                                obtain ⟨_, _, rd1242⟩ :=
                                  amm4CtorFourthCallDecodeWord
                                    hlo hretbound hlo2 hretbound2
                                    hlo3 hretbound3 hlo4 hretbound4
                                    rd1617_4
                                obtain ⟨_, _, rd1252⟩ :=
                                  amm4CtorReserve1Stored rd1242 hperm
                                have hprefixReserve1 :=
                                  amm4CtorSourceReserveBalance1Success
                                    t0 t1 liquidity hAccounts4 hlo4 hretbound4
                                    hprefix4 hcallS4
                                have hprefixReserve1Store :=
                                  amm4CtorSourceReserve1Stored t0 t1 liquidity
                                    hlo4 hprefixReserve1
                                have hAccountsFinal : accountMapEquiv
                                    (amm4CtorReserve1Map I σE4
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret4.extract 0 32))))
                                    (amm4CtorReserve1Map I σS4
                                      (UInt256.ofNat (fromByteArrayBigEndian
                                        (ret4.extract 0 32)))) :=
                                  amm4CtorReserve1Maps_equiv I σE4 σS4 _ hAccounts4'
                                have hret := amm4CtorReturnRuntime rd1252
                                have hprefixFinal : ExecBlock config
                                    ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
                                    (initState createdAccounts genesisBlockHeader
                                      blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    ((amm4CtorSourceReserve0Prefix ++
                                      [tokenBalance (.storage token1Ref)
                                        "reserveBalance1"]) ++
                                      [.assign .storage reserve1Ref
                                        (.var "reserveBalance1")])
                                    (.ok ⟨contract,
                                      amm4CtorAfterReserveBalance1Locals
                                        t0 t1 liquidity ret ret2 ret3 ret4⟩
                                      (initState createdAccounts4 genesisBlockHeader
                                        blocks (amm4CtorReserve1Map I σS4
                                          (UInt256.ofNat (fromByteArrayBigEndian
                                            (ret4.extract 0 32)))) σ₀
                                        (Sat256.ofUInt256 g) A4 I)) := by
                                  rw [← amm4CtorAfterReserve1Store_shape]
                                  simpa only [initState] using hprefixReserve1Store
                                have hsourceFinal :=
                                  amm4SolmCtorExecSuccess_afterReserves
                                    t0 t1 liquidity hprefixFinal
                                rcases hret with hOOG | ⟨s, hX, hacc⟩
                                · exact constructorEquivalenceFor.outOfGas
                                    (Xi_error_of_X (g := g) (by
                                      rw [← hcodeCtor] at hOOG
                                      simpa [initState, Sat256.ofUInt256] using hOOG))
                                · have hcA : s.createdAccounts = createdAccounts4 :=
                                    congrArg Prod.fst hacc
                                  have hσ : s.accountMap =
                                      amm4CtorReserve1Map I σE4
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
                        have hrdrev := amm4CtorProductEqualityMismatchReverts
                          rd647 hneWord
                        rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                        · exact constructorEquivalenceFor.outOfGas
                            (by simpa [Sat256.ofUInt256] using hOOG)
                        · refine constructorEquivalenceFor.execution
                            (by simpa [Sat256.ofUInt256] using hrev) ?_
                            (ctorResultEquiv.revert rfl rfl)
                          exact amm4SolmCtorExecReverts_productMismatch
                            t0 t1 liquidity heqProduct hprefixSquare
                    · have hoverSquare : UInt256.size ≤
                          (EVM.word liquidity.toNat).toNat *
                            (EVM.word liquidity.toNat).toNat := by
                        have hword := constructorUInt256Word_toNat liquidity h0 hlt
                        simpa only [hword] using Nat.le_of_not_lt hfitSquare
                      have hrdrev := amm4CtorLiquiditySquareOverflow rd635
                        hoverSquare haw2
                      rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                      · exact constructorEquivalenceFor.outOfGas
                          (by simpa [Sat256.ofUInt256] using hOOG)
                      · refine constructorEquivalenceFor.execution
                          (by simpa [Sat256.ofUInt256] using hrev) ?_
                          (ctorResultEquiv.revert rfl rfl)
                        exact amm4SolmCtorExecReverts_squareOverflow
                          t0 t1 liquidity h0 (Nat.le_of_not_lt hfitSquare)
                          hprefixProduct
                  · have hoverProduct : UInt256.size ≤
                        (UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))).toNat *
                          (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32))).toNat := by
                      simpa only [hv0, hv1] using Nat.le_of_not_lt hfitProduct
                    have hrdrev := amm4CtorInitialProductOverflow rd625
                      hoverProduct haw2
                    rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
                    · exact constructorEquivalenceFor.outOfGas
                        (by simpa [Sat256.ofUInt256] using hOOG)
                    · refine constructorEquivalenceFor.execution
                        (by simpa [Sat256.ofUInt256] using hrev) ?_
                        (ctorResultEquiv.revert rfl rfl)
                      exact amm4SolmCtorExecReverts_productOverflow
                        t0 t1 liquidity (Nat.le_of_not_lt hfitProduct) hprefix2
        · have hdepthEq : I.depth = (1024 : Fin 1025) := by
            apply Fin.ext
            have hbound := I.depth.isLt
            omega
          obtain ⟨_, _, _, rd421⟩ :=
            amm4CtorReachInitialToken1Staticcall
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              t0 t1 (EVM.word liquidity.toNat) hcodeCtor hwv hperm
              (by simpa [constructorUInt256Word_toNat liquidity h0 hlt] using hle)
              heq
          obtain ⟨_, _, rd422⟩ := RD.solcStaticcallDepthLimit rd421
            (by amm4_ctor_decode) hdepthEq
            (by simp only [List.length_cons, List.length_nil]; omega)
          have hrdrev := amm4CtorFirstCallFailed rd422
            (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
          rcases hrdrev.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
          · exact constructorEquivalenceFor.outOfGas
              (by simpa [Sat256.ofUInt256] using hOOG)
          · refine constructorEquivalenceFor.execution
              (by simpa [Sat256.ofUInt256] using hrev) ?_ (ctorResultEquiv.revert rfl rfl)
            exact amm4SolmCtorExecReverts_firstCallDepth
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
              (σ₀ := σ₀) (g := g) (A := A) (I := I)
              t0 t1 liquidity h0 hle (by simpa [UInt256.size] using hlt)
              heq hwv hAccounts hdepthEq
  · exact amm4ConstructorNonpayableFor hdeploy hcode hwv

theorem amm4ConstructorCorrect :
    constructorEquivalence config amm4CreationBytecode contract amm4Bytecode :=
  amm4ConstructorBodyCore

end Benchmarks.ActAmm4
