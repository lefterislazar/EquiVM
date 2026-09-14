import Benchmarks.Dss.End.CreationBlocks_001
import Reasoning.Constructor
import Reasoning.SolmBody
import Reasoning.Storage
import Reasoning.SummaryPatterns

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.End

theorem endCreation_runtime_window :
    endCreationBytecode.extract 94 (94 + 10265) = endBytecode := by
  native_decide

example {tail mem : ByteArray} {ee : ExecutionEnv} :
    ((endCreationBytecode ++ tail).write (UInt256.ofNat 94).toNat
        ((UInt256.ofNat 0).toByteArray.write 0
          ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 0).toNat (UInt256.ofNat 10265).toNat).readWithPadding
      (UInt256.ofNat 0).toNat (UInt256.ofNat 10265).toNat = endBytecode := by
  rw [show (UInt256.ofNat 94).toNat = 94 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 10265).toNat = 10265 by decide]
  rw [write0_read_back_from_gen (endCreationBytecode ++ tail)
    ((UInt256.ofNat 0).toByteArray.write 0
      ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem 0 32) 32 32)
    94 10265 (by decide) (by
      rw [ByteArray.size_append]
      have hsize : endCreationBytecode.size = 10359 := by native_decide
      rw [hsize]
      omega) (by decide)]
  rw [extract_append_left endCreationBytecode tail 94 (94 + 10265) (by
    native_decide)]
  exact endCreation_runtime_window

theorem endCreation_return_data_eq {tail mem : ByteArray} {ee : ExecutionEnv} :
    ((endCreationBytecode ++ tail).write (UInt256.ofNat 94).toNat
        ((UInt256.ofNat 0).toByteArray.write 0
          ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 0).toNat (UInt256.ofNat 10265).toNat).readWithPadding
      (UInt256.ofNat 0).toNat (UInt256.ofNat 10265).toNat = endBytecode := by
  rw [show (UInt256.ofNat 94).toNat = 94 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 10265).toNat = 10265 by decide]
  rw [write0_read_back_from_gen (endCreationBytecode ++ tail)
    ((UInt256.ofNat 0).toByteArray.write 0
      ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem 0 32) 32 32)
    94 10265 (by decide) (by
      rw [ByteArray.size_append]
      have hsize : endCreationBytecode.size = 10359 := by native_decide
      rw [hsize]
      omega) (by decide)]
  rw [extract_append_left endCreationBytecode tail 94 (94 + 10265) (by
    native_decide)]
  exact endCreation_runtime_window

theorem endCtorWardsSlot_eq (mem : ByteArray) (source : AccountAddress) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 0).toByteArray.write 0
          ((UInt256.ofNat source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = wardsSlot (.address source) := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat source.val) (UInt256.ofNat 0) mem) =
    wardsSlot (.address source)
  rw [twoWordHashMem_keccak_solcMappingSlot_ofNat]
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
  simp [solcMappingSlot, wardsSlot, mapSlot, keyValueToWord_address]

theorem endConstructorSolmBodyExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
      (∅ : Store) contract.ctor.body
      (.returned { contract := contract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner (wardsSlot (.address I.source)) (UInt256.ofNat 1))
          I.codeOwner (UInt256.ofNat 8) (UInt256.ofNat 1))
        none) := by
  let evm0 :=
    initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
  let solm0 : Frame := { contract := contract, locals := ∅ }
  let evm1 :=
    Solm.EVM.storageStore evm0 I.codeOwner (wardsSlot (.address I.source)) (UInt256.ofNat 1)
  let evm2 := Solm.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 8) (UInt256.ofNat 1)
  change ExecFuncBody config solm0 evm0 contract.ctor.body (.returned solm0 evm2 none)
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config solm0 evm0
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .assign .storage (wardsRef sender) (.intLit 1),
      .assign .storage liveRef (.intLit 1) ] (.ok solm0 evm2)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (evm := evm0) (by simp [evm0, initState, hwv])
  refine ExecBlock.consNormal (solm' := solm0) (evm' := evm1)
    (ExecStmt.assign (value := .int 1) (solm' := solm0) (evm' := evm1) ?_ ?_) ?_
  · simp [evalExpr?, pure]
  · refine assignStorageRef_storage_scalar
      (slot := wardsRef sender)
      (er := { base := "wards", steps := [.mindex (.address I.source)] })
      (ty := uint256St)
      (loc := wordLoc (wardsSlot (.address I.source))) ?_ ?_ ?_ ?_ ?_
    · simp [solm0, wardsRef]
    · simp [evalStorageRef, evalStorageRefStep, evalExpr?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, wardsRef, sender, envValue, valueToKey?, evm0, initState]
    · simp [solm0, contract, storageDecls, storageTypeAt?, storageTypeStep?, uint256St]
    · rfl
    · have hs := storageLocStore_uint256 evm0 (wardsSlot (.address I.source)) (UInt256.ofNat 1)
      simpa [wordLoc, uint256Loc, evm0, initState,
        show (UInt256.ofNat 1).toNat = 1 by decide] using hs
  refine ExecBlock.consNormal (solm' := solm0) (evm' := evm2)
    (ExecStmt.assign (value := .int 1) (solm' := solm0) (evm' := evm2) ?_ ?_) ?_
  · simp [evalExpr?, pure]
  · refine assignStorageRef_storage_scalar
      (slot := liveRef)
      (er := { base := "live", steps := [] })
      (ty := uint256St)
      (loc := wordLoc (UInt256.ofNat 8)) ?_ ?_ ?_ ?_ ?_
    · simp [solm0, liveRef]
    · simp [evalStorageRef, EvalResult.bind, bind, pure, liveRef]
    · simp [solm0, contract, storageDecls, storageTypeAt?, uint256St]
    · funext st
      change storageLayoutRaw { base := "live", steps := [] } st =
        some (wordLoc (UInt256.ofNat 8))
      rw [show UInt256.ofNat 8 = (⟨8⟩ : UInt256) by native_decide]
      rfl
    · have hs := storageLocStore_uint256 evm1 (UInt256.ofNat 8) (UInt256.ofNat 1)
      simpa [wordLoc, uint256Loc, evm1, evm0, initState, storageStore_executionEnv,
        show (UInt256.ofNat 1).toNat = 1 by decide] using hs
  exact ExecBlock.nil

theorem endConstructorSolmExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment endCreationBytecode args = some deployedInitcode)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract args createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := ∅ }
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            I.codeOwner (wardsSlot (.address I.source)) (UInt256.ofNat 1))
          I.codeOwner (UInt256.ofNat 8) (UInt256.ofNat 1))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := (∅ : Store)) ?_ ?_ ?_ ?_
  · rfl
  · exact emptyCtorDeployment_args_length
      (cfg := config) (contract := contract) (args := args)
      (initcode := endCreationBytecode) (deployedInitcode := deployedInitcode)
      (by rfl) (by rfl) hdeploy
  · simp [contract, constructorDecl]
  · exact endConstructorSolmBodyExecSuccess hwv

theorem endConstructorSolmExecRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment endCreationBytecode args = some deployedInitcode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract args createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := (∅ : Store)) ?_ ?_ ?_ ?_
  · rfl
  · exact emptyCtorDeployment_args_length
      (cfg := config) (contract := contract) (args := args)
      (initcode := endCreationBytecode) (deployedInitcode := deployedInitcode)
      (by rfl) (by rfl) hdeploy
  · simp [contract, constructorDecl]
  · rw [show contract.ctor.body =
        .require (.binary .eq (.env .callvalue) (.intLit 0)) ::
          [ .assign .storage (wardsRef sender) (.intLit 1),
            .assign .storage liveRef (.intLit 1) ] by
        rfl]
    exact bodyReverts_nonPayable (evm :=
      initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
      (by simpa [initState] using hwv)

theorem endCreationRunSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : Sat256}
    {A : Substate}
    {I : ExecutionEnv}
    (hcode : I.code = endCreationBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) :
    RDret endCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        storageWrite I.codeOwner
          (storageWrite I.codeOwner σ (wardsSlot (.address I.source)) (UInt256.ofNat 1))
          (UInt256.ofNat 8) (UInt256.ofNat 1))
      endBytecode := by
  have hcode' : I.code = endCreationBytecode ++ ByteArray.empty := by
    simpa [ByteArray.append_empty] using hcode
  have rd0 := RD.initState
    (code := endCreationBytecode ++ ByteArray.empty)
    (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode'
  obtain ⟨aw16, k16, C16, rd16⟩ :=
    endCreationBlocks.endCreation_block_0_taken_packed
      (tail := ByteArray.empty) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ByteArray.empty) (aw := UInt256.ofNat 0) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := σ) (k := 0) (C := 0) (R := [])
      (by decide) (by rw [hwv]; decide) (by native_decide) rd0
  have rd16' : RD (endCreationBytecode ++ ByteArray.empty) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (UInt256.ofNat 16) [I.weiValue]
      (endCreationBlocks.endCreation_block_0_taken_memory (mem := ByteArray.empty))
      aw16 ByteArray.empty (createdAccounts, σ) k16 C16 := by
    simpa [endCreationBlocks.endCreation_block_0_taken_stack] using rd16
  have rdret := endCreationBlocks.endCreation_block_16
    (tail := ByteArray.empty) (ee := I) (g := g)
    (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    (mem := endCreationBlocks.endCreation_block_0_taken_memory (mem := ByteArray.empty))
    (aw := aw16) (rdata := ByteArray.empty)
    (cA := createdAccounts) (σ := σ) (k := k16) (C := C16)
    (x0 := I.weiValue) (R := [])
    (by decide) hperm rd16'
  rw [endCreation_return_data_eq
    (tail := ByteArray.empty)
    (mem := endCreationBlocks.endCreation_block_0_taken_memory (mem := ByteArray.empty))
    (ee := I)] at rdret
  rw [endCtorWardsSlot_eq
    (endCreationBlocks.endCreation_block_0_taken_memory (mem := ByteArray.empty)) I.source] at rdret
  simpa [ByteArray.append_empty] using rdret

theorem endCreationRunRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : Sat256}
    {A : Substate}
    {I : ExecutionEnv}
    (hcode : I.code = endCreationBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev endCreationBytecode g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have hcode' : I.code = endCreationBytecode ++ ByteArray.empty := by
    simpa [ByteArray.append_empty] using hcode
  have rd0 := RD.initState
    (code := endCreationBytecode ++ ByteArray.empty)
    (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode'
  obtain ⟨aw12, k12, C12, rd12⟩ :=
    endCreationBlocks.endCreation_block_0_fallthrough_packed
      (tail := ByteArray.empty) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ByteArray.empty) (aw := UInt256.ofNat 0) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := σ) (k := 0) (C := 0) (R := [])
      (by decide) (isZero_eq_zero_of_ne hwv) rd0
  have rd12' : RD (endCreationBytecode ++ ByteArray.empty) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (UInt256.ofNat 12) [I.weiValue]
      (endCreationBlocks.endCreation_block_0_fallthrough_memory (mem := ByteArray.empty))
      aw12 ByteArray.empty (createdAccounts, σ) k12 C12 := by
    simpa [endCreationBlocks.endCreation_block_0_fallthrough_stack] using rd12
  have rdrev := endCreationBlocks.endCreation_block_12
    (tail := ByteArray.empty) (ee := I) (g := g)
    (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    (mem := endCreationBlocks.endCreation_block_0_fallthrough_memory (mem := ByteArray.empty))
    (aw := aw12) (rdata := ByteArray.empty)
    (cA := createdAccounts) (σ := σ) (k := k12) (C := C12)
    (R := [I.weiValue]) (by simp) rd12'
  simpa [ByteArray.append_empty] using rdrev

-- LIBRARY CANDIDATE: generalize `RDret.xiResult` to account-map-changing traces.
theorem RDret.xiResultAcc {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) acc o) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem endConstructorCorrectScratch :
    constructorEquivalence config endCreationBytecode contract endBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hσ
  have hdeployed := emptyCtorDeployment_eq_initcode
    (cfg := config) (contract := contract) (args := args)
    (initcode := endCreationBytecode) (deployedInitcode := deployedInitcode)
    (by rfl) (by rfl) hdeploy
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := endCreationRunSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
      (A := A) (I := I) hcode hwv hperm
    rcases RDret.xiResultAcc hcode hrd with hoog | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · refine constructorEquivalenceFor.execution hsuccess
        (endConstructorSolmExecSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g)
          (A := A) (I := I) (args := args) (deployedInitcode := deployedInitcode)
          hdeploy hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [storageStore_createdAccounts, initState]
      · simp [storageStore_accountMap, storageWrite_eq, initState]
        exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
          (wardsSlot (.address I.source)) (UInt256.ofNat 1)
          (UInt256.ofNat 8) (UInt256.ofNat 1) hσ
  · have hrd := endCreationRunRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
      (A := A) (I := I) hcode hwv
    rcases hrd.xiResult hcode with hoog | ⟨g', o, hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · refine constructorEquivalenceFor.execution hsuccess
        (endConstructorSolmExecRevert
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g)
          (A := A) (I := I) (args := args) (deployedInitcode := deployedInitcode)
          hdeploy hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.End
