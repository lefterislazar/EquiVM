import Examples.Precompiles.Modexp.BarrettSpec
import Examples.Precompiles.Modexp.MultiLimbBarrettNormalizedComposition

/-!
# Arbitrary-width even-modulus Barrett specifications

These theorems connect the completed direct and normalized multi-limb selectors to the public
wide entry.  The witness records the actual reduction, constant, exponent, serializer, and restore
choices; its `gas` projection is the exact bytecode gas for that selected path.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

open Modexp.MultiLimbBarrettComposition
open Modexp.MultiLimbBarrettNormalizedComposition

set_option maxRecDepth 500000
set_option maxHeartbeats 0
set_option Elab.async false

def wideBarrettEntryPrefixGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
    wideBaseGtOneGas I baseSize + operandSetupGas I baseSize exponentSize modulusSize

/-- Exposed direct multi-limb execution selected from the public PC 62 wide entry. -/
structure WideBarrettDirectMultiWitness
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (sigma sigma0 : AccountMap) (A : Substate)
    (I : ExecutionEnv) (g : Sat256)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (initialGas baseSize exponentSize modulusSize : Nat) where
  selectedSteps : Nat
  selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
    ByteArray.empty acc
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (wideWordResultWords baseSize exponentSize modulusSize) selectedSteps
    (initialGas + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize +
      preparedBarrettPrefixGasFromAw I
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize)
    (operandModulusPtr baseSize exponentSize)
    (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
    operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
    (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
    (UInt256.ofNat 1271) (UInt256.ofNat 173) []
  exponentSelected :
    Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection
  execution : PreparedDirectExecution selected exponentSelected

def WideBarrettDirectMultiWitness.gas
    {cA gh bl sigma sigma0 A I g acc initialGas baseSize exponentSize modulusSize}
    (w : WideBarrettDirectMultiWitness cA gh bl sigma sigma0 A I g acc initialGas
      baseSize exponentSize modulusSize) : Nat :=
  w.execution.totalGas

/-- Exposed normalized multi-limb execution selected from the public PC 62 wide entry. -/
structure WideBarrettNormalizedMultiWitness
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (sigma sigma0 : AccountMap) (A : Substate)
    (I : ExecutionEnv) (g : Sat256)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (initialGas baseSize exponentSize modulusSize : Nat) where
  selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
    ByteArray.empty acc
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (wideWordResultWords baseSize exponentSize modulusSize)
    (initialGas + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize +
      preparedBarrettPrefixGasFromAw I
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize)
    (operandModulusPtr baseSize exponentSize) modulusSize
    (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
    (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
    operandBasePtr baseSize (operandExponentPtr baseSize) 1271
    (operandFreePtr baseSize exponentSize modulusSize) 173 []
  exponentSelected :
    Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection
  execution : PreparedNormalizedExecution selected exponentSelected

def WideBarrettNormalizedMultiWitness.gas
    {cA gh bl sigma sigma0 A I g acc initialGas baseSize exponentSize modulusSize}
    (w : WideBarrettNormalizedMultiWitness cA gh bl sigma sigma0 A I g acc initialGas
      baseSize exponentSize modulusSize) : Nat :=
  w.execution.totalGas

/-- The deployed leading-byte test selects normalization whenever the direct selector is false. -/
theorem wideBarrettNormalize_of_not_direct
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hmodPos : 0 < modulusSize)
    (hnotDirect : ¬ (modulusSize = 1 ∨
      UInt256.byteAt (UInt256.ofNat 0)
        (wideLoadWord
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠
            UInt256.ofNat 0)) :
    operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize := by
  let p := operandModulusPtr baseSize exponentSize
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  have hmNeOne : modulusSize ≠ 1 := fun hm => hnotDirect (Or.inl hm)
  have hmGtOne : 1 < modulusSize := by omega
  have hfirstZero :
      UInt256.byteAt (UInt256.ofNat 0)
        (wideLoadWord mem aw (UInt256.ofNat (p + 32))) = UInt256.ofNat 0 := by
    by_contra hne
    exact hnotDirect (Or.inr (by simpa only [mem, aw, p] using hne))
  have hstartLtEnd : barrettScanStart p < barrettScanEnd p modulusSize := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstartLtEnd' : p + 32 < barrettScanEnd p modulusSize := by
    simpa only [barrettScanStart] using hstartLtEnd
  have hbounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p modulusSize) (p + 32 + 1) (by
      unfold barrettScanEnd
      omega)
  change p + 32 < barrettScanStop mem aw p modulusSize
  unfold barrettScanStop barrettScanStart
  rw [barrettScanStopAt, dif_pos hstartLtEnd']
  rw [if_pos (by simpa only [barrettScanByteAt] using hfirstZero)]
  omega

/-- Repackage the constructive normalized-word re-entry facts for the public calldata lengths. -/
theorem wideBarrettNormalizedWordFacts_of_prepared
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hlenEq : lengths I.calldata =
      { base := baseSize, exponent := exponentSize, modulus := modulusSize })
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (facts : NormalizedWordReentryFacts I
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)) :
    WideBarrettNormalizedWordFacts I := by
  refine {
    hnorm := ?_
    hzero := ?_
    hone := ?_
    hfirst := ?_
  }
  · simpa only [hlenEq] using hnormalize
  · simpa only [hlenEq, wideBarrettNormalizedLenFor] using facts.zeroCheck
  · simpa only [hlenEq, wideBarrettNormalizedLenFor] using facts.oneCheck
  · simpa only [hlenEq, wideBarrettNormalizedLenFor] using facts.first

/-- Exposed branch selected by an exact arbitrary-width even-Barrett execution.  Multi-limb
constructors retain the complete generated-trace selection, including the exponent selector. -/
inductive WideBarrettSelection
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (bl : ProcessedBlocks) (sigma sigma0 : AccountMap) (A : Substate)
    (I : ExecutionEnv) (g : Sat256)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (initialGas baseSize exponentSize modulusSize : Nat) where
  | directWord
  | normalizedWord
  | directMulti
      (w : WideBarrettDirectMultiWitness cA gh bl sigma sigma0 A I g acc initialGas
        baseSize exponentSize modulusSize)
  | normalizedMulti
      (w : WideBarrettNormalizedMultiWitness cA gh bl sigma sigma0 A I g acc initialGas
        baseSize exponentSize modulusSize)

def WideBarrettSelection.gas
    {cA gh bl sigma sigma0 A I g acc initialGas baseSize exponentSize modulusSize}
    (selected : WideBarrettSelection cA gh bl sigma sigma0 A I g acc initialGas
      baseSize exponentSize modulusSize) : Nat :=
  match selected with
  | .directWord => initialGas + wideBarrettDirectWordGas I baseSize exponentSize modulusSize
  | .normalizedWord =>
      initialGas + wideBarrettNormalizedWordGas I baseSize exponentSize modulusSize
  | .directMulti w => w.gas
  | .normalizedMulti w => w.gas

/-- Direct arbitrary-width Barrett from the real wide entry. -/
theorem wideBarrettDirectMultiFromEntrySelectedExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {C steps baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hexp : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hfirst : UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠
          UInt256.ofNat 0)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc steps C) :
    ∃ w : WideBarrettDirectMultiWitness cA gh bl sigma sigma0 A I g acc C
        baseSize exponentSize modulusSize,
      RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
        (Model.natToBytes
          (Model.bytesToNatPadded I.calldata 96 baseSize ^
            Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
              Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
          modulusSize) w.gas := by
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm hcalldata (by simp)
    (by simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize) := by
    have h173 : (⟨173⟩ : UInt256) = UInt256.ofNat 173 := by native_decide
    simpa only [wideBarrettEntryPrefixGas, wideModulusOffset, wideExponentOffset,
      Nat.add_assoc, h173] using rd1183
  have hbasePos : 0 < baseSize := by
    by_contra hnot
    have hz : baseSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst baseSize
    simp only [model_bytesToNatPadded_zero_width] at hbase
    omega
  obtain ⟨selectedSteps, selected, exponentSelected, execution⟩ :=
    runPreparedBarrettDirectMultiLimbSelected
      (C := C + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize)
      (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
      (ret := 173) (tail := []) hb he hm hbasePos hmodLarge hmod hcalldata heven hfirst
      (by simp) rd1183'
  let w : WideBarrettDirectMultiWitness cA gh bl sigma sigma0 A I g acc C
      baseSize exponentSize modulusSize :=
    { selectedSteps := selectedSteps, selected := selected,
      exponentSelected := exponentSelected, execution := execution }
  refine ⟨w, ?_⟩
  simpa only [WideBarrettDirectMultiWitness.gas, w] using
    execution.returnExactSelected hb he hm hbasePos hmodLarge (by simp)

/-- Normalized arbitrary-width Barrett from the real wide entry. -/
theorem wideBarrettNormalizedMultiFromEntrySelectedExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {C steps baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hexp : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLarge : 32 < wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc steps C) :
    ∃ w : WideBarrettNormalizedMultiWitness cA gh bl sigma sigma0 A I g acc C
        baseSize exponentSize modulusSize,
      RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
        (Model.natToBytes
          (Model.bytesToNatPadded I.calldata 96 baseSize ^
            Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
              Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
          modulusSize) w.gas := by
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm hcalldata (by simp)
    (by simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize) := by
    have h173 : (⟨173⟩ : UInt256) = UInt256.ofNat 173 := by native_decide
    simpa only [wideBarrettEntryPrefixGas, wideModulusOffset, wideExponentOffset,
      Nat.add_assoc, h173] using rd1183
  have hbasePos : 0 < baseSize := by
    by_contra hnot
    have hz : baseSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst baseSize
    simp only [model_bytesToNatPadded_zero_width] at hbase
    omega
  obtain ⟨selected, exponentSelected, execution⟩ :=
    runPreparedBarrettNormalizedMultiLimbSelected
      (C := C + wideBarrettEntryPrefixGas I baseSize exponentSize modulusSize)
      (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
      (ret := 173) (tail := []) hb he hm hbasePos hmodLarge hmod hcalldata heven
      hnormalize hnLarge (by simp) rd1183'
  let w : WideBarrettNormalizedMultiWitness cA gh bl sigma sigma0 A I g acc C
      baseSize exponentSize modulusSize :=
    { selected := selected, exponentSelected := exponentSelected, execution := execution }
  refine ⟨w, ?_⟩
  simpa only [WideBarrettNormalizedMultiWitness.gas, w] using
    execution.returnExactSelected hb he hm hbasePos hmodLarge hnormalize hcalldata (by simp)

/-- Every nontrivial bounded even-modulus input at the real wide entry follows one of the four
actual Barrett paths.  The returned selector is public and its `gas` projection is the exact gas
of that selected bytecode execution, not an unconstrained existential. -/
theorem wideBarrettFromEntrySelectedExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {C steps baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hlenEq : lengths I.calldata =
      { base := baseSize, exponent := exponentSize, modulus := modulusSize })
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc steps C) :
    ∃ selected : WideBarrettSelection cA gh bl sigma sigma0 A I g acc C
        baseSize exponentSize modulusSize,
      RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
        (Model.natToBytes
          (Model.bytesToNatPadded I.calldata 96 baseSize ^
            Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize %
              Model.bytesToNatPadded I.calldata
                (wideModulusOffset baseSize exponentSize) modulusSize)
          modulusSize) selected.gas := by
  have hmodPos : 0 < modulusSize := by
    by_contra hnot
    have hz : modulusSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst modulusSize
    simp only [model_bytesToNatPadded_zero_width] at hmod
    omega
  let firstNonzero :=
    UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠
          UInt256.ofNat 0
  by_cases hdirect : modulusSize = 1 ∨ firstNonzero
  · by_cases hmWord : modulusSize ≤ 32
    · refine ⟨.directWord, ?_⟩
      have hret := wideBarrettDirectWordFromEntryModelExact
        (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
        hb he hmodPos hmWord hexp hbase hmod hcalldata heven
        (by simpa only [firstNonzero] using hdirect) rd0
      rw [model_modPow_eq_pow_mod (base := Model.bytesToNatPadded I.calldata 96 baseSize)
        (exponent := Model.bytesToNatPadded I.calldata
          (wideExponentOffset baseSize) exponentSize)
        (modulus := Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize) (by omega)] at hret
      simpa only [WideBarrettSelection.gas] using hret
    · have hmodLarge : 32 < modulusSize := by omega
      have hfirst : firstNonzero := by
        rcases hdirect with hmOne | hfirst
        · omega
        · exact hfirst
      obtain ⟨w, hret⟩ := wideBarrettDirectMultiFromEntrySelectedExact
        (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
        hb he hm hmodLarge
        (by simpa only [wideExponentOffset] using hexp) hbase
        (by simpa only [wideModulusOffset] using hmod) hcalldata heven
        (by simpa only [firstNonzero] using hfirst) rd0
      refine ⟨.directMulti w, ?_⟩
      simpa only [WideBarrettSelection.gas, wideExponentOffset, wideModulusOffset] using hret
  · have hnormalize := wideBarrettNormalize_of_not_direct I hmodPos
      (by simpa only [firstNonzero] using hdirect)
    by_cases hnLe32 :
        wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤ 32
    · have reentry := preparedNormalizedWordReentryFactsAny I hb he hm hnormalize hnLe32
        (by simpa only [wideModulusOffset] using hmod) hcalldata
      have hfacts := wideBarrettNormalizedWordFacts_of_prepared I hlenEq hnormalize reentry
      refine ⟨.normalizedWord, ?_⟩
      have hret := wideBarrettNormalizedWordFromEntryModelExact
        (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
        hb he hmodPos hm hnLe32 hexp hbase hmod hcalldata heven hfacts hlenEq rd0
      rw [model_modPow_eq_pow_mod (base := Model.bytesToNatPadded I.calldata 96 baseSize)
        (exponent := Model.bytesToNatPadded I.calldata
          (wideExponentOffset baseSize) exponentSize)
        (modulus := Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize) (by omega)] at hret
      simpa only [WideBarrettSelection.gas] using hret
    · have hnLarge : 32 <
          wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize := by omega
      have hnLeMod :
          wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤ modulusSize := by
        have hsplit := barrettNormalizedSkippedPrefix_add_len
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize hmodPos
        dsimp only [wideBarrettNormalizedLenFor]
        omega
      have hmodLarge : 32 < modulusSize := lt_of_lt_of_le hnLarge hnLeMod
      obtain ⟨w, hret⟩ := wideBarrettNormalizedMultiFromEntrySelectedExact
        (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
        hb he hm hmodLarge
        (by simpa only [wideExponentOffset] using hexp) hbase
        (by simpa only [wideModulusOffset] using hmod) hcalldata heven hnormalize hnLarge rd0
      refine ⟨.normalizedMulti w, ?_⟩
      simpa only [WideBarrettSelection.gas, wideExponentOffset, wideModulusOffset] using hret

/-- Public nontrivial even-Barrett condition after the standard parser/dispatcher checks. -/
def wideBarrettNontrivialEvenCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  1 < Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus ∧
  modulusLastByteParity
    (operandCopiedMemory I l.base l.exponent l.modulus)
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus = UInt256.ofNat 0

/-- Caller-visible arbitrary-width even-Barrett theorem.  Parsing and dispatch start at PC 0,
the four-way selector remains exposed, output is the unchanged pure model, and gas is exactly the
selector projection. -/
theorem wideBarrettSelectedModelExactGas
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = UInt256.ofNat 0)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideBarrettNontrivialEvenCondition I) :
    let l := lengths I.calldata
    ∃ selected : WideBarrettSelection cA gh bl sigma sigma0 A I g (cA, sigma)
        (wideEntryGas I.calldata) l.base l.exponent l.modulus,
      RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) (cA, sigma)
        (Model.output I.calldata) selected.gas := by
  let l := lengths I.calldata
  dsimp only [wideBarrettNontrivialEvenCondition] at hcond
  rcases hcond with ⟨hexp, hbase, hmod, heven⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨entrySteps, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := sigma) (σ₀ := sigma0) (A := A) (g := g)
    hcode hvalue hvalid hwide
  obtain ⟨selected, hret⟩ := wideBarrettFromEntrySelectedExact
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (cA, sigma)) hb he hm hexp hbase hmod hcalldata heven (by rfl) rd62
  refine ⟨selected, ?_⟩
  have hout := model_output_of_lengths I.calldata
    (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
    (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
    (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
  have hmod' : 1 < Model.bytesToNatPadded I.calldata
      (96 + l.base + l.exponent) l.modulus := by
    simpa only [wideModulusOffset] using hmod
  rw [model_modPow_eq_pow_mod
    (base := Model.bytesToNatPadded I.calldata 96 l.base)
    (exponent := Model.bytesToNatPadded I.calldata (96 + l.base) l.exponent)
    (modulus := Model.bytesToNatPadded I.calldata
      (96 + l.base + l.exponent) l.modulus) hmod'] at hout
  rw [hout]
  simpa only [wideExponentOffset, wideModulusOffset] using hret

end Modexp
