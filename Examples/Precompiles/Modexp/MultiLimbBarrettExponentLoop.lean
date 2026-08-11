import Examples.Precompiles.Modexp.MultiLimbBarrettExponentSemantic
import Examples.Precompiles.Modexp.MultiLimbExponentModel

/-!
# Executable Barrett exponent bit loop

The selectors in this file retain the concrete correction selected by every `_barrettMulMod`
call.  Consequently `steps` and `gas` are transparent, path-sensitive totals over the same
computations used by the exact reduction and arithmetic theorems.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettExponentLoop

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettExponentSemantic
open Modexp.MultiLimbBarrettExponentTrace
open Modexp.MultiLimbBarrettReusedCall
open Modexp.MultiLimbExponentModel
open Modexp.MultiLimbExponentTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- One selected PC 6446 reduction, dynamic return, and PC 3406 copy-back. -/
structure BarrettExponentCallSelection where
  correction : BarrettCorrectionSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectBarrettExponentCall (fuel : Nat) (mem : ByteArray) (aw a b n mu target : UInt256)
    (fp kWords : Nat) : Option BarrettExponentCallSelection :=
  match Modexp.MultiLimbBarrettReusedCall.selectCall fuel mem aw a b n mu fp kWords with
  | none => none
  | some correction =>
      let resultFp := barrettCallResultFp fp kWords
      some {
        correction := correction
        memory := exponentCopyMemory correction.memory (UInt256.ofNat resultFp) target
          (UInt256.ofNat kWords)
        activeWords := exponentCopyAw correction.activeWords (UInt256.ofNat resultFp) target
          (UInt256.ofNat kWords)
        steps := Modexp.MultiLimbBarrettReusedCall.callSteps
          mem aw a b n mu fp kWords correction + 17
        gas := Modexp.MultiLimbBarrettReusedCall.callGas
          mem aw a b n mu fp kWords correction + 8 +
          exponentCopyGas correction.activeWords (UInt256.ofNat resultFp) target
            (UInt256.ofNat kWords) }

/-- A bounded complete Barrett call always produces an exponent-loop copy-back selection. -/
theorem selectBarrettExponentCall_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu target : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected,
      selectBarrettExponentCall fuel mem aw a b n mu target fp kWords = some selected := by
  rcases Modexp.MultiLimbBarrettReusedCall.selectCall_exists
    (mem := mem) (aw := aw) (a := a) (b := b) (n := n)
    (mu := mu) (fp := fp) hkPos hfuel with ⟨correction, hcorrection⟩
  simp [selectBarrettExponentCall, hcorrection]

/-- The first exponent operation starts before the scratch payload has been materialized.  It uses
the complete fresh-allocation selector; later operations use `selectBarrettExponentCall`. -/
def selectFreshBarrettExponentCall (fuel : Nat) (mem : ByteArray)
    (aw a b n mu target : UInt256) (fp kWords : Nat) :
    Option BarrettExponentCallSelection :=
  match Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall
      fuel mem aw a b n mu fp kWords with
  | none => none
  | some correction =>
      let resultFp := barrettCallResultFp fp kWords
      some {
        correction := correction
        memory := exponentCopyMemory correction.memory (UInt256.ofNat resultFp) target
          (UInt256.ofNat kWords)
        activeWords := exponentCopyAw correction.activeWords (UInt256.ofNat resultFp) target
          (UInt256.ofNat kWords)
        steps := Modexp.MultiLimbBarrettExponentTrace.barrettReductionSteps
          mem aw a b n mu fp kWords correction + 17
        gas := Modexp.MultiLimbBarrettExponentTrace.barrettReductionGas
          mem aw a b n mu fp kWords correction + 8 +
          exponentCopyGas correction.activeWords (UInt256.ofNat resultFp) target
            (UInt256.ofNat kWords) }

theorem selectFreshBarrettExponentCall_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu target : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected,
      selectFreshBarrettExponentCall fuel mem aw a b n mu target fp kWords =
        some selected := by
  rcases Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall_exists
    (mem := mem) (aw := aw) (a := a) (b := b) (n := n)
    (mu := mu) (fp := fp) hkPos hfuel with ⟨correction, hcorrection⟩
  simp [selectFreshBarrettExponentCall, hcorrection]

/-- Compact geometry for the one call whose scratch range is still represented by implicit EVM
zero padding. -/
structure FreshScratchInvariant
    (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray)
    (aw a b n mu : UInt256) (fp kWords : Nat)
    (selected : BarrettCorrectionSelection) : Prop where
  wordsPos : 0 < kWords
  words : kWords ≤ 32
  scratchBound : scratchEnd fp kWords < 2 ^ 64
  calldataBound : I.calldata.size < 2 ^ 64
  freePointerBase : 96 ≤ fp
  covered : MemoryCovered mem aw
  activeWordsFit : aw.toNat * 32 < UInt256.size
  memorySize : 96 ≤ mem.size
  memoryBeforeScratch : mem.size ≤ fp
  memoryGap : fp - mem.size < USize.size
  freePointerRead : mem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat fp)
  aBase : 96 ≤ a.toNat
  bBase : 96 ≤ b.toNat
  nBase : 96 ≤ n.toNat
  muBase : 96 ≤ mu.toNat
  aBeforeScratch : a.toNat + 32 * (kWords + 1) ≤ fp
  bBeforeScratch : b.toNat + 32 * (kWords + 1) ≤ fp
  nBeforeScratch : n.toNat + 32 * (kWords + 2) ≤ fp
  muBeforeScratch : mu.toNat + 32 * (kWords + 3) ≤ fp
  muHeader : mem.readWithPadding mu.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  selection : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall
    fuel mem aw a b n mu fp kWords = some selected

/-- Exact first-call execution from the compact fresh-scratch invariant. -/
theorem validFreshBarrettExponentCallExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu target : UInt256}
    {selected : BarrettExponentCallSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {resumePc : UInt256}
    (fresh : FreshScratchInvariant I fuel mem aw a b n mu fp kWords
      selected.correction)
    (hselect : selectFreshBarrettExponentCall fuel mem aw a b n mu target fp kWords =
      some selected)
    (hdepth : tail.length + 20 ≤ 1016)
    (hresume : (D_J runtimeBytecode 0).contains resumePc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: ⟨3406⟩ ::
        target :: UInt256.ofNat kWords :: resumePc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) resumePc tail
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  unfold selectFreshBarrettExponentCall at hselect
  cases hs : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall
      fuel mem aw a b n mu fp kWords with
  | none => simp [hs] at hselect
  | some correction =>
      simp only [hs, Option.some.injEq] at hselect
      subst selected
      have hfpScratch : fp ≤ scratchEnd fp kWords := by
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
        have hn64 : n.toNat + 32 * (kWords + 2) < 2 ^ 64 :=
          lt_of_le_of_lt (fresh.nBeforeScratch.trans hfpScratch) fresh.scratchBound
        exact lt_trans hn64 (by norm_num [UInt256.size])
      have haw3 : 3 ≤ aw.toNat := by
        have hcovered := fresh.covered
        have hmemSize := fresh.memorySize
        unfold MemoryCovered at hcovered
        omega
      have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
          umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) fresh.activeWordsFit
      have haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
        intro hge
        have hnat : (aw * ⟨32⟩).toNat ≤ 64 := hge
        rw [hmul] at hnat
        omega
      have hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
        apply lt_of_le_of_lt _ fresh.scratchBound
        unfold scratchEnd callResultFp
        omega
      have hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
          wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
        apply lt_of_le_of_lt _ fresh.scratchBound
        unfold scratchEnd callResultFp
        omega
      have hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
          wordArrayAllocationSize (kWords + 2) +
          wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
        apply lt_of_le_of_lt _ fresh.scratchBound
        unfold scratchEnd callResultFp
        omega
      have hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
          wordArrayAllocationSize (kWords + 2) +
          wordArrayAllocationSize (2 * kWords + 4) +
          wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
        apply lt_of_le_of_lt _ fresh.scratchBound
        unfold scratchEnd callResultFp
        omega
      have hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
          wordArrayAllocationSize (kWords + 2) +
          wordArrayAllocationSize (2 * kWords + 4) +
          wordArrayAllocationSize (kWords + 3) +
          wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
        apply lt_of_le_of_lt _ fresh.scratchBound
        unfold scratchEnd callResultFp
        omega
      have hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
          wordArrayAllocationSize (kWords + 2) +
          wordArrayAllocationSize (2 * kWords + 4) +
          wordArrayAllocationSize (kWords + 3) +
          wordArrayAllocationSize (kWords + 1) +
          wordArrayAllocationSize kWords < 2 ^ 64 := by
        simpa only [scratchEnd, callResultFp] using fresh.scratchBound
      have rd := Modexp.MultiLimbBarrettExponentTrace.selectedBarrettCallAndCopyExact
        (tail := tail) correction fresh.wordsPos fresh.words fresh.covered
        fresh.activeWordsFit fresh.memorySize fresh.memoryBeforeScratch fresh.memoryGap
        haw3 haw64
        fresh.freePointerRead fresh.aBeforeScratch fresh.bBeforeScratch fresh.muBase
        fresh.muBeforeScratch fresh.muHeader
        hfirstBound hq1Bound hsecondBound hq3Bound hr2Bound hresultBound hnFit
        fresh.calldataBound hdepth hresume fresh.selection h
      simpa only [barrettCallResultFp, Nat.add_assoc] using rd

/-- The first fresh-scratch call computes the same remainder as the pure Barrett model. -/
theorem FreshScratchInvariant.selectedResultValue
    {I : ExecutionEnv} {fuel fp kWords aValue bValue nValue x : Nat}
    {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    (fresh : FreshScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (haValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue)
    (hbValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue)
    (hxValue : aValue * bValue = x)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (barrettCallResultFp fp kWords + 32) kWords) =
      x % nValue := by
  have hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64 := by
    simpa only [scratchEnd, callResultFp] using fresh.scratchBound
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hn64 : n.toNat + 32 * (kWords + 2) < 2 ^ 64 :=
      lt_of_le_of_lt (fresh.nBeforeScratch.trans hfpScratch) fresh.scratchBound
    exact lt_trans hn64 (by norm_num [UInt256.size])
  have hsemantic :=
    Modexp.MultiLimbBarrettReduction.selectedBarrettFromFirstProduct_resultValue_eq_mod
      fresh.wordsPos fresh.words fresh.covered fresh.activeWordsFit fresh.memorySize
      fresh.memoryBeforeScratch fresh.memoryGap hfirstBound hq1Bound hsecondBound hq3Bound
      hr2Bound hresultBound
      (by have ha := fresh.aBase; omega) (by have hb := fresh.bBase; omega)
      (by have hn := fresh.nBase; omega) (by have hmu := fresh.muBase; omega)
      fresh.aBeforeScratch fresh.bBeforeScratch
      (by have hn := fresh.nBeforeScratch; omega) fresh.muBeforeScratch hnFit
      haValue hbValue hnValue hmuValue hxValue hnNormalized hx
      (by
        simpa only [Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall] using
          fresh.selection)
  simpa only [barrettCallResultFp, Nat.add_assoc] using hsemantic

/-- The selected fresh reduction establishes the materialized scratch geometry required by every
later reused call, before the caller copies the result back into its accumulator. -/
theorem FreshScratchInvariant.selectedStateGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (fresh : FreshScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.size = scratchEnd fp kWords ∧
      ∀ ptr words, 96 ≤ ptr → ptr + 32 * words ≤ fp →
        memoryWordsFrom selected.memory ptr words = memoryWordsFrom mem ptr words := by
  have hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64 := by
    simpa only [scratchEnd, callResultFp] using fresh.scratchBound
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hn64 : n.toNat + 32 * (kWords + 2) < 2 ^ 64 :=
      lt_of_le_of_lt (fresh.nBeforeScratch.trans hfpScratch) fresh.scratchBound
    exact lt_trans hn64 (by norm_num [UInt256.size])
  have hgeometry :=
    Modexp.MultiLimbBarrettReduction.selectedBarrettFromFirstProduct_stateGeometry
      fresh.wordsPos fresh.words fresh.covered fresh.activeWordsFit fresh.memorySize
      fresh.memoryBeforeScratch fresh.memoryGap hfirstBound hq1Bound hsecondBound hq3Bound
      hr2Bound hresultBound fresh.aBeforeScratch fresh.bBeforeScratch fresh.nBeforeScratch
      fresh.muBeforeScratch hnFit
      (by simpa only [Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall] using
        fresh.selection)
  refine ⟨hgeometry.1, hgeometry.2.1, ?_, hgeometry.2.2.2⟩
  simpa only [scratchEnd, callResultFp] using hgeometry.2.2.1

/-- Copying a fresh reduction result into a persistent accumulator preserves the new scratch
extent and every complete persistent range ending at the accumulator payload. -/
theorem FreshScratchInvariant.copyStateGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu target : UInt256} {selected : BarrettCorrectionSelection}
    (fresh : FreshScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (htargetBase : 96 ≤ target.toNat)
    (htargetBefore : target.toNat + 32 * (kWords + 1) ≤ fp) :
    let copiedMemory := exponentCopyMemory selected.memory
      (UInt256.ofNat (barrettCallResultFp fp kWords)) target (UInt256.ofNat kWords)
    let copiedWords := exponentCopyAw selected.activeWords
      (UInt256.ofNat (barrettCallResultFp fp kWords)) target (UInt256.ofNat kWords)
    MemoryCovered copiedMemory copiedWords ∧
      copiedWords.toNat * 32 < UInt256.size ∧
      copiedMemory.size = scratchEnd fp kWords ∧
      ∀ ptr words, 96 ≤ ptr → ptr + 32 * words ≤ target.toNat + 32 →
        memoryWordsFrom copiedMemory ptr words = memoryWordsFrom mem ptr words := by
  let resultFp := barrettCallResultFp fp kWords
  let source := UInt256.ofNat resultFp + ⟨32⟩
  let destination := target + ⟨32⟩
  let bytes := UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩
  have hstate := fresh.selectedStateGeometry
  have hresultFp64 : resultFp < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource64 : resultFp + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsourceNat : source.toNat = resultFp + 32 := by
    dsimp only [source]
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (hresultFp64.trans (by decide)),
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (hsource64.trans (by decide))]
  have htarget64 : target.toNat + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    omega
  have hdestinationNat : destination.toNat = target.toNat + 32 := by
    dsimp only [destination]
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (htarget64.trans (by decide))]
  have hbytesNat : bytes.toNat = 32 * kWords := by
    dsimp only [bytes]
    exact ushl5_ofNat_toNat kWords
      (lt_of_le_of_lt fresh.words (by native_decide : 32 < 2 ^ 251))
  have hfpScratch : fp ≤ scratchEnd fp kWords := by
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htargetStartFp : target.toNat + 32 ≤ fp := by omega
  have htargetEndFp : target.toNat + 32 + 32 * kWords ≤ fp := by omega
  have hsourceEnd : source.toNat + bytes.toNat ≤ selected.memory.size := by
    rw [hsourceNat, hbytesNat, hstate.2.2.1]
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htargetEnd : destination.toNat + bytes.toNat ≤ selected.memory.size := by
    rw [hdestinationNat, hbytesNat, hstate.2.2.1]
    exact htargetEndFp.trans hfpScratch
  have hsourceEndScratch : source.toNat + bytes.toNat = scratchEnd fp kWords := by
    rw [hsourceNat, hbytesNat]
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htargetEndScratch : destination.toNat + bytes.toNat ≤ scratchEnd fp kWords := by
    rw [hdestinationNat, hbytesNat]
    exact htargetEndFp.trans hfpScratch
  have hmaxEnd : max destination.toNat source.toNat + bytes.toNat ≤
      scratchEnd fp kWords := by
    by_cases hle : destination.toNat ≤ source.toNat
    · rw [max_eq_right hle]
      exact hsourceEndScratch.le
    · rw [max_eq_left (by omega)]
      exact htargetEndScratch
  have haccessFit : max destination.toNat source.toNat + bytes.toNat + 31 <
      UInt256.size := by
    exact lt_of_le_of_lt (Nat.add_le_add_right hmaxEnd 31)
      (lt_trans (Nat.add_lt_add_right fresh.scratchBound 31)
        (by norm_num [UInt256.size]))
  have hcopyCoverage := finalCopy_coverage selected.memory selected.activeWords source destination
    bytes (by rw [hbytesNat]; exact Nat.mul_ne_zero (by decide) (Nat.ne_of_gt fresh.wordsPos))
    hsourceEnd htargetEnd hstate.1 hstate.2.1 haccessFit
  have hcopySize := finalCopyMemory_size selected.memory source destination bytes
    (by rw [hbytesNat]; exact Nat.mul_ne_zero (by decide) (Nat.ne_of_gt fresh.wordsPos))
    hsourceEnd htargetEnd
  dsimp only
  refine ⟨by simpa only [exponentCopyMemory, exponentCopyAw, source, destination, bytes]
      using hcopyCoverage.1,
    by simpa only [exponentCopyAw, source, destination, bytes] using hcopyCoverage.2, ?_, ?_⟩
  · rw [show exponentCopyMemory selected.memory (UInt256.ofNat resultFp) target
        (UInt256.ofNat kWords) = finalCopyMemory selected.memory source destination bytes by rfl,
      hcopySize, hstate.2.2.1]
  · intro ptr words hptrBase hbelow
    have hread : ptr + 32 * words ≤ selected.memory.size := by
      rw [hstate.2.2.1]
      exact hbelow.trans (htargetStartFp.trans hfpScratch)
    have hdestinationMem : destination.toNat ≤ selected.memory.size := by
      rw [hdestinationNat, hstate.2.2.1]
      exact htargetStartFp.trans hfpScratch
    have hcopyFrame := memoryWordsFrom_finalCopy_below words selected.memory source destination
      bytes ptr
      (by rw [hbytesNat]; exact Nat.mul_ne_zero (by decide) (Nat.ne_of_gt fresh.wordsPos))
      hsourceEnd
      hdestinationMem hread (by
        rw [hdestinationNat]
        exact hbelow)
    have hpersistent := hstate.2.2.2 ptr words hptrBase (hbelow.trans htargetStartFp)
    calc
      memoryWordsFrom
          (exponentCopyMemory selected.memory (UInt256.ofNat resultFp) target
            (UInt256.ofNat kWords)) ptr words =
        memoryWordsFrom selected.memory ptr words := by
          simpa only [exponentCopyMemory, source, destination, bytes] using hcopyFrame
      _ = memoryWordsFrom mem ptr words := hpersistent

/-- The same copy-back places the pure fresh-reduction remainder in the accumulator payload. -/
theorem FreshScratchInvariant.copiedResultValue
    {I : ExecutionEnv} {fuel fp kWords aValue bValue nValue x : Nat}
    {mem : ByteArray} {aw a b n mu target : UInt256}
    {selected : BarrettCorrectionSelection}
    (fresh : FreshScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (haValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue)
    (hbValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue)
    (hxValue : aValue * bValue = x)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords))
    (htarget : (target + ⟨32⟩).toNat ≤ selected.memory.size) :
    barrettAccumulatorValue kWords target
        (exponentCopyMemory selected.memory
          (UInt256.ofNat (barrettCallResultFp fp kWords)) target (UInt256.ofNat kWords)) =
      x % nValue := by
  have hvalue := fresh.selectedResultValue haValue hbValue hnValue hmuValue hxValue hnPos
    hnNormalized hnFits hx
  let resultFp := barrettCallResultFp fp kWords
  have hresultFp64 : resultFp < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource64 : resultFp + 32 < 2 ^ 64 := by
    apply lt_of_le_of_lt _ fresh.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsourceNat : (UInt256.ofNat resultFp + ⟨32⟩).toNat = resultFp + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (hresultFp64.trans (by decide)),
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (hsource64.trans (by decide))]
  have hbytes : (UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩).toNat = 32 * kWords :=
    ushl5_ofNat_toNat kWords (by have hk := fresh.words; omega)
  have hsource : (UInt256.ofNat resultFp + ⟨32⟩).toNat + 32 * kWords ≤
      selected.memory.size := by
    rw [hsourceNat, fresh.selectedStateGeometry.2.2.1]
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopy := finalCopyMemory_words_eq_source kWords selected.memory
    (UInt256.ofNat resultFp + ⟨32⟩) (target + ⟨32⟩)
    (UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩)
    fresh.wordsPos hbytes hsource htarget
  unfold barrettAccumulatorValue exponentCopyMemory
  rw [hcopy, hsourceNat]
  simpa only [resultFp] using hvalue

/-- A decoded EVM memory word determines its canonical 32-byte representation. -/
theorem readWithPadding_eq_toByteArray_of_memoryWordNat_eq
    (mem : ByteArray) (ptr : Nat) (word : UInt256)
    (hword : UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) = word) :
    mem.readWithPadding ptr 32 = word.toByteArray := by
  have hsize : (mem.readWithPadding ptr 32).size = 32 := by
    have hread : (mem.readWithoutPadding ptr 32).size <= 32 := by
      unfold ByteArray.readWithoutPadding
      split
      · simp
      · rw [ByteArray.size_extract]
        omega
    unfold ByteArray.readWithPadding
    rw [if_neg (by norm_num)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  have hroundtrip : UInt256.toByteArray
      (UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr 32))) =
      mem.readWithPadding ptr 32 := by
    rw [← uInt256OfByteArray_eq]
    rw [← word_toBytesBE_toByteArray_eq_toByteArray
      (uInt256OfByteArray (mem.readWithPadding ptr 32))]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_data_toByteArray]
    simpa [byteArray_toList_eq] using
      toBytesBE_uInt256OfByteArray_of_size hsize
  rw [← hroundtrip]
  congr 1

/-- Exact-execution geometry for one already-prepared Barrett call. -/
structure BarrettExponentCallValid
    (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray) (aw a b n mu target : UInt256)
    (fp kWords : Nat) (selected : BarrettExponentCallSelection) : Prop where
  scratch : ScratchInvariant I fuel mem aw a b n mu fp kWords selected.correction
  selection : selectBarrettExponentCall fuel mem aw a b n mu target fp kWords = some selected

/-- One complete reused Barrett call, including its accumulator copy-back, preserves every
32-byte read below both the scratch frontier and the copy-back target. -/
theorem BarrettExponentCallValid.readBelow
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu target : UInt256} {selected : BarrettExponentCallSelection}
    (valid : BarrettExponentCallValid I fuel mem aw a b n mu target fp kWords selected)
    {read : Nat} (hread : 96 <= read) (hbelow : read + 32 <= target.toNat)
    (htarget : target.toNat + 32 <= fp) :
    selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hselection := valid.selection
  unfold selectBarrettExponentCall at hselection
  cases hcall : Modexp.MultiLimbBarrettReusedCall.selectCall
      fuel mem aw a b n mu fp kWords with
  | none => simp [hcall] at hselection
  | some correction =>
      simp only [hcall, Option.some.injEq] at hselection
      subst selected
      have hscratchConcrete := valid.scratch.selectedStateGeometry.2.2.1
      have hwords := valid.scratch.selectedStateGeometry.2.2.2 read 1 hread (by omega)
      have hnat := memoryWordNat_eq_of_memoryWordsFrom_one_eq
        correction.memory mem read hwords
      have hcorrection : correction.memory.readWithPadding read 32 =
          mem.readWithPadding read 32 := by
        have hleft := readWithPadding_eq_toByteArray_of_memoryWordNat_eq
          correction.memory read
          (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem read)) (by rw [hnat])
        have hright := readWithPadding_eq_toByteArray_of_memoryWordNat_eq
          mem read (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem read)) rfl
        exact hleft.trans hright.symm
      have hfp64 : fp < 2 ^ 64 := by
        apply lt_of_le_of_lt (b := scratchEnd fp kWords)
        · unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact valid.scratch.scratchBound
      have htargetWord : target.toNat + 32 < UInt256.size :=
        lt_trans (lt_of_le_of_lt htarget (by omega : fp < 2 ^ 64)) (by decide)
      have htargetAdd : (target + UInt256.ofNat 32).toNat = target.toNat + 32 := by
        rw [uadd_toNat, show (UInt256.ofNat 32).toNat = 32 by decide,
          Nat.mod_eq_of_lt htargetWord]
      have hresultFp64 : barrettCallResultFp fp kWords < 2 ^ 64 := by
        apply lt_of_le_of_lt (b := scratchEnd fp kWords)
        · unfold scratchEnd callResultFp barrettCallResultFp
          omega
        · exact valid.scratch.scratchBound
      have hsource64 : barrettCallResultFp fp kWords + 32 < UInt256.size :=
        lt_trans (by
          apply lt_of_le_of_lt (b := scratchEnd fp kWords)
          · unfold scratchEnd callResultFp barrettCallResultFp
              wordArrayAllocationSize wordArrayPayloadSize
            omega
          · exact valid.scratch.scratchBound) (by decide)
      have hsourceAdd : (UInt256.ofNat (barrettCallResultFp fp kWords) +
          UInt256.ofNat 32).toNat = barrettCallResultFp fp kWords + 32 := by
        rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (lt_trans hresultFp64 (by decide)),
          show (UInt256.ofNat 32).toNat = 32 by decide, Nat.mod_eq_of_lt hsource64]
      have hbytes : (UInt256.shiftLeft (UInt256.ofNat kWords) (UInt256.ofNat 5)).toNat =
          32 * kWords := ushl5_ofNat_toNat kWords (by
            have hk := valid.scratch.words
            omega)
      have hbytesPos : (UInt256.shiftLeft (UInt256.ofNat kWords)
          (UInt256.ofNat 5)).toNat ≠ 0 := by
        rw [hbytes]
        have hkPos := valid.scratch.wordsPos
        omega
      have hsource : (UInt256.ofNat (barrettCallResultFp fp kWords) +
          UInt256.ofNat 32).toNat +
          (UInt256.shiftLeft (UInt256.ofNat kWords) (UInt256.ofNat 5)).toNat <=
          correction.memory.size := by
        rw [hsourceAdd, hbytes]
        apply le_trans _ hscratchConcrete
        unfold scratchEnd callResultFp barrettCallResultFp
          wordArrayAllocationSize wordArrayPayloadSize
        omega
      have hdest : (target + UInt256.ofNat 32).toNat <= correction.memory.size := by
        rw [htargetAdd]
        apply le_trans htarget
        apply le_trans _ hscratchConcrete
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      have hreadInCorrection : read + 32 <= correction.memory.size := by
        apply le_trans (by omega : read + 32 <= fp)
        apply le_trans _ hscratchConcrete
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      unfold exponentCopyMemory finalCopyMemory
      exact (write_read_below_gen_from_extend correction.memory correction.memory
        (UInt256.ofNat (barrettCallResultFp fp kWords) + UInt256.ofNat 32).toNat
        (target + UInt256.ofNat 32).toNat
        (UInt256.shiftLeft (UInt256.ofNat kWords) (UInt256.ofNat 5)).toNat
        read 32 hbytesPos hsource hdest (by rw [htargetAdd]; omega)
        hreadInCorrection (by decide) (by decide)).trans hcorrection

/-- Execute one selected call with the exact correction-dependent cost retained in the record. -/
theorem validBarrettExponentCallExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu target : UInt256}
    {selected : BarrettExponentCallSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {resumePc : UInt256}
    (valid : BarrettExponentCallValid I fuel mem aw a b n mu target fp kWords selected)
    (hdepth : tail.length + 20 ≤ 1016)
    (hresume : (D_J runtimeBytecode 0).contains resumePc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: ⟨3406⟩ ::
        target :: UInt256.ofNat kWords :: resumePc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) resumePc tail
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have hselection := valid.selection
  unfold selectBarrettExponentCall at hselection
  cases hs : Modexp.MultiLimbBarrettReusedCall.selectCall
      fuel mem aw a b n mu fp kWords with
  | none => simp [hs] at hselection
  | some correction =>
      simp only [hs, Option.some.injEq] at hselection
      have hselected := hselection
      subst selected
      let resultFp := barrettCallResultFp fp kWords
      let callTail := target :: UInt256.ofNat kWords :: resumePc :: tail
      have rd6737 := validCallExactOfScratchInvariant (tail := callTail)
        valid.scratch (by
          dsimp only [callTail]
          simp only [List.length_cons]
          omega) (by simpa only [callTail] using h)
      have rd6737' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
          (⟨3406⟩ :: UInt256.ofNat resultFp :: callTail)
          correction.memory correction.activeWords rdata acc
          (steps + Modexp.MultiLimbBarrettReusedCall.callSteps
            mem aw a b n mu fp kWords correction)
          (gasUsed + Modexp.MultiLimbBarrettReusedCall.callGas
            mem aw a b n mu fp kWords correction) := by
        simpa only [resultFp, callTail, barrettCallResultFp,
          Modexp.MultiLimbBarrettReusedCall.callResultFp,
          Nat.add_assoc] using rd6737
      have rd3406 := barrettDynamicReturn (tail := callTail) (returnPc := ⟨3406⟩)
        (result := UInt256.ofNat resultFp)
        (by dsimp only [callTail]; simp only [List.length_cons]; omega)
        (by native_decide) rd6737'
      have rdResume := barrettCopyReturn (tail := tail)
        (resultBase := UInt256.ofNat resultFp) (r := target)
        (words := UInt256.ofNat kWords) (resumePc := resumePc)
        (by omega) hresume (by simpa only [callTail] using rd3406)
      simpa only [resultFp, Nat.add_assoc] using rdResume

/-- Persistent state carried between Barrett exponentiation calls.  The deployed layout places
the immutable base, modulus, and Barrett constant below the accumulator, followed by the reused
scratch extent. -/
structure BarrettExponentInvariant
    (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256) (kWords fp : Nat)
    (r a n mu : UInt256) (rValue baseValue nValue : Nat) : Prop where
  wordsPos : 0 < kWords
  words : kWords <= 32
  scratchBound : scratchEnd fp kWords < 2 ^ 64
  calldataBound : I.calldata.size < 2 ^ 64
  freePointerBase : 96 <= fp
  covered : MemoryCovered mem aw
  activeWordsFit : aw.toNat * 32 < UInt256.size
  scratchConcrete : scratchEnd fp kWords <= mem.size
  rBase : 96 <= r.toNat
  aBase : 96 <= a.toNat
  nBase : 96 <= n.toNat
  muBase : 96 <= mu.toNat
  aBeforeR : a.toNat + 32 * (kWords + 1) <= r.toNat
  nBeforeR : n.toNat + 32 * (kWords + 2) <= r.toNat
  muBeforeR : mu.toNat + 32 * (kWords + 3) <= r.toNat
  rBeforeScratch : r.toNat + 32 * (kWords + 1) <= fp
  rHeader : mem.readWithPadding r.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  aHeader : mem.readWithPadding a.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  nHeader : mem.readWithPadding n.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  muHeader : mem.readWithPadding mu.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  rValueEq : barrettAccumulatorValue kWords r mem = rValue
  baseValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (a.toNat + 32) kWords) = baseValue
  nValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue
  muValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
      UInt256.size ^ (2 * kWords) / nValue
  nPos : 0 < nValue
  nNormalized : UInt256.size ^ (kWords - 1) <= nValue
  nFits : nValue < UInt256.size ^ kWords

/-- State at the exponent-loop entry, before the first Barrett call has materialized its scratch
payload.  The arithmetic arrays are already persistent, but concrete memory ends no later than
the scratch base. -/
structure InitialBarrettExponentInvariant
    (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256) (kWords fp : Nat)
    (r a n mu : UInt256) (rValue baseValue nValue : Nat) : Prop where
  wordsPos : 0 < kWords
  words : kWords <= 32
  scratchBound : scratchEnd fp kWords < 2 ^ 64
  calldataBound : I.calldata.size < 2 ^ 64
  freePointerBase : 96 <= fp
  covered : MemoryCovered mem aw
  activeWordsFit : aw.toNat * 32 < UInt256.size
  memorySize : 96 <= mem.size
  memoryBeforeScratch : mem.size <= fp
  memoryGap : fp - mem.size < USize.size
  rBase : 96 <= r.toNat
  aBase : 96 <= a.toNat
  nBase : 96 <= n.toNat
  muBase : 96 <= mu.toNat
  aBeforeR : a.toNat + 32 * (kWords + 1) <= r.toNat
  nBeforeR : n.toNat + 32 * (kWords + 2) <= r.toNat
  muBeforeR : mu.toNat + 32 * (kWords + 3) <= r.toNat
  rBeforeScratch : r.toNat + 32 * (kWords + 1) <= fp
  rHeader : mem.readWithPadding r.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  aHeader : mem.readWithPadding a.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  nHeader : mem.readWithPadding n.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat kWords)
  muHeader : mem.readWithPadding mu.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  rValueEq : barrettAccumulatorValue kWords r mem = rValue
  baseValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (a.toNat + 32) kWords) = baseValue
  nValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue
  muValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
      UInt256.size ^ (2 * kWords) / nValue
  nPos : 0 < nValue
  nNormalized : UInt256.size ^ (kWords - 1) <= nValue
  nFits : nValue < UInt256.size ^ kWords

/-- A read-only word load can only enlarge the active-word counter; it preserves the persistent
Barrett arrays and their numeric interpretation. -/
theorem BarrettExponentInvariant.afterReadWords1
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu ptr : UInt256}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hptrFit : ptr.toNat + 32 + 31 < UInt256.size) :
    BarrettExponentInvariant I mem (readWords1 aw ptr)
      kWords fp r a n mu rValue baseValue nValue := by
  have hread := machineM_coverage mem aw ptr.toNat 32 invariant.covered
    invariant.activeWordsFit hptrFit
  exact {
    invariant with
    covered := by simpa [readWords1] using hread.1
    activeWordsFit := by simpa [readWords1] using hread.2 }

/-- Loading the dynamic-array length is the first read in every exponent scan. -/
theorem BarrettExponentInvariant.afterExponentArrayLengthLoad
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu exponent : UInt256}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size) :
    BarrettExponentInvariant I mem (exponentArrayLengthAw aw exponent)
      kWords fp r a n mu rValue baseValue nValue := by
  simpa [exponentArrayLengthAw, readWords1] using
    invariant.afterReadWords1 (ptr := exponent) hexponentFit

/-- Resetting Solidity's free-memory pointer preserves every padded persistent word range. -/
theorem memoryWordsFrom_barrettResetMemory_above
    (mem : ByteArray) (fp ptr words : Nat)
    (hmem : 96 <= mem.size) (hptr : 96 <= ptr) :
    memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp)) ptr words =
      memoryWordsFrom mem ptr words := by
  have hreset : barrettResetMemory mem (UInt256.ofNat fp) = setFreePtr mem fp := by
    simp [barrettResetMemory, setFreePtr]
  rw [hreset]
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      simp only [memoryWordsFrom]
      have hread := setFreePtr_read_above_padded (mem := mem) (fp := fp) (read := ptr)
        hmem hptr
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat (setFreePtr mem fp) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hread]]
      congr 1
      exact ih (ptr + 32) (by omega)

/-- Read-only exponent loads preserve the compact state used before the first reduction. -/
theorem InitialBarrettExponentInvariant.afterReadWords1
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu ptr : UInt256}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hptrFit : ptr.toNat + 32 + 31 < UInt256.size) :
    InitialBarrettExponentInvariant I mem (readWords1 aw ptr)
      kWords fp r a n mu rValue baseValue nValue := by
  have hread := machineM_coverage mem aw ptr.toNat 32 invariant.covered
    invariant.activeWordsFit hptrFit
  exact {
    invariant with
    covered := by simpa [readWords1] using hread.1
    activeWordsFit := by simpa [readWords1] using hread.2 }

theorem InitialBarrettExponentInvariant.afterExponentArrayLengthLoad
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu exponent : UInt256}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size) :
    InitialBarrettExponentInvariant I mem (exponentArrayLengthAw aw exponent)
      kWords fp r a n mu rValue baseValue nValue := by
  simpa [exponentArrayLengthAw, readWords1] using
    invariant.afterReadWords1 (ptr := exponent) hexponentFit

theorem InitialBarrettExponentInvariant.afterExponentByteLoad
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu exponent byteIdx : UInt256}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size) :
    InitialBarrettExponentInvariant I mem (exponentByteLoadAw aw exponent byteIdx)
      kWords fp r a n mu rValue baseValue nValue := by
  have hlength := machineM_coverage mem aw exponent.toNat 32 invariant.covered
    invariant.activeWordsFit hexponentFit
  have hbyte := machineM_coverage mem (exponentArrayLengthAw aw exponent)
    (exponentByteAddress exponent byteIdx).toNat 32 hlength.1 hlength.2 hbyteFit
  exact {
    invariant with
    covered := by
      simpa [exponentByteLoadAw, exponentArrayLengthAw] using hbyte.1
    activeWordsFit := by
      simpa [exponentByteLoadAw, exponentArrayLengthAw] using hbyte.2 }

/-- The first PC 3379 reset retains compact memory and prepares the fresh-allocation reduction. -/
theorem InitialBarrettExponentInvariant.resetFreshScratch
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu x y : UInt256}
    {selected : BarrettCorrectionSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hxBase : 96 <= x.toNat)
    (hyBase : 96 <= y.toNat)
    (hxBefore : x.toNat + 32 * (kWords + 1) <= fp)
    (hyBefore : y.toNat + 32 * (kWords + 1) <= fp)
    (hselect : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      x y n mu fp kWords = some selected) :
    FreshScratchInvariant I fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      x y n mu fp kWords selected := by
  have hresetSize :
      (barrettResetMemory mem (UInt256.ofNat fp)).size = mem.size := by
    simpa [barrettResetMemory, setFreePtr] using
      setFreePtr_size (mem := mem) (fp := fp) invariant.memorySize
  have hexpansion := machineM_coverage mem aw 64 32 invariant.covered
    invariant.activeWordsFit (by norm_num [UInt256.size])
  have hresetCovered : MemoryCovered
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw) := by
    unfold MemoryCovered at hexpansion ⊢
    rw [hresetSize]
    simpa [barrettResetAw] using hexpansion.1
  have hresetFit : (barrettResetAw aw).toNat * 32 < UInt256.size := by
    simpa [barrettResetAw] using hexpansion.2
  have hmuHeader' : (barrettResetMemory mem (UInt256.ofNat fp)).readWithPadding
      mu.toNat 32 = UInt256.toByteArray (UInt256.ofNat (kWords + 2)) := by
    have hread := setFreePtr_read_above_padded (mem := mem) (fp := fp)
      (read := mu.toNat) invariant.memorySize invariant.muBase
    simpa [barrettResetMemory, setFreePtr] using hread.trans invariant.muHeader
  have hrLe : r.toNat <= fp := by
    have hr := invariant.rBeforeScratch
    omega
  exact {
    wordsPos := invariant.wordsPos
    words := invariant.words
    scratchBound := invariant.scratchBound
    calldataBound := invariant.calldataBound
    freePointerBase := invariant.freePointerBase
    covered := hresetCovered
    activeWordsFit := hresetFit
    memorySize := by rw [hresetSize]; exact invariant.memorySize
    memoryBeforeScratch := by rw [hresetSize]; exact invariant.memoryBeforeScratch
    memoryGap := by rw [hresetSize]; exact invariant.memoryGap
    freePointerRead := by
      simpa [barrettResetMemory, setFreePtr] using
        setFreePtr_read64 (mem := mem) (fp := fp) invariant.memorySize
    aBase := hxBase
    bBase := hyBase
    nBase := invariant.nBase
    muBase := invariant.muBase
    aBeforeScratch := hxBefore
    bBeforeScratch := hyBefore
    nBeforeScratch := le_trans invariant.nBeforeR hrLe
    muBeforeScratch := le_trans invariant.muBeforeR hrLe
    muHeader := hmuHeader'
    selection := hselect }

/-- The concrete PC 3379/3448 reset rebuilds the compact scratch contract for the next call. -/
theorem BarrettExponentInvariant.resetScratch
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu x y : UInt256}
    {selected : BarrettCorrectionSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hxBase : 96 <= x.toNat)
    (hyBase : 96 <= y.toNat)
    (hxBefore : x.toNat + 32 * (kWords + 1) <= fp)
    (hyBefore : y.toNat + 32 * (kWords + 1) <= fp)
    (hselect : selectCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      x y n mu fp kWords = some selected) :
    ScratchInvariant I fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      x y n mu fp kWords selected := by
  have hmem96 : 96 <= mem.size := by
    exact invariant.freePointerBase.trans (le_trans (by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) invariant.scratchConcrete)
  have hresetSize :
      (barrettResetMemory mem (UInt256.ofNat fp)).size = mem.size := by
    simpa [barrettResetMemory, setFreePtr] using setFreePtr_size (mem := mem) (fp := fp) hmem96
  have hexpansion := machineM_coverage mem aw 64 32 invariant.covered
    invariant.activeWordsFit (by norm_num [UInt256.size])
  have hresetCovered : MemoryCovered
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw) := by
    unfold MemoryCovered at hexpansion ⊢
    rw [hresetSize]
    simpa [barrettResetAw] using hexpansion.1
  have hresetFit : (barrettResetAw aw).toNat * 32 < UInt256.size := by
    simpa [barrettResetAw] using hexpansion.2
  have hmuHeader' : (barrettResetMemory mem (UInt256.ofNat fp)).readWithPadding
      mu.toNat 32 = UInt256.toByteArray (UInt256.ofNat (kWords + 2)) := by
    have hread := setFreePtr_read_above_padded (mem := mem) (fp := fp)
      (read := mu.toNat) hmem96 invariant.muBase
    simpa [barrettResetMemory, setFreePtr] using hread.trans invariant.muHeader
  have hrLe : r.toNat <= fp := by
    have hr := invariant.rBeforeScratch
    omega
  exact {
    wordsPos := invariant.wordsPos
    words := invariant.words
    scratchBound := invariant.scratchBound
    calldataBound := invariant.calldataBound
    freePointerBase := invariant.freePointerBase
    covered := hresetCovered
    activeWordsFit := hresetFit
    scratchConcrete := by rw [hresetSize]; exact invariant.scratchConcrete
    freePointerRead := by
      simpa [barrettResetMemory, setFreePtr] using
        setFreePtr_read64 (mem := mem) (fp := fp) hmem96
    aBase := hxBase
    bBase := hyBase
    nBase := invariant.nBase
    muBase := invariant.muBase
    aBeforeScratch := hxBefore
    bBeforeScratch := hyBefore
    nBeforeScratch := le_trans invariant.nBeforeR hrLe
    muBeforeScratch := le_trans invariant.muBeforeR hrLe
    muHeader := hmuHeader'
    selection := hselect }

/-- Checked exponent MLOADs only change the active-word counter; all persistent arithmetic
facts remain unchanged. -/
theorem BarrettExponentInvariant.afterExponentByteLoad
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu exponent byteIdx : UInt256}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size) :
    BarrettExponentInvariant I mem (exponentByteLoadAw aw exponent byteIdx)
      kWords fp r a n mu rValue baseValue nValue := by
  have hlength := machineM_coverage mem aw exponent.toNat 32 invariant.covered
    invariant.activeWordsFit hexponentFit
  have hbyte := machineM_coverage mem (exponentArrayLengthAw aw exponent)
    (exponentByteAddress exponent byteIdx).toNat 32 hlength.1 hlength.2 hbyteFit
  exact {
    invariant with
    covered := by
      simpa [exponentByteLoadAw, exponentArrayLengthAw] using hbyte.1
    activeWordsFit := by
      simpa [exponentByteLoadAw, exponentArrayLengthAw] using hbyte.2 }

structure BarrettSquareSelection where
  call : BarrettExponentCallSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

/-- The first square has the same caller shape and cost record as later squares, but selects the
fresh-allocation reduction because its scratch payload does not yet exist. -/
def selectFreshBarrettSquare (fuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (r n mu : UInt256) : Option BarrettSquareSelection :=
  let resetMemory := barrettResetMemory mem (UInt256.ofNat fp)
  let resetAw := barrettResetAw aw
  match selectFreshBarrettExponentCall fuel resetMemory resetAw r r n mu r fp kWords with
  | none => none
  | some call => some {
      call := call
      memory := call.memory
      activeWords := call.activeWords
      steps := 20 + call.steps
      gas := barrettSquareEntryGas aw + call.gas }

def selectBarrettSquare (fuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (r n mu : UInt256) : Option BarrettSquareSelection :=
  let resetMemory := barrettResetMemory mem (UInt256.ofNat fp)
  let resetAw := barrettResetAw aw
  match selectBarrettExponentCall fuel resetMemory resetAw r r n mu r fp kWords with
  | none => none
  | some call => some {
      call := call
      memory := call.memory
      activeWords := call.activeWords
      steps := 20 + call.steps
      gas := barrettSquareEntryGas aw + call.gas }

structure BarrettMultiplySelection where
  call : BarrettExponentCallSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectBarrettMultiply (fuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (r a n mu : UInt256) : Option BarrettMultiplySelection :=
  let resetMemory := barrettResetMemory mem (UInt256.ofNat fp)
  let resetAw := barrettResetAw aw
  match selectBarrettExponentCall fuel resetMemory resetAw r a n mu r fp kWords with
  | none => none
  | some call => some {
      call := call
      memory := call.memory
      activeWords := call.activeWords
      steps := 12 + call.steps
      gas := barrettMultiplyEntryGas aw + call.gas }

/-- Resetting temporary memory does not change selector totality for a square call. -/
theorem selectBarrettSquare_exists
    {fuel kWords fp : Nat} {mem : ByteArray} {aw r n mu : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectBarrettSquare fuel mem aw kWords fp r n mu = some selected := by
  rcases selectBarrettExponentCall_exists
      (mem := barrettResetMemory mem (UInt256.ofNat fp)) (aw := barrettResetAw aw)
      (a := r) (b := r) (n := n) (mu := mu) (target := r) (fp := fp)
      hkPos hfuel with ⟨call, hcall⟩
  simp [selectBarrettSquare, hcall]

theorem selectFreshBarrettSquare_exists
    {fuel kWords fp : Nat} {mem : ByteArray} {aw r n mu : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords <= fuel) :
    exists selected, selectFreshBarrettSquare fuel mem aw kWords fp r n mu = some selected := by
  rcases selectFreshBarrettExponentCall_exists
      (mem := barrettResetMemory mem (UInt256.ofNat fp)) (aw := barrettResetAw aw)
      (a := r) (b := r) (n := n) (mu := mu) (target := r) (fp := fp)
      hkPos hfuel with ⟨call, hcall⟩
  simp [selectFreshBarrettSquare, hcall]

/-- Resetting temporary memory does not change selector totality for a multiply call. -/
theorem selectBarrettMultiply_exists
    {fuel kWords fp : Nat} {mem : ByteArray} {aw r a n mu : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectBarrettMultiply fuel mem aw kWords fp r a n mu = some selected := by
  rcases selectBarrettExponentCall_exists
      (mem := barrettResetMemory mem (UInt256.ofNat fp)) (aw := barrettResetAw aw)
      (a := r) (b := a) (n := n) (mu := mu) (target := r) (fp := fp)
      hkPos hfuel with ⟨call, hcall⟩
  simp [selectBarrettMultiply, hcall]

structure BarrettSquareValid (I : ExecutionEnv) (fuel : Nat)
    (mem : ByteArray) (aw : UInt256) (kWords fp : Nat) (r n mu : UInt256)
    (selected : BarrettSquareSelection) : Prop where
  selection : selectBarrettSquare fuel mem aw kWords fp r n mu = some selected
  call : BarrettExponentCallValid I fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r r n mu r fp kWords selected.call

structure BarrettMultiplyValid (I : ExecutionEnv) (fuel : Nat)
    (mem : ByteArray) (aw : UInt256) (kWords fp : Nat) (r a n mu : UInt256)
    (selected : BarrettMultiplySelection) : Prop where
  selection : selectBarrettMultiply fuel mem aw kWords fp r a n mu = some selected
  call : BarrettExponentCallValid I fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r a n mu r fp kWords selected.call

structure FreshBarrettSquareValid (I : ExecutionEnv) (fuel : Nat)
    (mem : ByteArray) (aw : UInt256) (kWords fp : Nat) (r n mu : UInt256)
    (selected : BarrettSquareSelection) : Prop where
  selection : selectFreshBarrettSquare fuel mem aw kWords fp r n mu = some selected
  scratch : FreshScratchInvariant I fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r r n mu fp kWords selected.call.correction
  callSelection : selectFreshBarrettExponentCall fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r r n mu r fp kWords = some selected.call

/-- A reused square preserves every persistent 32-byte word strictly below the accumulator. -/
theorem BarrettExponentInvariant.readBelowSquare
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettSquareValid I fuel mem aw kWords fp r n mu selected)
    {read : Nat} (hread : 96 <= read) (hbelow : read + 32 <= r.toNat) :
    selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  have htarget : r.toNat + 32 <= fp := by
    have hr := invariant.rBeforeScratch
    omega
  have hmem : 96 <= mem.size := by
    apply le_trans invariant.freePointerBase
    apply le_trans _ invariant.scratchConcrete
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hselection := valid.selection
  unfold selectBarrettSquare at hselection
  cases hcall : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hcall] at hselection
  | some call =>
      simp only [hcall, Option.some.injEq] at hselection
      subst selected
      have hcallFrame := valid.call.readBelow hread hbelow htarget
      have hreset := setFreePtr_read_above_padded (mem := mem) (fp := fp)
        (read := read) hmem hread
      exact hcallFrame.trans (by
        simpa only [barrettResetMemory, setFreePtr] using hreset)

/-- A reused multiply preserves every persistent 32-byte word strictly below the accumulator. -/
theorem BarrettExponentInvariant.readBelowMultiply
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettMultiplySelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected)
    {read : Nat} (hread : 96 <= read) (hbelow : read + 32 <= r.toNat) :
    selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  have htarget : r.toNat + 32 <= fp := by
    have hr := invariant.rBeforeScratch
    omega
  have hmem : 96 <= mem.size := by
    apply le_trans invariant.freePointerBase
    apply le_trans _ invariant.scratchConcrete
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hselection := valid.selection
  unfold selectBarrettMultiply at hselection
  cases hcall : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r a n mu r fp kWords with
  | none => simp [hcall] at hselection
  | some call =>
      simp only [hcall, Option.some.injEq] at hselection
      subst selected
      have hcallFrame := valid.call.readBelow hread hbelow htarget
      have hreset := setFreePtr_read_above_padded (mem := mem) (fp := fp)
        (read := read) hmem hread
      exact hcallFrame.trans (by
        simpa only [barrettResetMemory, setFreePtr] using hreset)

/-- The first fresh square has the same persistent frame as later reused calls. -/
theorem InitialBarrettExponentInvariant.readBelowFreshSquare
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : FreshBarrettSquareValid I fuel mem aw kWords fp r n mu selected)
    {read : Nat} (hread : 96 <= read) (hbelow : read + 32 <= r.toNat) :
    selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hselection := valid.selection
  unfold selectFreshBarrettSquare at hselection
  cases hcall : selectFreshBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hcall] at hselection
  | some call =>
      simp only [hcall, Option.some.injEq] at hselection
      subst selected
      unfold selectFreshBarrettExponentCall at hcall
      cases hraw : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => simp [hraw] at hcall
      | some correction =>
          simp only [hraw, Option.some.injEq] at hcall
          subst call
          have hcopy := valid.scratch.copyStateGeometry invariant.rBase
            invariant.rBeforeScratch
          have hwords := hcopy.2.2.2 read 1 hread (by omega)
          have hnat := memoryWordNat_eq_of_memoryWordsFrom_one_eq
            (exponentCopyMemory correction.memory
              (UInt256.ofNat (barrettCallResultFp fp kWords)) r (UInt256.ofNat kWords))
            (barrettResetMemory mem (UInt256.ofNat fp)) read hwords
          have hcopyRead :
              (exponentCopyMemory correction.memory
                (UInt256.ofNat (barrettCallResultFp fp kWords)) r
                (UInt256.ofNat kWords)).readWithPadding read 32 =
              (barrettResetMemory mem (UInt256.ofNat fp)).readWithPadding read 32 := by
            have hleft := readWithPadding_eq_toByteArray_of_memoryWordNat_eq
              (exponentCopyMemory correction.memory
                (UInt256.ofNat (barrettCallResultFp fp kWords)) r (UInt256.ofNat kWords))
              read (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
                (barrettResetMemory mem (UInt256.ofNat fp)) read)) (by rw [hnat])
            have hright := readWithPadding_eq_toByteArray_of_memoryWordNat_eq
              (barrettResetMemory mem (UInt256.ofNat fp)) read
              (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
                (barrettResetMemory mem (UInt256.ofNat fp)) read)) rfl
            exact hleft.trans hright.symm
          have hreset := setFreePtr_read_above_padded (mem := mem) (fp := fp)
            (read := read) invariant.memorySize hread
          exact hcopyRead.trans (by
            simpa only [barrettResetMemory, setFreePtr] using hreset)

theorem InitialBarrettExponentInvariant.freshSquareValid
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hselect : selectFreshBarrettSquare fuel mem aw kWords fp r n mu = some selected) :
    FreshBarrettSquareValid I fuel mem aw kWords fp r n mu selected := by
  unfold selectFreshBarrettSquare at hselect
  cases hcall : selectFreshBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hcall] at hselect
  | some call =>
      simp only [hcall, Option.some.injEq] at hselect
      subst selected
      unfold selectFreshBarrettExponentCall at hcall
      cases hcorrection : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => rw [hcorrection] at hcall; contradiction
      | some correction =>
          rw [hcorrection] at hcall
          injection hcall with heq
          subst call
          exact {
            selection := by
              simp [selectFreshBarrettSquare, selectFreshBarrettExponentCall, hcorrection]
            scratch := invariant.resetFreshScratch invariant.rBase invariant.rBase
              invariant.rBeforeScratch invariant.rBeforeScratch hcorrection
            callSelection := by simp [selectFreshBarrettExponentCall, hcorrection] }

/-- A selected square call is valid directly from the preserved exponent state. -/
theorem BarrettExponentInvariant.squareValid
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hselect : selectBarrettSquare fuel mem aw kWords fp r n mu = some selected) :
    BarrettSquareValid I fuel mem aw kWords fp r n mu selected := by
  unfold selectBarrettSquare at hselect
  cases hcall : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hcall] at hselect
  | some call =>
      simp only [hcall, Option.some.injEq] at hselect
      subst selected
      unfold selectBarrettExponentCall at hcall
      cases hcorrection : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => rw [hcorrection] at hcall; contradiction
      | some correction =>
          rw [hcorrection] at hcall
          injection hcall with heq
          subst call
          exact {
            selection := by simp [selectBarrettSquare, selectBarrettExponentCall, hcorrection]
            call := {
              scratch := invariant.resetScratch invariant.rBase invariant.rBase
                invariant.rBeforeScratch invariant.rBeforeScratch hcorrection
              selection := by simp [selectBarrettExponentCall, hcorrection] } }

/-- A selected multiply call is valid directly from the preserved exponent state. -/
theorem BarrettExponentInvariant.multiplyValid
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettMultiplySelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hselect : selectBarrettMultiply fuel mem aw kWords fp r a n mu = some selected) :
    BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected := by
  unfold selectBarrettMultiply at hselect
  cases hcall : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r a n mu r fp kWords with
  | none => simp [hcall] at hselect
  | some call =>
      simp only [hcall, Option.some.injEq] at hselect
      subst selected
      unfold selectBarrettExponentCall at hcall
      cases hcorrection : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r a n mu fp kWords with
      | none => rw [hcorrection] at hcall; contradiction
      | some correction =>
          rw [hcorrection] at hcall
          injection hcall with heq
          subst call
          exact {
            selection := by simp [selectBarrettMultiply, selectBarrettExponentCall, hcorrection]
            call := {
              scratch := invariant.resetScratch invariant.rBase invariant.aBase
                invariant.rBeforeScratch
                (le_trans invariant.aBeforeR (by
                  have hr := invariant.rBeforeScratch
                  omega)) hcorrection
              selection := by simp [selectBarrettExponentCall, hcorrection] } }

theorem validBarrettSquareExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {fuel kWords fp : Nat}
    {mem : ByteArray} {aw bit r n mu : UInt256} {selected : BarrettSquareSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : BarrettSquareValid I fuel mem aw kWords fp r n mu selected)
    (hdepth : tail.length + 25 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3379⟩
      (bit :: r :: UInt256.ofNat kWords :: n :: UInt256.ofNat fp :: mu ::
        tail) mem aw rdata acc steps gasUsed) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3411⟩
      (r :: UInt256.ofNat kWords :: n :: previousBit :: previousBit :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have hselection := valid.selection
  unfold selectBarrettSquare at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      have rd6446 := barrettSquareEntry (tail := tail) (by omega) h
      have rd3411 := validBarrettExponentCallExact (resumePc := ⟨3411⟩) (tail :=
          r :: UInt256.ofNat kWords :: n :: (UInt256.lnot ⟨0⟩ + bit) ::
            (UInt256.lnot ⟨0⟩ + bit) :: tail)
        valid.call (by simp only [List.length_cons]; omega) (by native_decide)
        (by simpa using rd6446)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3411

theorem validFreshBarrettSquareExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {fuel kWords fp : Nat}
    {mem : ByteArray} {aw bit r n mu : UInt256} {selected : BarrettSquareSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : FreshBarrettSquareValid I fuel mem aw kWords fp r n mu selected)
    (hdepth : tail.length + 25 <= 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3379⟩
      (bit :: r :: UInt256.ofNat kWords :: n :: UInt256.ofNat fp :: mu ::
        tail) mem aw rdata acc steps gasUsed) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3411⟩
      (r :: UInt256.ofNat kWords :: n :: previousBit :: previousBit :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have hselection := valid.selection
  unfold selectFreshBarrettSquare at hselection
  cases hc : selectFreshBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      have rd6446 := barrettSquareEntry (tail := tail) (by omega) h
      have rd3411 := validFreshBarrettExponentCallExact (resumePc := ⟨3411⟩) (tail :=
          r :: UInt256.ofNat kWords :: n :: (UInt256.lnot ⟨0⟩ + bit) ::
            (UInt256.lnot ⟨0⟩ + bit) :: tail)
        valid.scratch valid.callSelection (by simp only [List.length_cons]; omega)
        (by native_decide) (by simpa using rd6446)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3411

theorem validBarrettMultiplyExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {fuel kWords fp : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettMultiplySelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected)
    (hdepth : tail.length + 20 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3448⟩
      (mu :: UInt256.ofNat fp :: a :: r :: UInt256.ofNat kWords :: n :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3467⟩ tail
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have hselection := valid.selection
  unfold selectBarrettMultiply at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r a n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      have rd6446 := barrettMultiplyEntry (tail := tail) (by omega) h
      have rd3467 := validBarrettExponentCallExact (resumePc := ⟨3467⟩) valid.call
        (by omega) (by native_decide)
        (by simpa using rd6446)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3467

inductive BarrettBitLoopSelection where
  | done (memory : ByteArray) (activeWords : UInt256)
  | unset (square : BarrettSquareSelection) (rest : BarrettBitLoopSelection)
  | set (square : BarrettSquareSelection) (multiply : BarrettMultiplySelection)
      (rest : BarrettBitLoopSelection)

namespace BarrettBitLoopSelection

def memory : BarrettBitLoopSelection → ByteArray
  | .done mem _ => mem
  | .unset _ rest => rest.memory
  | .set _ _ rest => rest.memory

def activeWords : BarrettBitLoopSelection → UInt256
  | .done _ aw => aw
  | .unset _ rest => rest.activeWords
  | .set _ _ rest => rest.activeWords

def steps : BarrettBitLoopSelection → Nat
  | .done _ _ => 0
  | .unset square rest => square.steps + 34 + rest.steps
  | .set square multiply rest => square.steps + multiply.steps + 43 + rest.steps

def gas : BarrettBitLoopSelection → Nat
  | .done _ _ => 0
  | .unset square rest => square.gas + 109 + rest.gas
  | .set square multiply rest => square.gas + multiply.gas + 139 + rest.gas

end BarrettBitLoopSelection

def selectBarrettBitLoop (bitFuel callFuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (bit byte r a n mu : UInt256) : Option BarrettBitLoopSelection :=
  if bit = ⟨0⟩ then some (.done mem aw) else
    match bitFuel with
    | 0 => none
    | bitFuel + 1 =>
        match selectBarrettSquare callFuel mem aw kWords fp r n mu with
        | none => none
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            if ((⟨1⟩ : UInt256).land ((byte.land ⟨255⟩).shiftRight previousBit)).eq
                ⟨1⟩ = ⟨0⟩ then
              match selectBarrettBitLoop bitFuel callFuel square.memory square.activeWords
                  kWords fp previousBit byte r a n mu with
              | none => none
              | some rest => some (.unset square rest)
            else
              match selectBarrettMultiply callFuel square.memory square.activeWords
                  kWords fp r a n mu with
              | none => none
              | some multiply =>
                  match selectBarrettBitLoop bitFuel callFuel multiply.memory
                      multiply.activeWords kWords fp previousBit byte r a n mu with
                  | none => none
                  | some rest => some (.set square multiply rest)

/-- The bit selector is total when bit fuel bounds the concrete descending bit counter and call
fuel bounds the modulus limb count. -/
theorem selectBarrettBitLoop_exists
    {bitFuel callFuel kWords fp : Nat} {mem : ByteArray} {aw bit byte r a n mu : UInt256}
    (hkPos : 0 < kWords) (hcallFuel : kWords ≤ callFuel)
    (hbitFuel : bit.toNat ≤ bitFuel) :
    ∃ selected,
      selectBarrettBitLoop bitFuel callFuel mem aw kWords fp bit byte r a n mu =
        some selected := by
  induction bitFuel generalizing mem aw bit with
  | zero =>
      have hbitNat : bit.toNat = 0 := by omega
      have hbit : bit = ⟨0⟩ := by
        apply u256_inj
        simpa using hbitNat
      simp [selectBarrettBitLoop, hbit]
  | succ bitFuel ih =>
      by_cases hbit : bit = ⟨0⟩
      · simp [selectBarrettBitLoop, hbit]
      · let previousBit := UInt256.lnot ⟨0⟩ + bit
        have hpreviousFuel : previousBit.toNat ≤ bitFuel := by
          rw [previousBit_toNat hbit]
          omega
        rcases selectBarrettSquare_exists (mem := mem) (aw := aw) (r := r) (n := n)
          (mu := mu) (fp := fp) hkPos hcallFuel with ⟨square, hsquare⟩
        by_cases hunset : ((⟨1⟩ : UInt256).land
            ((byte.land ⟨255⟩).shiftRight previousBit)).eq ⟨1⟩ = ⟨0⟩
        · rcases ih (mem := square.memory) (aw := square.activeWords) (bit := previousBit)
            hpreviousFuel with ⟨rest, hrest⟩
          simp only [selectBarrettBitLoop, hbit, if_false, hsquare]
          rw [if_pos hunset, hrest]
          exact ⟨_, rfl⟩
        · rcases selectBarrettMultiply_exists (mem := square.memory)
            (aw := square.activeWords) (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
            hkPos hcallFuel with ⟨multiply, hmultiply⟩
          rcases ih (mem := multiply.memory) (aw := multiply.activeWords)
            (bit := previousBit) hpreviousFuel with ⟨rest, hrest⟩
          have hrestRaw : selectBarrettBitLoop bitFuel callFuel multiply.memory
              multiply.activeWords kWords fp (UInt256.lnot ⟨0⟩ + bit) byte r a n mu =
              some rest := by
            simpa only [previousBit] using hrest
          simp only [selectBarrettBitLoop, hbit, if_false, hsquare]
          rw [if_neg hunset]
          simp only [hmultiply]
          rw [hrestRaw]
          exact ⟨_, rfl⟩

inductive BarrettBitLoopValid (I : ExecutionEnv) (callFuel : Nat)
    (kWords fp : Nat) (r a n mu byte : UInt256) :
    ByteArray → UInt256 → UInt256 → BarrettBitLoopSelection → Prop where
  | done (mem : ByteArray) (aw : UInt256) :
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw ⟨0⟩ (.done mem aw)
  | unset {mem : ByteArray} {aw bit : UInt256} {square : BarrettSquareSelection}
      {rest : BarrettBitLoopSelection}
      (bitNonzero : bit ≠ ⟨0⟩)
      (squareValid : BarrettSquareValid I callFuel mem aw kWords fp r n mu square)
      (bitUnset : ((⟨1⟩ : UInt256).land
        ((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit))).eq ⟨1⟩ = ⟨0⟩)
      (restValid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte
        square.memory square.activeWords (UInt256.lnot ⟨0⟩ + bit) rest) :
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit (.unset square rest)
  | set {mem : ByteArray} {aw bit : UInt256} {square : BarrettSquareSelection}
      {multiply : BarrettMultiplySelection} {rest : BarrettBitLoopSelection}
      (bitNonzero : bit ≠ ⟨0⟩)
      (squareValid : BarrettSquareValid I callFuel mem aw kWords fp r n mu square)
      (multiplyValid : BarrettMultiplyValid I callFuel square.memory square.activeWords
        kWords fp r a n mu multiply)
      (bitSet : ((⟨1⟩ : UInt256).land
        ((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit))).eq ⟨1⟩ ≠ ⟨0⟩)
      (restValid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte
        multiply.memory multiply.activeWords (UInt256.lnot ⟨0⟩ + bit) rest) :
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit
        (.set square multiply rest)

/-- A successful executable selector is recursively valid when each selected call satisfies the
local deployed-call geometry. -/
theorem selectBarrettBitLoop_valid
    {I : ExecutionEnv} {bitFuel callFuel kWords fp : Nat}
    {r a n mu byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettBitLoopSelection}
    (hsquareValid : ∀ (mem' : ByteArray) (aw' : UInt256)
      (square : BarrettSquareSelection),
      selectBarrettSquare callFuel mem' aw' kWords fp r n mu = some square →
        BarrettSquareValid I callFuel mem' aw' kWords fp r n mu square)
    (hmultiplyValid : ∀ (mem' : ByteArray) (aw' : UInt256)
      (multiply : BarrettMultiplySelection),
      selectBarrettMultiply callFuel mem' aw' kWords fp r a n mu = some multiply →
        BarrettMultiplyValid I callFuel mem' aw' kWords fp r a n mu multiply)
    (hselect : selectBarrettBitLoop bitFuel callFuel mem aw kWords fp
      bit byte r a n mu = some selected) :
    BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected := by
  induction bitFuel generalizing mem aw bit selected with
  | zero =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw
      · simp [hbit] at hselect
  | succ bitFuel ih =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw
      · simp only [hbit, ↓reduceIte] at hselect
        cases hsquare : selectBarrettSquare callFuel mem aw kWords fp r n mu with
        | none => simp [hsquare] at hselect
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            by_cases hunset : ((⟨1⟩ : UInt256).land
                ((byte.land ⟨255⟩).shiftRight previousBit)).eq ⟨1⟩ = ⟨0⟩
            · cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
                  square.activeWords kWords fp previousBit byte r a n mu with
              | none => simp [hsquare, previousBit, hunset, hrest] at hselect
              | some rest =>
                  simp only [hsquare, previousBit, hunset, if_true, hrest,
                    Option.some.injEq] at hselect
                  subst selected
                  exact .unset hbit (hsquareValid mem aw square hsquare) hunset (ih hrest)
            · cases hmultiply : selectBarrettMultiply callFuel square.memory
                  square.activeWords kWords fp r a n mu with
              | none => simp [hsquare, previousBit, hunset, hmultiply] at hselect
              | some multiply =>
                  cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
                      multiply.activeWords kWords fp previousBit byte r a n mu with
                  | none =>
                      simp [hsquare, previousBit, hunset, hmultiply, hrest] at hselect
                  | some rest =>
                      simp only [hsquare, previousBit, hunset, if_false, hmultiply, hrest,
                        Option.some.injEq] at hselect
                      subst selected
                      exact .set hbit (hsquareValid mem aw square hsquare)
                        (hmultiplyValid square.memory square.activeWords multiply hmultiply)
                        hunset (ih hrest)

theorem validBarrettBitLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettBitLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    {aux0 aux1 aux2 aux3 : UInt256}
    (valid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected)
    (hdepth : tail.length + 36 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3364⟩
      (barrettBitGuardStack bit r (UInt256.ofNat kWords) n (UInt256.ofNat fp) mu byte
        aux0 aux1 aux2 a aux3 tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3364⟩
      (barrettBitGuardStack ⟨0⟩ r (UInt256.ofNat kWords) n (UInt256.ofNat fp) mu byte
        aux0 aux1 aux2 a aux3 tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  induction valid generalizing steps gasUsed with
  | done mem aw =>
      simpa [BarrettBitLoopSelection.memory, BarrettBitLoopSelection.activeWords,
        BarrettBitLoopSelection.steps, BarrettBitLoopSelection.gas] using h
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      have rd3379 := barrettBitGuardTaken (by omega) bitNonzero h
      let squareTail := byte :: aux0 :: aux1 :: aux2 :: mu :: UInt256.ofNat fp :: a ::
        UInt256.ofNat kWords :: aux3 :: n :: r :: tail
      have rd3411 := validBarrettSquareExact (tail := squareTail) squareValid (by
        simp only [squareTail, List.length_cons]
        omega) (by
          simpa [barrettSquareStack, barrettBitFrame, squareTail] using rd3379)
      have rdNext := barrettUnsetBitToGuard (tail := tail) (by omega) bitUnset (by
        simpa [squareTail] using rd3411)
      have rdFinal := ih (steps := steps + 1 + square.steps + 33)
        (gasUsed := gasUsed + 10 + square.gas + 99) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      simpa [BarrettBitLoopSelection.memory, BarrettBitLoopSelection.activeWords,
        BarrettBitLoopSelection.steps, BarrettBitLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      have rd3379 := barrettBitGuardTaken (by omega) bitNonzero h
      let squareTail := byte :: aux0 :: aux1 :: aux2 :: mu :: UInt256.ofNat fp :: a ::
        UInt256.ofNat kWords :: aux3 :: n :: r :: tail
      have rd3411 := validBarrettSquareExact (tail := squareTail) squareValid (by
        simp only [squareTail, List.length_cons]
        omega) (by
          simpa [barrettSquareStack, barrettBitFrame, squareTail] using rd3379)
      have rd3448 := barrettSetBitToMultiply (tail := tail) (by omega) bitSet (by
        simpa [squareTail] using rd3411)
      let multiplyTail := (UInt256.lnot ⟨0⟩ + bit) :: (UInt256.lnot ⟨0⟩ + bit) ::
        byte :: aux0 :: aux1 :: aux2 :: mu :: UInt256.ofNat fp :: a ::
        UInt256.ofNat kWords :: aux3 :: n :: r :: tail
      have rd3467 := validBarrettMultiplyExact (tail := multiplyTail) multiplyValid (by
        simp only [multiplyTail, List.length_cons]
        omega) (by simpa [multiplyTail] using rd3448)
      have rdNext := barrettSetResultToGuard (tail := tail) (by omega) (by
        simpa [multiplyTail] using rd3467)
      have rdFinal := ih
        (steps := steps + 1 + square.steps + 15 + multiply.steps + 27)
        (gasUsed := gasUsed + 10 + square.gas + 50 + multiply.gas + 79) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      simpa [BarrettBitLoopSelection.memory, BarrettBitLoopSelection.activeWords,
        BarrettBitLoopSelection.steps, BarrettBitLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

/-! ## Pure arithmetic interpretation -/

structure BarrettSquareSemanticGeometry
    (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray) (aw : UInt256) (kWords fp : Nat)
    (r n mu : UInt256) (selected : BarrettSquareSelection) (rValue nValue : Nat) : Prop where
  initialValue : barrettAccumulatorValue kWords r mem = rValue
  call : BarrettCallSemanticGeometry I fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r r n mu r fp kWords selected.call.correction rValue rValue nValue

structure BarrettMultiplySemanticGeometry
    (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray) (aw : UInt256) (kWords fp : Nat)
    (r a n mu : UInt256) (selected : BarrettMultiplySelection)
    (rValue baseValue nValue : Nat) : Prop where
  accumulatorValue : barrettAccumulatorValue kWords r mem = rValue
  baseValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (a.toNat + 32) kWords) = baseValue
  call : BarrettCallSemanticGeometry I fuel
    (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
    r a n mu r fp kWords selected.call.correction rValue baseValue nValue

/-- The first fresh square materializes scratch and establishes the ordinary persistent invariant
used by the leading-bit multiply and every later operation. -/
theorem InitialBarrettExponentInvariant.afterFreshSquare
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : FreshBarrettSquareValid I fuel mem aw kWords fp r n mu selected) :
    BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
      (rValue * rValue % nValue) baseValue nValue := by
  have hselection := valid.selection
  unfold selectFreshBarrettSquare at hselection
  cases hc : selectFreshBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      unfold selectFreshBarrettExponentCall at hc
      cases hr : Modexp.MultiLimbBarrettExponentTrace.selectBarrettCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => simp [hr] at hc
      | some correction =>
          simp only [hr, Option.some.injEq] at hc
          subst call
          let resetMem := barrettResetMemory mem (UInt256.ofNat fp)
          let resetAw := barrettResetAw aw
          have fresh : FreshScratchInvariant I fuel resetMem resetAw
              r r n mu fp kWords correction := by
            simpa only [resetMem, resetAw] using valid.scratch
          have hresetWords : forall ptr words, 96 <= ptr ->
              memoryWordsFrom resetMem ptr words = memoryWordsFrom mem ptr words := by
            intro ptr words hptr
            simpa only [resetMem] using
              memoryWordsFrom_barrettResetMemory_above mem fp ptr words
                invariant.memorySize hptr
          have hrAdd : (r + ⟨32⟩).toNat = r.toNat + 32 :=
            uadd_word_lit32_toNat r (by
              exact lt_of_le_of_lt (by
                apply le_trans (b := scratchEnd fp kWords)
                · have hrb := invariant.rBeforeScratch
                  unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
                  omega
                · exact invariant.scratchBound.le)
                (by norm_num [UInt256.size]))
          have hrValue : Modexp.wordLimbsToNat
              (memoryWordsFrom resetMem (r.toNat + 32) kWords) = rValue := by
            rw [hresetWords (r.toNat + 32) kWords (by have hb := invariant.rBase; omega)]
            simpa [barrettAccumulatorValue, hrAdd] using invariant.rValueEq
          have hnValue : Modexp.wordLimbsToNat
              (memoryWordsFrom resetMem (n.toNat + 32) kWords) = nValue := by
            rw [hresetWords (n.toNat + 32) kWords (by have hb := invariant.nBase; omega)]
            exact invariant.nValueEq
          have hmuValue : Modexp.wordLimbsToNat
              (memoryWordsFrom resetMem (mu.toNat + 32) (kWords + 2)) =
                UInt256.size ^ (2 * kWords) / nValue := by
            rw [hresetWords (mu.toNat + 32) (kWords + 2)
              (by have hb := invariant.muBase; omega)]
            exact invariant.muValueEq
          have hrBound : rValue < UInt256.size ^ kWords := by
            have hbound := Modexp.wordLimbsToNat_lt_pow
              (memoryWordsFrom resetMem (r.toNat + 32) kWords)
            rw [memoryWordsFrom_length, hrValue] at hbound
            exact hbound
          have hproduct : rValue * rValue < UInt256.size ^ (2 * kWords) := by
            have hpowPos : 0 < UInt256.size ^ kWords :=
              pow_pos (by norm_num [UInt256.size]) _
            have hmul : rValue * rValue <
                (UInt256.size ^ kWords) * (UInt256.size ^ kWords) := by
              nlinarith
            calc
              rValue * rValue < UInt256.size ^ kWords * UInt256.size ^ kWords := hmul
              _ = UInt256.size ^ (2 * kWords) := by
                rw [← pow_add]
                congr 1
                omega
          have hcopy := fresh.copyStateGeometry invariant.rBase invariant.rBeforeScratch
          have hframe : forall ptr words, 96 <= ptr ->
              ptr + 32 * words <= r.toNat + 32 ->
              memoryWordsFrom
                  (exponentCopyMemory correction.memory
                    (UInt256.ofNat (barrettCallResultFp fp kWords)) r
                    (UInt256.ofNat kWords)) ptr words =
                memoryWordsFrom mem ptr words := by
            intro ptr words hptr hbelow
            rw [hcopy.2.2.2 ptr words hptr hbelow]
            exact hresetWords ptr words hptr
          have hheader : forall ptr (word : UInt256), 96 <= ptr ->
              ptr + 32 <= r.toNat + 32 ->
              mem.readWithPadding ptr 32 = word.toByteArray ->
              (exponentCopyMemory correction.memory
                (UInt256.ofNat (barrettCallResultFp fp kWords)) r
                (UInt256.ofNat kWords)).readWithPadding ptr 32 = word.toByteArray := by
            intro ptr word hptr hbelow horiginal
            apply readWithPadding_eq_toByteArray_of_memoryWordNat_eq
            have hwords := hframe ptr 1 hptr (by simpa using hbelow)
            have hword : UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
                (exponentCopyMemory correction.memory
                  (UInt256.ofNat (barrettCallResultFp fp kWords)) r
                  (UInt256.ofNat kWords)) ptr) =
                UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) := by
              simpa [memoryWordsFrom] using hwords
            apply hword.trans
            unfold Modexp.MultiLimbMemoryModel.memoryWordNat
            rw [horiginal, fromByteArrayBigEndian_toByteArray]
            exact u256_ofNat_toNat word
          have htarget : (r + ⟨32⟩).toNat <= correction.memory.size := by
            rw [hrAdd, fresh.selectedStateGeometry.2.2.1]
            apply le_trans (b := fp)
            · have hb := invariant.rBeforeScratch
              omega
            · unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
              omega
          have hresult := fresh.copiedResultValue hrValue hrValue hnValue hmuValue rfl
            invariant.nPos invariant.nNormalized invariant.nFits hproduct htarget
          exact {
            wordsPos := invariant.wordsPos
            words := invariant.words
            scratchBound := invariant.scratchBound
            calldataBound := invariant.calldataBound
            freePointerBase := invariant.freePointerBase
            covered := hcopy.1
            activeWordsFit := hcopy.2.1
            scratchConcrete := by rw [hcopy.2.2.1]
            rBase := invariant.rBase
            aBase := invariant.aBase
            nBase := invariant.nBase
            muBase := invariant.muBase
            aBeforeR := invariant.aBeforeR
            nBeforeR := invariant.nBeforeR
            muBeforeR := invariant.muBeforeR
            rBeforeScratch := invariant.rBeforeScratch
            rHeader := hheader r.toNat (UInt256.ofNat kWords) invariant.rBase (by omega)
              invariant.rHeader
            aHeader := hheader a.toNat (UInt256.ofNat kWords) invariant.aBase (by
              have hb := invariant.aBeforeR
              omega) invariant.aHeader
            nHeader := hheader n.toNat (UInt256.ofNat kWords) invariant.nBase (by
              have hb := invariant.nBeforeR
              omega) invariant.nHeader
            muHeader := hheader mu.toNat (UInt256.ofNat (kWords + 2)) invariant.muBase (by
              have hb := invariant.muBeforeR
              omega) invariant.muHeader
            rValueEq := hresult
            baseValueEq := by
              rw [hframe (a.toNat + 32) kWords (by have hb := invariant.aBase; omega) (by
                have hb := invariant.aBeforeR
                omega)]
              exact invariant.baseValueEq
            nValueEq := by
              rw [hframe (n.toNat + 32) kWords (by have hb := invariant.nBase; omega) (by
                have hb := invariant.nBeforeR
                omega)]
              exact invariant.nValueEq
            muValueEq := by
              rw [hframe (mu.toNat + 32) (kWords + 2)
                (by have hb := invariant.muBase; omega) (by
                  have hb := invariant.muBeforeR
                  omega)]
              exact invariant.muValueEq
            nPos := invariant.nPos
            nNormalized := invariant.nNormalized
            nFits := invariant.nFits }

/-- The persistent exponent invariant supplies all numeric geometry for a selected square. -/
theorem BarrettExponentInvariant.squareGeometry
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettSquareValid I fuel mem aw kWords fp r n mu selected) :
    BarrettSquareSemanticGeometry I fuel mem aw kWords fp r n mu selected
      rValue nValue := by
  have hmem96 : 96 <= mem.size := by
    exact invariant.freePointerBase.trans (le_trans (by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) invariant.scratchConcrete)
  have hrAdd : (r + ⟨32⟩).toNat = r.toNat + 32 :=
    uadd_word_lit32_toNat r (by
      exact lt_of_le_of_lt (by
        have hr := invariant.rBeforeScratch
        apply le_trans (b := scratchEnd fp kWords)
        · unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact invariant.scratchBound.le)
        (by norm_num [UInt256.size]))
  have hrReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (r.toNat + 32) kWords hmem96 (by have hr := invariant.rBase; omega)
  have hnReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (n.toNat + 32) kWords hmem96 (by have hn := invariant.nBase; omega)
  have hmuReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (mu.toNat + 32) (kWords + 2) hmem96 (by have hmu := invariant.muBase; omega)
  have hrValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (r.toNat + 32) kWords) = rValue := by
    rw [hrReset]
    simpa [barrettAccumulatorValue, hrAdd] using invariant.rValueEq
  have hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (n.toNat + 32) kWords) = nValue := by
    rw [hnReset]
    exact invariant.nValueEq
  have hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue := by
    rw [hmuReset]
    exact invariant.muValueEq
  have hrBound : rValue < UInt256.size ^ kWords := by
    have hbound := Modexp.wordLimbsToNat_lt_pow
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (r.toNat + 32) kWords)
    rw [memoryWordsFrom_length, hrValue] at hbound
    exact hbound
  have hproduct : rValue * rValue < UInt256.size ^ (2 * kWords) := by
    have hpowPos : 0 < UInt256.size ^ kWords := pow_pos (by norm_num [UInt256.size]) _
    have hmul : rValue * rValue <
        (UInt256.size ^ kWords) * (UInt256.size ^ kWords) := by
      nlinarith
    calc
      rValue * rValue < UInt256.size ^ kWords * UInt256.size ^ kWords := hmul
      _ = UInt256.size ^ (2 * kWords) := by
        rw [← pow_add]
        congr 1
        omega
  have hstate := valid.call.scratch.selectedStateGeometry
  let resultFp := barrettCallResultFp fp kWords
  have hresultFp : resultFp < 2 ^ 64 := by
    apply lt_of_le_of_lt _ invariant.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp :=
    UInt256.toNat_ofNat_of_lt (hresultFp.trans (by decide))
  have hsourceNat : (UInt256.ofNat resultFp + ⟨32⟩).toNat = resultFp + 32 :=
    (uadd_word_lit32_toNat (UInt256.ofNat resultFp) (by
      rw [hresultNat]
      exact (show resultFp + 32 < UInt256.size by
        exact (show resultFp + 32 < 2 ^ 64 by
          apply lt_of_le_of_lt _ invariant.scratchBound
          dsimp only [resultFp, barrettCallResultFp]
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega).trans (by decide)))).trans (by rw [hresultNat])
  exact {
    initialValue := invariant.rValueEq
    call := {
      scratch := valid.call.scratch
      aValueEq := hrValue
      bValueEq := hrValue
      nValueEq := hnValue
      muValueEq := hmuValue
      nPos := invariant.nPos
      nNormalized := invariant.nNormalized
      nFits := invariant.nFits
      productBound := hproduct
      copySource := by
        rw [show barrettCallResultFp fp kWords = resultFp by rfl, hsourceNat]
        exact le_trans (by
          dsimp only [resultFp, barrettCallResultFp]
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hstate.2.2.1
      copyTarget := by
        rw [hrAdd]
        exact le_trans (by
          have hr := invariant.rBeforeScratch
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hstate.2.2.1 } }

/-- The persistent exponent invariant supplies all numeric geometry for a selected multiply. -/
theorem BarrettExponentInvariant.multiplyGeometry
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettMultiplySelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected) :
    BarrettMultiplySemanticGeometry I fuel mem aw kWords fp r a n mu selected
      rValue baseValue nValue := by
  have hmem96 : 96 <= mem.size := by
    exact invariant.freePointerBase.trans (le_trans (by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) invariant.scratchConcrete)
  have haReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (a.toNat + 32) kWords hmem96 (by have ha := invariant.aBase; omega)
  have hrReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (r.toNat + 32) kWords hmem96 (by have hr := invariant.rBase; omega)
  have hnReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (n.toNat + 32) kWords hmem96 (by have hn := invariant.nBase; omega)
  have hmuReset := memoryWordsFrom_barrettResetMemory_above mem fp
    (mu.toNat + 32) (kWords + 2) hmem96 (by have hmu := invariant.muBase; omega)
  have hrAdd : (r + ⟨32⟩).toNat = r.toNat + 32 :=
    uadd_word_lit32_toNat r (by
      exact lt_of_le_of_lt (by
        have hr := invariant.rBeforeScratch
        apply le_trans (b := scratchEnd fp kWords)
        · unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact invariant.scratchBound.le)
        (by norm_num [UInt256.size]))
  have hrValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (r.toNat + 32) kWords) = rValue := by
    rw [hrReset]
    simpa [barrettAccumulatorValue, hrAdd] using invariant.rValueEq
  have hbaseValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (a.toNat + 32) kWords) = baseValue := by
    rw [haReset]
    exact invariant.baseValueEq
  have hbaseBound : baseValue < UInt256.size ^ kWords := by
    have hbound := Modexp.wordLimbsToNat_lt_pow
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (a.toNat + 32) kWords)
    rw [memoryWordsFrom_length, hbaseValue] at hbound
    exact hbound
  have hrBound : rValue < UInt256.size ^ kWords := by
    have hbound := Modexp.wordLimbsToNat_lt_pow
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (r.toNat + 32) kWords)
    rw [memoryWordsFrom_length, hrValue] at hbound
    exact hbound
  have hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (n.toNat + 32) kWords) = nValue := by
    rw [hnReset]
    exact invariant.nValueEq
  have hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (barrettResetMemory mem (UInt256.ofNat fp))
        (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue := by
    rw [hmuReset]
    exact invariant.muValueEq
  have hstate := valid.call.scratch.selectedStateGeometry
  let resultFp := barrettCallResultFp fp kWords
  have hresultFp : resultFp < 2 ^ 64 := by
    apply lt_of_le_of_lt _ invariant.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp :=
    UInt256.toNat_ofNat_of_lt (hresultFp.trans (by decide))
  have hsourceNat : (UInt256.ofNat resultFp + ⟨32⟩).toNat = resultFp + 32 :=
    (uadd_word_lit32_toNat (UInt256.ofNat resultFp) (by
      rw [hresultNat]
      exact (show resultFp + 32 < UInt256.size by
        exact (show resultFp + 32 < 2 ^ 64 by
          apply lt_of_le_of_lt _ invariant.scratchBound
          dsimp only [resultFp, barrettCallResultFp]
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega).trans (by decide)))).trans (by rw [hresultNat])
  exact {
    accumulatorValue := invariant.rValueEq
    baseValueEq := invariant.baseValueEq
    call := {
      scratch := valid.call.scratch
      aValueEq := hrValue
      bValueEq := hbaseValue
      nValueEq := hnValue
      muValueEq := hmuValue
      nPos := invariant.nPos
      nNormalized := invariant.nNormalized
      nFits := invariant.nFits
      productBound := by
        have hpowPos : 0 < UInt256.size ^ kWords :=
          pow_pos (by norm_num [UInt256.size]) _
        have hmul : rValue * baseValue <
            (UInt256.size ^ kWords) * (UInt256.size ^ kWords) := by
          nlinarith
        calc
          rValue * baseValue < UInt256.size ^ kWords * UInt256.size ^ kWords :=
            hmul
          _ = UInt256.size ^ (2 * kWords) := by
            rw [← pow_add]
            congr 1
            omega
      copySource := by
        rw [show barrettCallResultFp fp kWords = resultFp by rfl, hsourceNat]
        exact le_trans (by
          dsimp only [resultFp, barrettCallResultFp]
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hstate.2.2.1
      copyTarget := by
        rw [hrAdd]
        exact le_trans (by
          have hr := invariant.rBeforeScratch
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hstate.2.2.1 } }

/-- Copying a selected reused Barrett result back to the accumulator reconstructs the full
persistent exponent invariant for the next bit. -/
theorem BarrettExponentInvariant.afterCall
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue xValue yValue : Nat}
    {mem : ByteArray} {aw r a n mu x y : UInt256}
    {correction : BarrettCorrectionSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (geometry : BarrettCallSemanticGeometry I fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      x y n mu r fp kWords correction xValue yValue nValue) :
    BarrettExponentInvariant I
      (exponentCopyMemory correction.memory
        (UInt256.ofNat (barrettCallResultFp fp kWords)) r (UInt256.ofNat kWords))
      (exponentCopyAw correction.activeWords
        (UInt256.ofNat (barrettCallResultFp fp kWords)) r (UInt256.ofNat kWords))
      kWords fp r a n mu (xValue * yValue % nValue) baseValue nValue := by
  have hstate := geometry.scratch.selectedStateGeometry
  let resultFp := barrettCallResultFp fp kWords
  let source := UInt256.ofNat resultFp + ⟨32⟩
  let target := r + ⟨32⟩
  let bytes := UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩
  have hmem96 : 96 <= mem.size := by
    exact invariant.freePointerBase.trans (le_trans (by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) invariant.scratchConcrete)
  have hrAdd : target.toNat = r.toNat + 32 := by
    dsimp only [target]
    exact uadd_word_lit32_toNat r (by
      exact lt_of_le_of_lt (by
        apply le_trans (b := scratchEnd fp kWords)
        · have hr := invariant.rBeforeScratch
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact invariant.scratchBound.le)
        (by norm_num [UInt256.size]))
  have hbytes : bytes.toNat = 32 * kWords := by
    dsimp only [bytes]
    exact ushl5_ofNat_toNat kWords (by have hw := invariant.words; omega)
  have hsource : source.toNat + bytes.toNat <= correction.memory.size := by
    simpa only [source, bytes, resultFp, hbytes] using geometry.copySource
  have htarget : target.toNat + bytes.toNat <= correction.memory.size := by
    rw [hrAdd, hbytes]
    exact le_trans (by
      have hr := invariant.rBeforeScratch
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hstate.2.2.1
  have haccess : max target.toNat source.toNat + bytes.toNat + 31 < UInt256.size := by
    have hresultFp : resultFp < 2 ^ 64 := by
      apply lt_of_le_of_lt _ invariant.scratchBound
      dsimp only [resultFp, barrettCallResultFp]
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp :=
      UInt256.toNat_ofNat_of_lt (hresultFp.trans (by decide))
    have hsourceNat : source.toNat = resultFp + 32 := by
      dsimp only [source]
      rw [uadd_word_lit32_toNat (UInt256.ofNat resultFp) (by
        rw [hresultNat]
        exact (show resultFp + 32 < UInt256.size by
          exact (show resultFp + 32 < 2 ^ 64 by
            apply lt_of_le_of_lt _ invariant.scratchBound
            dsimp only [resultFp, barrettCallResultFp]
            unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
            omega).trans (by decide))), hresultNat]
    have hr := invariant.rBeforeScratch
    have hs := invariant.scratchBound
    have htarget64 : target.toNat < 2 ^ 64 := by
      rw [hrAdd]
      apply lt_of_le_of_lt _ hs
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hsource64 : source.toNat < 2 ^ 64 := by
      rw [hsourceNat]
      apply lt_of_le_of_lt _ hs
      dsimp only [resultFp, barrettCallResultFp]
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hmax64 : max target.toNat source.toNat < 2 ^ 64 :=
      (max_lt_iff).2 ⟨htarget64, hsource64⟩
    have hbytesBound : bytes.toNat <= 1024 := by
      rw [hbytes]
      have hw := invariant.words
      omega
    exact lt_trans (b := 2 ^ 64 + 1024 + 31) (by omega)
      (by norm_num [UInt256.size])
  have hcopy := finalCopy_coverage correction.memory correction.activeWords source target bytes
    (by rw [hbytes]; have hk := invariant.wordsPos; omega) hsource htarget
    hstate.1 hstate.2.1 haccess
  have hcopySize := finalCopyMemory_size correction.memory source target bytes
    (by rw [hbytes]; have hk := invariant.wordsPos; omega) hsource htarget
  have hframe : forall ptr words, 96 <= ptr -> ptr + 32 * words <= target.toNat ->
      memoryWordsFrom (finalCopyMemory correction.memory source target bytes) ptr words =
        memoryWordsFrom mem ptr words := by
    intro ptr words hptr hbelow
    have hfinal := memoryWordsFrom_finalCopy_below words correction.memory source target bytes ptr
      (by rw [hbytes]; have hk := invariant.wordsPos; omega) hsource
      (le_trans (by omega) htarget) (le_trans hbelow (le_trans (by omega) htarget)) hbelow
    rw [hfinal]
    have hselected := hstate.2.2.2 ptr words hptr (by
      rw [hrAdd] at hbelow
      have hr := invariant.rBeforeScratch
      omega)
    rw [hselected]
    exact memoryWordsFrom_barrettResetMemory_above mem fp ptr words hmem96 hptr
  have hheader : forall ptr (word : UInt256), 96 <= ptr -> ptr + 32 <= target.toNat ->
      mem.readWithPadding ptr 32 = word.toByteArray ->
      (finalCopyMemory correction.memory source target bytes).readWithPadding ptr 32 =
        word.toByteArray := by
    intro ptr word hptr hbelow horiginal
    apply readWithPadding_eq_toByteArray_of_memoryWordNat_eq
    have hwords := hframe ptr 1 hptr (by simpa using hbelow)
    have hword : UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
        (finalCopyMemory correction.memory source target bytes) ptr) =
        UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) := by
      simpa [memoryWordsFrom] using hwords
    apply hword.trans
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [horiginal, fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat word
  have hbaseWords := hframe (a.toNat + 32) kWords (by
    have ha := invariant.aBase; omega) (by
    rw [hrAdd]
    have ha := invariant.aBeforeR
    omega)
  have hnWords := hframe (n.toNat + 32) kWords (by
    have hn := invariant.nBase; omega) (by
    rw [hrAdd]
    have hn := invariant.nBeforeR
    omega)
  have hmuWords := hframe (mu.toNat + 32) (kWords + 2) (by
    have hmu := invariant.muBase; omega) (by
    rw [hrAdd]
    have hmu := invariant.muBeforeR
    omega)
  simpa only [exponentCopyMemory, exponentCopyAw, resultFp, source, target, bytes] using
    (show BarrettExponentInvariant I (finalCopyMemory correction.memory source target bytes)
      (finalCopyAw correction.activeWords source target bytes)
      kWords fp r a n mu (xValue * yValue % nValue) baseValue nValue from {
      wordsPos := invariant.wordsPos
      words := invariant.words
      scratchBound := invariant.scratchBound
      calldataBound := invariant.calldataBound
      freePointerBase := invariant.freePointerBase
      covered := hcopy.1
      activeWordsFit := hcopy.2
      scratchConcrete := by rw [hcopySize]; exact hstate.2.2.1
      rBase := invariant.rBase
      aBase := invariant.aBase
      nBase := invariant.nBase
      muBase := invariant.muBase
      aBeforeR := invariant.aBeforeR
      nBeforeR := invariant.nBeforeR
      muBeforeR := invariant.muBeforeR
      rBeforeScratch := invariant.rBeforeScratch
      rHeader := hheader r.toNat (UInt256.ofNat kWords) invariant.rBase (by
        rw [hrAdd]) invariant.rHeader
      aHeader := hheader a.toNat (UInt256.ofNat kWords) invariant.aBase (by
        rw [hrAdd]
        have ha := invariant.aBeforeR
        omega) invariant.aHeader
      nHeader := hheader n.toNat (UInt256.ofNat kWords) invariant.nBase (by
        rw [hrAdd]
        have hn := invariant.nBeforeR
        omega) invariant.nHeader
      muHeader := hheader mu.toNat (UInt256.ofNat (kWords + 2)) invariant.muBase (by
        rw [hrAdd]
        have hmu := invariant.muBeforeR
        omega) invariant.muHeader
      rValueEq := by
        simpa only [resultFp, source, target, bytes, exponentCopyMemory] using
          selectedBarrettCallAndCopy_value geometry
      baseValueEq := by rw [hbaseWords]; exact invariant.baseValueEq
      nValueEq := by rw [hnWords]; exact invariant.nValueEq
      muValueEq := by rw [hmuWords]; exact invariant.muValueEq
      nPos := invariant.nPos
      nNormalized := invariant.nNormalized
      nFits := invariant.nFits })

theorem BarrettSquareValid.value
    {I : ExecutionEnv} {fuel kWords fp : Nat} {mem : ByteArray} {aw r n mu : UInt256}
    {selected : BarrettSquareSelection} {rValue nValue : Nat}
    (valid : BarrettSquareValid I fuel mem aw kWords fp r n mu selected)
    (geometry : BarrettSquareSemanticGeometry I fuel mem aw kWords fp r n mu selected
      rValue nValue) :
    barrettAccumulatorValue kWords r selected.memory = rValue * rValue % nValue := by
  have hselection := valid.selection
  unfold selectBarrettSquare at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      unfold selectBarrettExponentCall at hc
      cases hr : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => simp [hr] at hc
      | some correction =>
          simp only [hr, Option.some.injEq] at hc
          subst call
          simpa using selectedBarrettCallAndCopy_value geometry.call

theorem BarrettMultiplyValid.value
    {I : ExecutionEnv} {fuel kWords fp : Nat} {mem : ByteArray} {aw r a n mu : UInt256}
    {selected : BarrettMultiplySelection} {rValue baseValue nValue : Nat}
    (valid : BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected)
    (geometry : BarrettMultiplySemanticGeometry I fuel mem aw kWords fp r a n mu selected
      rValue baseValue nValue) :
    barrettAccumulatorValue kWords r selected.memory = rValue * baseValue % nValue := by
  have hselection := valid.selection
  unfold selectBarrettMultiply at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r a n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      unfold selectBarrettExponentCall at hc
      cases hr : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r a n mu fp kWords with
      | none => simp [hr] at hc
      | some correction =>
          simp only [hr, Option.some.injEq] at hc
          subst call
          simpa using selectedBarrettCallAndCopy_value geometry.call

/-- A selected square advances the persistent accumulator and preserves the next-call state. -/
theorem BarrettExponentInvariant.afterSquare
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettSquareSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettSquareValid I fuel mem aw kWords fp r n mu selected) :
    BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
      (rValue * rValue % nValue) baseValue nValue := by
  have geometry := invariant.squareGeometry valid
  have hselection := valid.selection
  unfold selectBarrettSquare at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r r n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      unfold selectBarrettExponentCall at hc
      cases hr : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r r n mu fp kWords with
      | none => simp [hr] at hc
      | some correction =>
          simp only [hr, Option.some.injEq] at hc
          subst call
          exact invariant.afterCall geometry.call

/-- A selected multiply advances the persistent accumulator and preserves the next-call state. -/
theorem BarrettExponentInvariant.afterMultiply
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu : UInt256} {selected : BarrettMultiplySelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (valid : BarrettMultiplyValid I fuel mem aw kWords fp r a n mu selected) :
    BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
      (rValue * baseValue % nValue) baseValue nValue := by
  have geometry := invariant.multiplyGeometry valid
  have hselection := valid.selection
  unfold selectBarrettMultiply at hselection
  cases hc : selectBarrettExponentCall fuel
      (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
      r a n mu r fp kWords with
  | none => simp [hc] at hselection
  | some call =>
      simp only [hc, Option.some.injEq] at hselection
      subst selected
      unfold selectBarrettExponentCall at hc
      cases hr : Modexp.MultiLimbBarrettReusedCall.selectCall fuel
          (barrettResetMemory mem (UInt256.ofNat fp)) (barrettResetAw aw)
          r a n mu fp kWords with
      | none => simp [hr] at hc
      | some correction =>
          simp only [hr, Option.some.injEq] at hc
          subst call
          exact invariant.afterCall geometry.call

/-- The executable bit selector carries its own validity and persistent arithmetic state.  No
external square/multiply geometry provider is needed once the initial invariant is available. -/
theorem selectBarrettBitLoop_validInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettBitLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hselect : selectBarrettBitLoop bitFuel callFuel mem aw kWords fp
      bit byte r a n mu = some selected) :
    exists finalValue,
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  induction bitFuel generalizing mem aw bit selected rValue with
  | zero =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw, invariant⟩
      · simp [hbit] at hselect
  | succ bitFuel ih =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw, invariant⟩
      · simp only [hbit, ↓reduceIte] at hselect
        cases hsquare : selectBarrettSquare callFuel mem aw kWords fp r n mu with
        | none => simp [hsquare] at hselect
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            have squareValid := invariant.squareValid hsquare
            have squareInvariant := invariant.afterSquare squareValid
            by_cases hunset : ((⟨1⟩ : UInt256).land
                ((byte.land ⟨255⟩).shiftRight previousBit)).eq ⟨1⟩ = ⟨0⟩
            · cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
                  square.activeWords kWords fp previousBit byte r a n mu with
              | none => simp [hsquare, previousBit, hunset, hrest] at hselect
              | some rest =>
                  simp only [hsquare, previousBit, hunset, if_true, hrest,
                    Option.some.injEq] at hselect
                  subst selected
                  rcases ih squareInvariant hrest with ⟨finalValue, restValid, finalInvariant⟩
                  exact ⟨finalValue, .unset hbit squareValid hunset restValid,
                    finalInvariant⟩
            · cases hmultiply : selectBarrettMultiply callFuel square.memory
                  square.activeWords kWords fp r a n mu with
              | none => simp [hsquare, previousBit, hunset, hmultiply] at hselect
              | some multiply =>
                  have multiplyValid := squareInvariant.multiplyValid hmultiply
                  have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
                  cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
                      multiply.activeWords kWords fp previousBit byte r a n mu with
                  | none =>
                      simp [hsquare, previousBit, hunset, hmultiply, hrest] at hselect
                  | some rest =>
                      simp only [hsquare, previousBit, hunset, if_false, hmultiply, hrest,
                        Option.some.injEq] at hselect
                      subst selected
                      rcases ih multiplyInvariant hrest with
                        ⟨finalValue, restValid, finalInvariant⟩
                      exact ⟨finalValue,
                        .set hbit squareValid multiplyValid hunset restValid,
                        finalInvariant⟩

/-- The executable bit loop preserves any persistent word below the accumulator while carrying
the same validity and arithmetic invariant as `selectBarrettBitLoop_validInvariant`. -/
theorem selectBarrettBitLoop_validInvariantReadBelow
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettBitLoopSelection} {read : Nat}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hselect : selectBarrettBitLoop bitFuel callFuel mem aw kWords fp
      bit byte r a n mu = some selected) :
    exists finalValue,
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction bitFuel generalizing mem aw bit selected rValue with
  | zero =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw, invariant, rfl⟩
      · simp [hbit] at hselect
  | succ bitFuel ih =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw, invariant, rfl⟩
      · simp only [hbit, ↓reduceIte] at hselect
        cases hsquare : selectBarrettSquare callFuel mem aw kWords fp r n mu with
        | none => simp [hsquare] at hselect
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            have squareValid := invariant.squareValid hsquare
            have squareInvariant := invariant.afterSquare squareValid
            have squareFrame := invariant.readBelowSquare squareValid hread hbelow
            by_cases hunset : ((⟨1⟩ : UInt256).land
                ((byte.land ⟨255⟩).shiftRight previousBit)).eq ⟨1⟩ = ⟨0⟩
            · cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
                  square.activeWords kWords fp previousBit byte r a n mu with
              | none => simp [hsquare, previousBit, hunset, hrest] at hselect
              | some rest =>
                  simp only [hsquare, previousBit, hunset, if_true, hrest,
                    Option.some.injEq] at hselect
                  subst selected
                  rcases ih squareInvariant hrest with
                    ⟨finalValue, restValid, finalInvariant, restFrame⟩
                  exact ⟨finalValue, .unset hbit squareValid hunset restValid,
                    finalInvariant, restFrame.trans squareFrame⟩
            · cases hmultiply : selectBarrettMultiply callFuel square.memory
                  square.activeWords kWords fp r a n mu with
              | none => simp [hsquare, previousBit, hunset, hmultiply] at hselect
              | some multiply =>
                  have multiplyValid := squareInvariant.multiplyValid hmultiply
                  have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
                  have multiplyFrame := squareInvariant.readBelowMultiply multiplyValid
                    hread hbelow
                  cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
                      multiply.activeWords kWords fp previousBit byte r a n mu with
                  | none =>
                      simp [hsquare, previousBit, hunset, hmultiply, hrest] at hselect
                  | some rest =>
                      simp only [hsquare, previousBit, hunset, if_false, hmultiply, hrest,
                        Option.some.injEq] at hselect
                      subst selected
                      rcases ih multiplyInvariant hrest with
                        ⟨finalValue, restValid, finalInvariant, restFrame⟩
                      exact ⟨finalValue,
                        .set hbit squareValid multiplyValid hunset restValid,
                        finalInvariant,
                        (restFrame.trans multiplyFrame).trans squareFrame⟩

/-- Set/unset decisions made by the selected Barrett loop, in deployed order. -/
def barrettBitLoopDecisions : BarrettBitLoopSelection → List Bool
  | .done _ _ => []
  | .unset _ rest => false :: barrettBitLoopDecisions rest
  | .set _ _ rest => true :: barrettBitLoopDecisions rest

/-- The executable selector's final accumulator is the pure MSB scan, derived from the carried
invariant at each concrete square and multiply rather than from geometry callbacks. -/
theorem selectBarrettBitLoop_valueInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettBitLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hselect : selectBarrettBitLoop bitFuel callFuel mem aw kWords fp
      bit byte r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx } (barrettBitLoopDecisions selected)).value := by
  induction bitFuel generalizing mem aw bit selected rValue pfx with
  | zero =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettBitLoopSelection.memory, barrettBitLoopDecisions,
          invariant.rValueEq]
      · simp [hbit] at hselect
  | succ bitFuel ih =>
      rw [selectBarrettBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettBitLoopSelection.memory, barrettBitLoopDecisions,
          invariant.rValueEq]
      · simp only [hbit, ↓reduceIte] at hselect
        cases hsquare : selectBarrettSquare callFuel mem aw kWords fp r n mu with
        | none => simp [hsquare] at hselect
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            have squareValid := invariant.squareValid hsquare
            have squareGeometry := invariant.squareGeometry squareValid
            have squareInvariant := invariant.afterSquare squareValid
            by_cases hunset : ((⟨1⟩ : UInt256).land
                ((byte.land ⟨255⟩).shiftRight previousBit)).eq ⟨1⟩ = ⟨0⟩
            · cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
                  square.activeWords kWords fp previousBit byte r a n mu with
              | none => simp [hsquare, previousBit, hunset, hrest] at hselect
              | some rest =>
                  simp only [hsquare, previousBit, hunset, if_true, hrest,
                    Option.some.injEq] at hselect
                  subst selected
                  simp only [BarrettBitLoopSelection.memory, barrettBitLoopDecisions,
                    Modexp.msbPowScan]
                  rw [ih (pfx := 2 * pfx) squareInvariant hrest]
                  simp
            · cases hmultiply : selectBarrettMultiply callFuel square.memory
                  square.activeWords kWords fp r a n mu with
              | none => simp [hsquare, previousBit, hunset, hmultiply] at hselect
              | some multiply =>
                  have multiplyValid := squareInvariant.multiplyValid hmultiply
                  have multiplyGeometry := squareInvariant.multiplyGeometry multiplyValid
                  have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
                  cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
                      multiply.activeWords kWords fp previousBit byte r a n mu with
                  | none =>
                      simp [hsquare, previousBit, hunset, hmultiply, hrest] at hselect
                  | some rest =>
                      simp only [hsquare, previousBit, hunset, if_false, hmultiply, hrest,
                        Option.some.injEq] at hselect
                      subst selected
                      simp only [BarrettBitLoopSelection.memory, barrettBitLoopDecisions,
                        Modexp.msbPowScan]
                      rw [ih (pfx := 2 * pfx + 1) multiplyInvariant hrest]
                      simp

/-- The branch sequence is exactly the descending low-byte bit sequence inspected by the
deployed shift/mask code. -/
theorem BarrettBitLoopValid.decisions_eq
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu byte bit : UInt256}
    {mem : ByteArray} {aw : UInt256} {selected : BarrettBitLoopSelection}
    (valid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected) :
    barrettBitLoopDecisions selected =
      exponentBitDecisions (byte.land ⟨255⟩) bit.toNat := by
  induction valid with
  | done => rfl
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      have hpos : 0 < bit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply bitNonzero
        apply u256_inj
        simpa using hz
      obtain ⟨previous, hbit⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : bit.toNat ≠ 0)
      have hprevious : (UInt256.lnot ⟨0⟩ + bit).toNat = previous := by
        rw [previousBit_toNat bitNonzero, hbit]
        simp
      have hword : UInt256.ofNat previous = UInt256.lnot ⟨0⟩ + bit := by
        rw [← hprevious]
        exact u256_ofNat_toNat _
      have bitUnset' :
          ((((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq
            ⟨1⟩) = ⟨0⟩ := by
        simpa only [u256_land_comm (⟨1⟩ : UInt256)
          ((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit))] using bitUnset
      have hunset : ¬ (((((byte.land ⟨255⟩).shiftRight (UInt256.ofNat previous)).land
          ⟨1⟩).eq ⟨1⟩) ≠ ⟨0⟩) := by
        rw [hword]
        exact fun hne => hne bitUnset'
      simp only [barrettBitLoopDecisions, hbit, exponentBitDecisions,
        exponentBitDecision, hunset, decide_false, List.cons.injEq, true_and]
      simpa [hprevious] using ih
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      have hpos : 0 < bit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply bitNonzero
        apply u256_inj
        simpa using hz
      obtain ⟨previous, hbit⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : bit.toNat ≠ 0)
      have hprevious : (UInt256.lnot ⟨0⟩ + bit).toNat = previous := by
        rw [previousBit_toNat bitNonzero, hbit]
        simp
      have hword : UInt256.ofNat previous = UInt256.lnot ⟨0⟩ + bit := by
        rw [← hprevious]
        exact u256_ofNat_toNat _
      have bitSet' :
          ((((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq
            ⟨1⟩) ≠ ⟨0⟩ := by
        simpa only [u256_land_comm (⟨1⟩ : UInt256)
          ((byte.land ⟨255⟩).shiftRight (UInt256.lnot ⟨0⟩ + bit))] using bitSet
      have hset : ((((byte.land ⟨255⟩).shiftRight (UInt256.ofNat previous)).land
          ⟨1⟩).eq ⟨1⟩) ≠ ⟨0⟩ := by
        rw [hword]
        exact bitSet'
      have hdecision : exponentBitDecision (byte.land ⟨255⟩) previous = true := by
        unfold exponentBitDecision
        simp [hset]
      rw [barrettBitLoopDecisions, hbit, exponentBitDecisions, hdecision]
      simp only [List.cons.injEq, true_and]
      simpa [hprevious] using ih

/-- Once the selected calls have their arithmetic contracts, the recursive Barrett loop is the
backend-independent MSB-first power scan. -/
theorem BarrettBitLoopValid.value_eq_msbPowScan
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu byte bit : UInt256}
    {mem : ByteArray} {aw : UInt256} {selected : BarrettBitLoopSelection}
    (valid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected)
    (modulus base pfx : Nat)
    (hsquare : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.unset square rest) →
      BarrettSquareSemanticGeometry I callFuel mem' aw' kWords fp r n mu square
        (barrettAccumulatorValue kWords r mem') modulus)
    (hsquareSet : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {multiply : BarrettMultiplySelection}
      {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.set square multiply rest) →
      BarrettSquareSemanticGeometry I callFuel mem' aw' kWords fp r n mu square
        (barrettAccumulatorValue kWords r mem') modulus)
    (hmultiply : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {multiply : BarrettMultiplySelection}
      {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.set square multiply rest) →
      BarrettMultiplySemanticGeometry I callFuel square.memory square.activeWords
        kWords fp r a n mu multiply
        (barrettAccumulatorValue kWords r square.memory) base modulus) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % modulus) base
        { value := barrettAccumulatorValue kWords r mem, exponent := pfx }
        (barrettBitLoopDecisions selected)).value := by
  induction valid generalizing pfx with
  | done => rfl
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      simp only [BarrettBitLoopSelection.memory, barrettBitLoopDecisions, Modexp.msbPowScan]
      rw [← squareValid.value (hsquare (.unset bitNonzero squareValid bitUnset restValid))]
      exact ih (2 * pfx)
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      simp only [BarrettBitLoopSelection.memory, barrettBitLoopDecisions, Modexp.msbPowScan]
      rw [← squareValid.value
        (hsquareSet (.set bitNonzero squareValid multiplyValid bitSet restValid))]
      rw [← multiplyValid.value
        (hmultiply (.set bitNonzero squareValid multiplyValid bitSet restValid))]
      exact ih (2 * pfx + 1)

theorem BarrettBitLoopValid.value_eq_pow
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu byte bit : UInt256}
    {mem : ByteArray} {aw : UInt256} {selected : BarrettBitLoopSelection}
    (valid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected)
    (modulus base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ pfx % modulus)
    (hsquare : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.unset square rest) →
      BarrettSquareSemanticGeometry I callFuel mem' aw' kWords fp r n mu square
        (barrettAccumulatorValue kWords r mem') modulus)
    (hsquareSet : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {multiply : BarrettMultiplySelection}
      {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.set square multiply rest) →
      BarrettSquareSemanticGeometry I callFuel mem' aw' kWords fp r n mu square
        (barrettAccumulatorValue kWords r mem') modulus)
    (hmultiply : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : BarrettSquareSelection} {multiply : BarrettMultiplySelection}
      {rest : BarrettBitLoopSelection},
      BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem' aw' bit'
        (.set square multiply rest) →
      BarrettMultiplySemanticGeometry I callFuel square.memory square.activeWords
        kWords fp r a n mu multiply
        (barrettAccumulatorValue kWords r square.memory) base modulus) :
    barrettAccumulatorValue kWords r selected.memory =
      base ^ ((barrettBitLoopDecisions selected).foldl
        (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  rw [valid.value_eq_msbPowScan modulus base pfx hsquare hsquareSet hmultiply]
  have hcorrect := Modexp.msbPowScan_correct id (fun x y => x * y % modulus) base
    modulus hmodulus (by intro x y; rfl)
    { value := barrettAccumulatorValue kWords r mem, exponent := pfx }
    (barrettBitLoopDecisions selected) hinitial
  rw [Modexp.msbPowScan_exponent] at hcorrect
  exact hcorrect

/-! ## Executable exponent-byte loop -/

structure BarrettByteSelection where
  byte : UInt256
  bits : BarrettBitLoopSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectBarrettByte (bitFuel callFuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (byteIdx exponent topBit r a n mu : UInt256) :
    Option BarrettByteSelection :=
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  match selectBarrettBitLoop bitFuel callFuel mem loadAw kWords fp
      (topBit + ⟨1⟩) byte r a n mu with
  | none => none
  | some bits => some {
      byte := byte
      bits := bits
      memory := bits.memory
      activeWords := bits.activeWords
      steps := bits.steps + 80
      gas := barrettExponentByteLoadGas aw exponent byteIdx + bits.gas + 64 }

/-- Loading one exponent byte is total whenever bit fuel bounds its selected top-bit counter. -/
theorem selectBarrettByte_exists
    {bitFuel callFuel kWords fp : Nat} {mem : ByteArray}
    {aw byteIdx exponent topBit r a n mu : UInt256}
    (hkPos : 0 < kWords) (hcallFuel : kWords ≤ callFuel)
    (hbitFuel : (topBit + ⟨1⟩).toNat ≤ bitFuel) :
    ∃ selected,
      selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
        r a n mu = some selected := by
  rcases selectBarrettBitLoop_exists (mem := mem)
    (aw := exponentByteLoadAw aw exponent byteIdx) (bit := topBit + ⟨1⟩)
    (byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
      exponent byteIdx)
    (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
    hkPos hcallFuel hbitFuel with ⟨bits, hbits⟩
  simp [selectBarrettByte, hbits]

structure BarrettByteValid (I : ExecutionEnv) (callFuel : Nat) (kWords fp : Nat)
    (r a n mu : UInt256) (mem : ByteArray) (aw byteIdx exponent topBit expLen : UInt256)
    (selected : BarrettByteSelection) : Prop where
  guardTaken : byteIdx.lt expLen ≠ ⟨0⟩
  indexValid : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩
  topBitValid : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩
  byteEq : selected.byte =
    barrettExponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx
  bitsValid : BarrettBitLoopValid I callFuel kWords fp r a n mu selected.byte
    mem (exponentByteLoadAw aw exponent byteIdx) (topBit + ⟨1⟩) selected.bits
  memoryEq : selected.memory = selected.bits.memory
  activeWordsEq : selected.activeWords = selected.bits.activeWords
  stepsEq : selected.steps = selected.bits.steps + 80
  gasEq : selected.gas =
    barrettExponentByteLoadGas aw exponent byteIdx + selected.bits.gas + 64

theorem selectBarrettByte_valid
    {I : ExecutionEnv} {bitFuel callFuel kWords fp : Nat} {r a n mu : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : BarrettByteSelection}
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hbitsValid : ∀ (bits : BarrettBitLoopSelection),
      selectBarrettBitLoop bitFuel callFuel mem (exponentByteLoadAw aw exponent byteIdx)
        kWords fp (topBit + ⟨1⟩)
        (barrettExponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx)
        r a n mu = some bits →
      BarrettBitLoopValid I callFuel kWords fp r a n mu
        (barrettExponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx)
        mem (exponentByteLoadAw aw exponent byteIdx) (topBit + ⟨1⟩) bits)
    (hselect : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
      r a n mu = some selected) :
    BarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent topBit expLen
      selected := by
  unfold selectBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hbits : selectBarrettBitLoop bitFuel callFuel mem loadAw kWords fp
      (topBit + ⟨1⟩) byte r a n mu with
  | none => simpa [lengthAw, byte, loadAw, hbits] using hselect
  | some bits =>
      have hselected : selected = {
          byte := byte
          bits := bits
          memory := bits.memory
          activeWords := bits.activeWords
          steps := bits.steps + 80
          gas := barrettExponentByteLoadGas aw exponent byteIdx + bits.gas + 64 } := by
        simpa [lengthAw, byte, loadAw, hbits] using hselect.symm
      subst selected
      exact {
        guardTaken := hguard
        indexValid := hindex
        topBitValid := htop
        byteEq := by rfl
        bitsValid := hbitsValid bits (by simpa [lengthAw, byte, loadAw] using hbits)
        memoryEq := by rfl
        activeWordsEq := by rfl
        stepsEq := by rfl
        gasEq := by rfl }

/-- A selected exponent byte is valid from the arithmetic invariant plus only the checked-array
and non-wrapping MLOAD geometry of that Solidity byte access. -/
theorem selectBarrettByte_validInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256} {selected : BarrettByteSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
      r a n mu = some selected) :
    exists finalValue,
      BarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent topBit expLen
          selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  unfold selectBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hbits : selectBarrettBitLoop bitFuel callFuel mem loadAw kWords fp
      (topBit + ⟨1⟩) byte r a n mu with
  | none => simpa [lengthAw, byte, loadAw, hbits] using hselect
  | some bits =>
      have hselected : selected = {
          byte := byte
          bits := bits
          memory := bits.memory
          activeWords := bits.activeWords
          steps := bits.steps + 80
          gas := barrettExponentByteLoadGas aw exponent byteIdx + bits.gas + 64 } := by
        simpa [lengthAw, byte, loadAw, hbits] using hselect.symm
      subst selected
      have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
      rcases selectBarrettBitLoop_validInvariant loadInvariant
          (by simpa [lengthAw, byte, loadAw] using hbits) with
        ⟨finalValue, bitsValid, finalInvariant⟩
      exact ⟨finalValue, {
        guardTaken := hguard
        indexValid := hindex
        topBitValid := htop
        byteEq := by rfl
        bitsValid := bitsValid
        memoryEq := by rfl
        activeWordsEq := by rfl
        stepsEq := by rfl
        gasEq := by rfl }, finalInvariant⟩

/-- One selected byte also preserves any fixed persistent word below the accumulator. -/
theorem selectBarrettByte_validInvariantReadBelow
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256} {selected : BarrettByteSelection}
    {read : Nat}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hselect : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
      r a n mu = some selected) :
    exists finalValue,
      BarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent topBit expLen
          selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold selectBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hbits : selectBarrettBitLoop bitFuel callFuel mem loadAw kWords fp
      (topBit + ⟨1⟩) byte r a n mu with
  | none => simpa [lengthAw, byte, loadAw, hbits] using hselect
  | some bits =>
      have hselected : selected = {
          byte := byte
          bits := bits
          memory := bits.memory
          activeWords := bits.activeWords
          steps := bits.steps + 80
          gas := barrettExponentByteLoadGas aw exponent byteIdx + bits.gas + 64 } := by
        simpa [lengthAw, byte, loadAw, hbits] using hselect.symm
      subst selected
      have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
      rcases selectBarrettBitLoop_validInvariantReadBelow loadInvariant hread hbelow
          (by simpa [lengthAw, byte, loadAw] using hbits) with
        ⟨finalValue, bitsValid, finalInvariant, frame⟩
      exact ⟨finalValue, {
        guardTaken := hguard
        indexValid := hindex
        topBitValid := htop
        byteEq := by rfl
        bitsValid := bitsValid
        memoryEq := by rfl
        activeWordsEq := by rfl
        stepsEq := by rfl
        gasEq := by rfl }, finalInvariant, frame⟩

/-- One selected byte has exactly the pure MSB-scan value, with its MLOAD assumptions kept
separate from the modular arithmetic proof. -/
theorem selectBarrettByte_valueInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit : UInt256} {selected : BarrettByteSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
      r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx }
        (barrettBitLoopDecisions selected.bits)).value := by
  unfold selectBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hbits : selectBarrettBitLoop bitFuel callFuel mem loadAw kWords fp
      (topBit + ⟨1⟩) byte r a n mu with
  | none => simpa [lengthAw, byte, loadAw, hbits] using hselect
  | some bits =>
      have hselected : selected = {
          byte := byte
          bits := bits
          memory := bits.memory
          activeWords := bits.activeWords
          steps := bits.steps + 80
          gas := barrettExponentByteLoadGas aw exponent byteIdx + bits.gas + 64 } := by
        simpa [lengthAw, byte, loadAw, hbits] using hselect.symm
      subst selected
      have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
      exact selectBarrettBitLoop_valueInvariant (pfx := pfx) loadInvariant
        (by simpa [lengthAw, byte, loadAw] using hbits)

theorem validBarrettByteExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu : UInt256} {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : BarrettByteSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : BarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent topBit
      expLen selected)
    (hdepth : tail.length + 36 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have rd3323 := barrettByteGuardTaken (by omega) valid.guardTaken h
  have rd3364 := barrettExponentByteLoadToBitGuardExact (by omega) valid.indexValid
    valid.topBitValid rd3323
  have bitsValid := valid.bitsValid
  rw [valid.byteEq] at bitsValid
  have rdDone := validBarrettBitLoopExact bitsValid hdepth (by simpa using rd3364)
  have rd3304 := barrettBitGuardExitToByteGuard (by omega) rdDone
  have normalized := rd3304.withIndices (k' := steps + selected.steps) (by
      rw [valid.stepsEq]
      omega)
    (C' := gasUsed + selected.gas) (by
      rw [valid.gasEq]
      omega)
  simpa [valid.memoryEq, valid.activeWordsEq] using normalized

/-! ## First nonzero exponent byte

The leading scan proves that `topBit` is set.  We expose that first iteration separately so its
square can use fresh scratch; after the mandatory multiply, the ordinary recursive selector
handles the remaining lower bits. -/

structure InitialBarrettByteSelection where
  byte : UInt256
  square : BarrettSquareSelection
  multiply : BarrettMultiplySelection
  rest : BarrettBitLoopSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectInitialBarrettByte (bitFuel callFuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (byteIdx exponent topBit r a n mu : UInt256) :
    Option InitialBarrettByteSelection :=
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  match selectFreshBarrettSquare callFuel mem loadAw kWords fp r n mu with
  | none => none
  | some square =>
      match selectBarrettMultiply callFuel square.memory square.activeWords
          kWords fp r a n mu with
      | none => none
      | some multiply =>
          match selectBarrettBitLoop bitFuel callFuel multiply.memory multiply.activeWords
              kWords fp topBit byte r a n mu with
          | none => none
          | some rest => some {
              byte := byte
              square := square
              multiply := multiply
              rest := rest
              memory := rest.memory
              activeWords := rest.activeWords
              steps := square.steps + multiply.steps + rest.steps + 123
              gas := barrettExponentByteLoadGas aw exponent byteIdx + square.gas +
                multiply.gas + rest.gas + 203 }

theorem selectInitialBarrettByte_exists
    {bitFuel callFuel kWords fp : Nat} {mem : ByteArray}
    {aw byteIdx exponent topBit r a n mu : UInt256}
    (hkPos : 0 < kWords) (hcallFuel : kWords <= callFuel)
    (hbitFuel : topBit.toNat <= bitFuel) :
    exists selected,
      selectInitialBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
        r a n mu = some selected := by
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  rcases selectFreshBarrettSquare_exists (mem := mem) (aw := loadAw)
    (r := r) (n := n) (mu := mu) (fp := fp) hkPos hcallFuel with ⟨square, hsquare⟩
  rcases selectBarrettMultiply_exists (mem := square.memory) (aw := square.activeWords)
    (r := r) (a := a) (n := n) (mu := mu) (fp := fp) hkPos hcallFuel with
    ⟨multiply, hmultiply⟩
  rcases selectBarrettBitLoop_exists (mem := multiply.memory) (aw := multiply.activeWords)
    (bit := topBit)
    (byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
      exponent byteIdx)
    (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
    hkPos hcallFuel hbitFuel with ⟨rest, hrest⟩
  simp [selectInitialBarrettByte, loadAw, hsquare, hmultiply, hrest]

structure InitialBarrettByteValid (I : ExecutionEnv) (callFuel : Nat) (kWords fp : Nat)
    (r a n mu : UInt256) (mem : ByteArray) (aw byteIdx exponent topBit expLen : UInt256)
    (selected : InitialBarrettByteSelection) : Prop where
  guardTaken : byteIdx.lt expLen ≠ ⟨0⟩
  indexValid : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩
  topBitValid : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩
  bitCounterNonzero : topBit + ⟨1⟩ ≠ ⟨0⟩
  byteEq : selected.byte =
    barrettExponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx
  bitSet : ((⟨1⟩ : UInt256).land
    ((selected.byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ ≠ ⟨0⟩
  squareValid : FreshBarrettSquareValid I callFuel mem
    (exponentByteLoadAw aw exponent byteIdx) kWords fp r n mu selected.square
  multiplyValid : BarrettMultiplyValid I callFuel selected.square.memory
    selected.square.activeWords kWords fp r a n mu selected.multiply
  restValid : BarrettBitLoopValid I callFuel kWords fp r a n mu selected.byte
    selected.multiply.memory selected.multiply.activeWords topBit selected.rest
  memoryEq : selected.memory = selected.rest.memory
  activeWordsEq : selected.activeWords = selected.rest.activeWords
  stepsEq : selected.steps =
    selected.square.steps + selected.multiply.steps + selected.rest.steps + 123
  gasEq : selected.gas = barrettExponentByteLoadGas aw exponent byteIdx +
    selected.square.gas + selected.multiply.gas + selected.rest.gas + 203

theorem selectInitialBarrettByte_validInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256}
    {selected : InitialBarrettByteSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (hbitSet : ((⟨1⟩ : UInt256).land
      (((barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
        exponent byteIdx).land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ ≠ ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected) :
    exists finalValue,
      InitialBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  unfold selectInitialBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hsquare : selectFreshBarrettSquare callFuel mem loadAw kWords fp r n mu with
  | none => simpa [lengthAw, byte, loadAw, hsquare] using hselect
  | some square =>
      cases hmultiply : selectBarrettMultiply callFuel square.memory square.activeWords
          kWords fp r a n mu with
      | none => simpa [lengthAw, byte, loadAw, hsquare, hmultiply] using hselect
      | some multiply =>
          cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
              multiply.activeWords kWords fp topBit byte r a n mu with
          | none =>
              simpa [lengthAw, byte, loadAw, hsquare, hmultiply, hrest] using hselect
          | some rest =>
              have hselected : selected = {
                  byte := byte
                  square := square
                  multiply := multiply
                  rest := rest
                  memory := rest.memory
                  activeWords := rest.activeWords
                  steps := square.steps + multiply.steps + rest.steps + 123
                  gas := barrettExponentByteLoadGas aw exponent byteIdx + square.gas +
                    multiply.gas + rest.gas + 203 } := by
                simpa [lengthAw, byte, loadAw, hsquare, hmultiply, hrest] using hselect.symm
              subst selected
              have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
              have squareValid := loadInvariant.freshSquareValid (by
                simpa only [loadAw] using hsquare)
              have squareInvariant := loadInvariant.afterFreshSquare squareValid
              have multiplyValid := squareInvariant.multiplyValid hmultiply
              have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
              rcases selectBarrettBitLoop_validInvariant multiplyInvariant
                  (by simpa only [byte] using hrest) with
                ⟨finalValue, restValid, finalInvariant⟩
              exact ⟨finalValue, {
                guardTaken := hguard
                indexValid := hindex
                topBitValid := htop
                bitCounterNonzero := hcounter
                byteEq := by rfl
                bitSet := by simpa only [byte, lengthAw] using hbitSet
                squareValid := squareValid
                multiplyValid := multiplyValid
                restValid := restValid
                memoryEq := by rfl
                activeWordsEq := by rfl
                stepsEq := by rfl
                gasEq := by rfl }, finalInvariant⟩

/-- The first set exponent byte preserves a fixed persistent word through its fresh square,
mandatory multiply, and remaining bit loop. -/
theorem selectInitialBarrettByte_validInvariantReadBelow
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256}
    {selected : InitialBarrettByteSelection} {read : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (hbitSet : ((⟨1⟩ : UInt256).land
      (((barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
        exponent byteIdx).land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ ≠ ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hselect : selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected) :
    exists finalValue,
      InitialBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold selectInitialBarrettByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := barrettExponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hsquare : selectFreshBarrettSquare callFuel mem loadAw kWords fp r n mu with
  | none => simpa [lengthAw, byte, loadAw, hsquare] using hselect
  | some square =>
      cases hmultiply : selectBarrettMultiply callFuel square.memory square.activeWords
          kWords fp r a n mu with
      | none => simpa [lengthAw, byte, loadAw, hsquare, hmultiply] using hselect
      | some multiply =>
          cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
              multiply.activeWords kWords fp topBit byte r a n mu with
          | none =>
              simpa [lengthAw, byte, loadAw, hsquare, hmultiply, hrest] using hselect
          | some rest =>
              have hselected : selected = {
                  byte := byte
                  square := square
                  multiply := multiply
                  rest := rest
                  memory := rest.memory
                  activeWords := rest.activeWords
                  steps := square.steps + multiply.steps + rest.steps + 123
                  gas := barrettExponentByteLoadGas aw exponent byteIdx + square.gas +
                    multiply.gas + rest.gas + 203 } := by
                simpa [lengthAw, byte, loadAw, hsquare, hmultiply, hrest] using hselect.symm
              subst selected
              have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
              have squareValid := loadInvariant.freshSquareValid (by
                simpa only [loadAw] using hsquare)
              have squareInvariant := loadInvariant.afterFreshSquare squareValid
              have squareFrame := loadInvariant.readBelowFreshSquare squareValid hread hbelow
              have multiplyValid := squareInvariant.multiplyValid hmultiply
              have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
              have multiplyFrame := squareInvariant.readBelowMultiply multiplyValid
                hread hbelow
              rcases selectBarrettBitLoop_validInvariantReadBelow multiplyInvariant
                  hread hbelow (by simpa only [byte] using hrest) with
                ⟨finalValue, restValid, finalInvariant, restFrame⟩
              exact ⟨finalValue, {
                guardTaken := hguard
                indexValid := hindex
                topBitValid := htop
                bitCounterNonzero := hcounter
                byteEq := by rfl
                bitSet := by simpa only [byte, lengthAw] using hbitSet
                squareValid := squareValid
                multiplyValid := multiplyValid
                restValid := restValid
                memoryEq := by rfl
                activeWordsEq := by rfl
                stepsEq := by rfl
                gasEq := by rfl }, finalInvariant,
                (restFrame.trans multiplyFrame).trans squareFrame⟩

theorem validInitialBarrettByteExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu : UInt256} {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : InitialBarrettByteSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : InitialBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx
      exponent topBit expLen selected)
    (hdepth : tail.length + 36 <= 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  have rd3323 := barrettByteGuardTaken (by omega) valid.guardTaken h
  have rd3364 := barrettExponentByteLoadToBitGuardExact (by omega) valid.indexValid
    valid.topBitValid rd3323
  have rd3364' := rd3364
  rw [← valid.byteEq] at rd3364'
  have rd3379 := barrettBitGuardTaken (by omega) valid.bitCounterNonzero rd3364'
  let squareTail := selected.byte :: byteIdx :: exponent :: ⟨7⟩ :: mu ::
    UInt256.ofNat fp :: a :: UInt256.ofNat kWords :: expLen :: n :: r :: tail
  have rd3411 := validFreshBarrettSquareExact (tail := squareTail) valid.squareValid (by
    simp only [squareTail, List.length_cons]
    omega) (by
      simpa [barrettSquareStack, barrettBitFrame, squareTail] using rd3379)
  have hprevious : UInt256.lnot ⟨0⟩ + (topBit + ⟨1⟩) = topBit := by
    rw [u256_add_comm topBit (⟨1⟩ : UInt256), ← u256_add_assoc,
      show UInt256.lnot ⟨0⟩ + (⟨1⟩ : UInt256) = ⟨0⟩ by native_decide]
    apply u256_inj
    rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 by decide, zero_add]
    exact Nat.mod_eq_of_lt topBit.val.isLt
  rw [hprevious] at rd3411
  have rd3448 := barrettSetBitToMultiply (tail := tail) (by omega) valid.bitSet (by
    simpa [squareTail] using rd3411)
  let multiplyTail := topBit :: topBit :: selected.byte :: byteIdx :: exponent :: ⟨7⟩ :: mu ::
    UInt256.ofNat fp :: a :: UInt256.ofNat kWords :: expLen :: n :: r :: tail
  have rd3467 := validBarrettMultiplyExact (tail := multiplyTail) valid.multiplyValid (by
    simp only [multiplyTail, List.length_cons]
    omega) (by simpa [multiplyTail] using rd3448)
  have rdNext := barrettSetResultToGuard (tail := tail) (by omega) (by
    simpa [multiplyTail] using rd3467)
  have rdDone := validBarrettBitLoopExact valid.restValid hdepth (by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
  have rd3304 := barrettBitGuardExitToByteGuard (by omega) rdDone
  have normalized := rd3304.withIndices (k' := steps + selected.steps) (by
      rw [valid.stepsEq]
      omega)
    (C' := gasUsed + selected.gas) (by
      rw [valid.gasEq]
      omega)
  simpa [valid.memoryEq, valid.activeWordsEq] using normalized

inductive FreshBarrettByteSelection where
  | unset (byte : UInt256) (square : BarrettSquareSelection)
      (rest : BarrettBitLoopSelection)
  | set (selected : InitialBarrettByteSelection)

namespace FreshBarrettByteSelection

def memory : FreshBarrettByteSelection -> ByteArray
  | .unset _ _ rest => rest.memory
  | .set selected => selected.memory

def activeWords : FreshBarrettByteSelection -> UInt256
  | .unset _ _ rest => rest.activeWords
  | .set selected => selected.activeWords

def steps : FreshBarrettByteSelection -> Nat
  | .unset _ square rest => square.steps + rest.steps + 114
  | .set selected => selected.steps

def gas (aw exponent byteIdx : UInt256) : FreshBarrettByteSelection -> Nat
  | .unset _ square rest => barrettExponentByteLoadGas aw exponent byteIdx +
      square.gas + rest.gas + 173
  | .set selected => selected.gas

def byte : FreshBarrettByteSelection -> UInt256
  | .unset byte _ _ => byte
  | .set selected => selected.byte

end FreshBarrettByteSelection

def selectFreshBarrettByte (bitFuel callFuel : Nat) (mem : ByteArray) (aw : UInt256)
    (kWords fp : Nat) (byteIdx exponent topBit r a n mu : UInt256) :
    Option FreshBarrettByteSelection :=
  let byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
    exponent byteIdx
  if ((⟨1⟩ : UInt256).land ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩ then
    match selectFreshBarrettSquare callFuel mem (exponentByteLoadAw aw exponent byteIdx)
        kWords fp r n mu with
    | none => none
    | some square =>
        match selectBarrettBitLoop bitFuel callFuel square.memory square.activeWords
            kWords fp topBit byte r a n mu with
        | none => none
        | some rest => some (.unset byte square rest)
  else
    match selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
        byteIdx exponent topBit r a n mu with
    | none => none
    | some selected => some (.set selected)

theorem selectFreshBarrettByte_exists
    {bitFuel callFuel kWords fp : Nat} {mem : ByteArray}
    {aw byteIdx exponent topBit r a n mu : UInt256}
    (hkPos : 0 < kWords) (hcallFuel : kWords <= callFuel)
    (hbitFuel : topBit.toNat <= bitFuel) :
    exists selected, selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected := by
  let byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
    exponent byteIdx
  by_cases hunset : ((⟨1⟩ : UInt256).land
      ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩
  · rcases selectFreshBarrettSquare_exists
      (mem := mem) (aw := exponentByteLoadAw aw exponent byteIdx)
      (r := r) (n := n) (mu := mu) (fp := fp) hkPos hcallFuel with ⟨square, hsquare⟩
    rcases selectBarrettBitLoop_exists (mem := square.memory) (aw := square.activeWords)
      (bit := topBit) (byte := byte) (r := r) (a := a) (n := n) (mu := mu)
      (fp := fp) hkPos hcallFuel hbitFuel with ⟨rest, hrest⟩
    simp [selectFreshBarrettByte, byte, hunset, hsquare, hrest]
  · rcases selectInitialBarrettByte_exists (mem := mem) (aw := aw)
      (byteIdx := byteIdx) (exponent := exponent) (topBit := topBit)
      (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
      hkPos hcallFuel hbitFuel with ⟨selected, hselected⟩
    simp [selectFreshBarrettByte, byte, hunset, hselected]

inductive FreshBarrettByteValid (I : ExecutionEnv) (callFuel : Nat) (kWords fp : Nat)
    (r a n mu : UInt256) (mem : ByteArray) (aw byteIdx exponent topBit expLen : UInt256) :
    FreshBarrettByteSelection -> Prop where
  | unset {byte : UInt256} {square : BarrettSquareSelection}
      {rest : BarrettBitLoopSelection}
      (guardTaken : byteIdx.lt expLen ≠ ⟨0⟩)
      (indexValid : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
      (topBitValid : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
      (bitCounterNonzero : topBit + ⟨1⟩ ≠ ⟨0⟩)
      (byteEq : byte = barrettExponentByteValue mem
        (exponentArrayLengthAw aw exponent) exponent byteIdx)
      (bitUnset : ((⟨1⟩ : UInt256).land
        ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩)
      (squareValid : FreshBarrettSquareValid I callFuel mem
        (exponentByteLoadAw aw exponent byteIdx) kWords fp r n mu square)
      (restValid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte
        square.memory square.activeWords topBit rest) :
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen (.unset byte square rest)
  | set {selected : InitialBarrettByteSelection}
      (valid : InitialBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx
        exponent topBit expLen selected) :
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen (.set selected)

theorem FreshBarrettByteValid.guardTaken
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection}
    (valid : FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
      topBit expLen selected) :
    byteIdx.lt expLen ≠ ⟨0⟩ := by
  cases valid with
  | unset guardTaken => exact guardTaken
  | set valid => exact valid.guardTaken

theorem selectFreshBarrettByte_validInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected) :
    exists finalValue,
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  let byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
    exponent byteIdx
  by_cases hunset : ((⟨1⟩ : UInt256).land
      ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩
  · rw [selectFreshBarrettByte, if_pos hunset] at hselect
    cases hsquare : selectFreshBarrettSquare callFuel mem
        (exponentByteLoadAw aw exponent byteIdx) kWords fp r n mu with
    | none => simp [byte, hsquare] at hselect
    | some square =>
        cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
            square.activeWords kWords fp topBit byte r a n mu with
        | none => simp [byte, hsquare, hrest] at hselect
        | some rest =>
            simp only [byte, hsquare, hrest, Option.some.injEq] at hselect
            subst selected
            have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
            have squareValid := loadInvariant.freshSquareValid hsquare
            have squareInvariant := loadInvariant.afterFreshSquare squareValid
            rcases selectBarrettBitLoop_validInvariant squareInvariant hrest with
              ⟨finalValue, restValid, finalInvariant⟩
            exact ⟨finalValue, .unset hguard hindex htop hcounter rfl hunset
              squareValid restValid, finalInvariant⟩
  · rw [selectFreshBarrettByte, if_neg hunset] at hselect
    cases hset : selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
        byteIdx exponent topBit r a n mu with
    | none => simp [hset] at hselect
    | some initial =>
        simp only [hset, Option.some.injEq] at hselect
        subst selected
        rcases selectInitialBarrettByte_validInvariant invariant hguard hindex htop hcounter
            (by simpa only [byte] using hunset) hexponentFit hbyteFit hset with
          ⟨finalValue, initialValid, finalInvariant⟩
        exact ⟨finalValue, .set initialValid, finalInvariant⟩

/-- The first selected byte preserves a fixed persistent word in both its set and unset paths. -/
theorem selectFreshBarrettByte_validInvariantReadBelow
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection} {read : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hselect : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected) :
    exists finalValue,
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
    exponent byteIdx
  by_cases hunset : ((⟨1⟩ : UInt256).land
      ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩
  · rw [selectFreshBarrettByte, if_pos hunset] at hselect
    cases hsquare : selectFreshBarrettSquare callFuel mem
        (exponentByteLoadAw aw exponent byteIdx) kWords fp r n mu with
    | none => simp [byte, hsquare] at hselect
    | some square =>
        cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
            square.activeWords kWords fp topBit byte r a n mu with
        | none => simp [byte, hsquare, hrest] at hselect
        | some rest =>
            simp only [byte, hsquare, hrest, Option.some.injEq] at hselect
            subst selected
            have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
            have squareValid := loadInvariant.freshSquareValid hsquare
            have squareInvariant := loadInvariant.afterFreshSquare squareValid
            have squareFrame := loadInvariant.readBelowFreshSquare squareValid hread hbelow
            rcases selectBarrettBitLoop_validInvariantReadBelow squareInvariant hread hbelow
                hrest with ⟨finalValue, restValid, finalInvariant, restFrame⟩
            exact ⟨finalValue, .unset hguard hindex htop hcounter rfl hunset
              squareValid restValid, finalInvariant, restFrame.trans squareFrame⟩
  · rw [selectFreshBarrettByte, if_neg hunset] at hselect
    cases hset : selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
        byteIdx exponent topBit r a n mu with
    | none => simp [hset] at hselect
    | some initial =>
        simp only [hset, Option.some.injEq] at hselect
        subst selected
        rcases selectInitialBarrettByte_validInvariantReadBelow invariant hguard hindex htop
            hcounter (by simpa only [byte] using hunset) hexponentFit hbyteFit hread hbelow
            hset with ⟨finalValue, initialValid, finalInvariant, frame⟩
        exact ⟨finalValue, .set initialValid, finalInvariant, frame⟩

theorem validFreshBarrettByteExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu : UInt256} {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx
      exponent topBit expLen selected)
    (hdepth : tail.length + 36 <= 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas aw exponent byteIdx) := by
  cases valid with
  | set initialValid =>
      simpa [FreshBarrettByteSelection.memory, FreshBarrettByteSelection.activeWords,
        FreshBarrettByteSelection.steps, FreshBarrettByteSelection.gas] using
        validInitialBarrettByteExact initialValid hdepth h
  | @unset byte square rest guardTaken indexValid topBitValid bitCounterNonzero byteEq
      bitUnset squareValid restValid =>
      have rd3323 := barrettByteGuardTaken (by omega) guardTaken h
      have rd3364 := barrettExponentByteLoadToBitGuardExact (by omega) indexValid
        topBitValid rd3323
      rw [← byteEq] at rd3364
      have rd3379 := barrettBitGuardTaken (by omega) bitCounterNonzero rd3364
      let squareTail := byte :: byteIdx :: exponent :: ⟨7⟩ :: mu :: UInt256.ofNat fp ::
        a :: UInt256.ofNat kWords :: expLen :: n :: r :: tail
      have rd3411 := validFreshBarrettSquareExact (tail := squareTail) squareValid (by
        simp only [squareTail, List.length_cons]
        omega) (by simpa [barrettSquareStack, barrettBitFrame, squareTail] using rd3379)
      have hprevious : UInt256.lnot ⟨0⟩ + (topBit + ⟨1⟩) = topBit := by
        rw [u256_add_comm topBit (⟨1⟩ : UInt256), ← u256_add_assoc,
          show UInt256.lnot ⟨0⟩ + (⟨1⟩ : UInt256) = ⟨0⟩ by native_decide]
        apply u256_inj
        rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 by decide, zero_add]
        exact Nat.mod_eq_of_lt topBit.val.isLt
      rw [hprevious] at rd3411
      have rdNext := barrettUnsetBitToGuard (tail := tail) (by omega) bitUnset (by
        simpa [squareTail] using rd3411)
      have rdDone := validBarrettBitLoopExact restValid hdepth (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      have rd3304 := barrettBitGuardExitToByteGuard (by omega) rdDone
      have normalized := rd3304.withIndices
        (k' := steps + (FreshBarrettByteSelection.unset byte square rest).steps) (by
          simp [FreshBarrettByteSelection.steps]
          omega)
        (C' := gasUsed +
          (FreshBarrettByteSelection.unset byte square rest).gas aw exponent byteIdx) (by
          simp [FreshBarrettByteSelection.gas]
          omega)
      simpa [FreshBarrettByteSelection.memory, FreshBarrettByteSelection.activeWords] using
        normalized

/-- Decisions made by the first significant byte. Its current top bit is handled by the fresh
square branch; the ordinary bit-loop selection records every lower bit. -/
def freshBarrettByteDecisions : FreshBarrettByteSelection -> List Bool
  | .unset _ _ rest => false :: barrettBitLoopDecisions rest
  | .set selected => true :: barrettBitLoopDecisions selected.rest

/-- The fresh first-byte branch plus its reused lower-bit loop records exactly the descending
bits from `topBit` through zero of the selected exponent byte. -/
theorem FreshBarrettByteValid.decisions_eq
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection}
    (valid : FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
      topBit expLen selected)
    (htop : topBit.toNat < 8) :
    freshBarrettByteDecisions selected =
      exponentBitDecisions (selected.byte.land ⟨255⟩) (topBit.toNat + 1) := by
  have hword : UInt256.ofNat topBit.toNat = topBit := u256_ofNat_toNat topBit
  cases valid with
  | @unset byte square rest guardTaken indexValid topBitValid bitCounterNonzero byteEq
      bitUnset squareValid restValid =>
      have bitUnset' :
          ((((byte.land ⟨255⟩).shiftRight topBit).land ⟨1⟩).eq ⟨1⟩) = ⟨0⟩ := by
        simpa only [u256_land_comm (⟨1⟩ : UInt256)
          ((byte.land ⟨255⟩).shiftRight topBit)] using bitUnset
      have hunset : ¬ (((((byte.land ⟨255⟩).shiftRight
          (UInt256.ofNat topBit.toNat)).land ⟨1⟩).eq ⟨1⟩) ≠ ⟨0⟩) := by
        rw [hword]
        exact fun hne => hne bitUnset'
      simp only [FreshBarrettByteSelection.byte, freshBarrettByteDecisions,
        exponentBitDecisions, exponentBitDecision, hunset, decide_false, List.cons.injEq,
        true_and]
      exact restValid.decisions_eq
  | @set initial valid =>
      have bitSet' :
          ((((initial.byte.land ⟨255⟩).shiftRight topBit).land ⟨1⟩).eq ⟨1⟩) ≠ ⟨0⟩ := by
        simpa only [u256_land_comm (⟨1⟩ : UInt256)
          ((initial.byte.land ⟨255⟩).shiftRight topBit)] using valid.bitSet
      have hset : ((((initial.byte.land ⟨255⟩).shiftRight
          (UInt256.ofNat topBit.toNat)).land ⟨1⟩).eq ⟨1⟩) ≠ ⟨0⟩ := by
        rw [hword]
        exact bitSet'
      have hdecision :
          exponentBitDecision (initial.byte.land ⟨255⟩) topBit.toNat = true := by
        unfold exponentBitDecision
        simp [hset]
      simp only [FreshBarrettByteSelection.byte, freshBarrettByteDecisions,
        exponentBitDecisions]
      rw [hdecision]
      simp only [List.cons.injEq, true_and]
      exact valid.restValid.decisions_eq

/-- The branch-complete first-byte selector is exactly one pure MSB scan. The proof follows the
selected fresh square, optional multiply, and reused lower-bit computations. -/
theorem selectFreshBarrettByte_valueInvariant
    {I : ExecutionEnv} {bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu : UInt256} {mem : ByteArray}
    {aw byteIdx exponent topBit : UInt256} {selected : FreshBarrettByteSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx } (freshBarrettByteDecisions selected)).value := by
  let byte := barrettExponentByteValue mem (exponentArrayLengthAw aw exponent)
    exponent byteIdx
  by_cases hunset : ((⟨1⟩ : UInt256).land
      ((byte.land ⟨255⟩).shiftRight topBit)).eq ⟨1⟩ = ⟨0⟩
  · rw [selectFreshBarrettByte, if_pos hunset] at hselect
    cases hsquare : selectFreshBarrettSquare callFuel mem
        (exponentByteLoadAw aw exponent byteIdx) kWords fp r n mu with
    | none => simp [byte, hsquare] at hselect
    | some square =>
        cases hrest : selectBarrettBitLoop bitFuel callFuel square.memory
            square.activeWords kWords fp topBit byte r a n mu with
        | none => simp [byte, hsquare, hrest] at hselect
        | some rest =>
            simp only [byte, hsquare, hrest, Option.some.injEq] at hselect
            subst selected
            have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
            have squareValid := loadInvariant.freshSquareValid hsquare
            have squareInvariant := loadInvariant.afterFreshSquare squareValid
            have hvalue := selectBarrettBitLoop_valueInvariant (pfx := 2 * pfx)
              squareInvariant hrest
            simpa [FreshBarrettByteSelection.memory, freshBarrettByteDecisions,
              Modexp.msbPowScan] using hvalue
  · rw [selectFreshBarrettByte, if_neg hunset] at hselect
    cases hinitial : selectInitialBarrettByte bitFuel callFuel mem aw kWords fp
        byteIdx exponent topBit r a n mu with
    | none => simp [hinitial] at hselect
    | some initial =>
        simp only [hinitial, Option.some.injEq] at hselect
        subst selected
        unfold selectInitialBarrettByte at hinitial
        dsimp only at hinitial
        let lengthAw := exponentArrayLengthAw aw exponent
        let loadedByte := barrettExponentByteValue mem lengthAw exponent byteIdx
        let loadAw := exponentByteLoadAw aw exponent byteIdx
        cases hsquare : selectFreshBarrettSquare callFuel mem loadAw kWords fp r n mu with
        | none => simpa [lengthAw, loadedByte, loadAw, hsquare] using hinitial
        | some square =>
            cases hmultiply : selectBarrettMultiply callFuel square.memory square.activeWords
                kWords fp r a n mu with
            | none =>
                simpa [lengthAw, loadedByte, loadAw, hsquare, hmultiply] using hinitial
            | some multiply =>
                cases hrest : selectBarrettBitLoop bitFuel callFuel multiply.memory
                    multiply.activeWords kWords fp topBit loadedByte r a n mu with
                | none =>
                    simpa [lengthAw, loadedByte, loadAw, hsquare, hmultiply, hrest] using
                      hinitial
                | some rest =>
                    have hselected : initial = {
                        byte := loadedByte
                        square := square
                        multiply := multiply
                        rest := rest
                        memory := rest.memory
                        activeWords := rest.activeWords
                        steps := square.steps + multiply.steps + rest.steps + 123
                        gas := barrettExponentByteLoadGas aw exponent byteIdx + square.gas +
                          multiply.gas + rest.gas + 203 } := by
                      simpa [lengthAw, loadedByte, loadAw, hsquare, hmultiply, hrest] using
                        hinitial.symm
                    subst initial
                    have loadInvariant := invariant.afterExponentByteLoad hexponentFit hbyteFit
                    have squareValid := loadInvariant.freshSquareValid (by
                      simpa only [loadAw] using hsquare)
                    have squareInvariant := loadInvariant.afterFreshSquare squareValid
                    have multiplyValid := squareInvariant.multiplyValid hmultiply
                    have multiplyInvariant := squareInvariant.afterMultiply multiplyValid
                    have hvalue := selectBarrettBitLoop_valueInvariant (pfx := 2 * pfx + 1)
                      multiplyInvariant (by simpa only [loadedByte] using hrest)
                    simpa [FreshBarrettByteSelection.memory, freshBarrettByteDecisions,
                      Modexp.msbPowScan] using hvalue

inductive BarrettByteLoopSelection where
  | done (memory : ByteArray) (activeWords byteIdx topBit : UInt256)
  | next (byte : BarrettByteSelection) (rest : BarrettByteLoopSelection)

namespace BarrettByteLoopSelection

def memory : BarrettByteLoopSelection → ByteArray
  | .done mem _ _ _ => mem
  | .next _ rest => rest.memory

def activeWords : BarrettByteLoopSelection → UInt256
  | .done _ aw _ _ => aw
  | .next _ rest => rest.activeWords

def byteIdx : BarrettByteLoopSelection → UInt256
  | .done _ _ idx _ => idx
  | .next _ rest => rest.byteIdx

def topBit : BarrettByteLoopSelection → UInt256
  | .done _ _ _ top => top
  | .next _ rest => rest.topBit

def steps : BarrettByteLoopSelection → Nat
  | .done _ _ _ _ => 0
  | .next byte rest => byte.steps + rest.steps

def gas : BarrettByteLoopSelection → Nat
  | .done _ _ _ _ => 0
  | .next byte rest => byte.gas + rest.gas

end BarrettByteLoopSelection

def selectBarrettByteLoop (byteFuel bitFuel callFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (kWords fp : Nat)
    (byteIdx exponent topBit expLen r a n mu : UInt256) : Option BarrettByteLoopSelection :=
  if byteIdx.lt expLen = ⟨0⟩ then some (.done mem aw byteIdx topBit) else
    match byteFuel with
    | 0 => none
    | byteFuel + 1 =>
        match selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent topBit
            r a n mu with
        | none => none
        | some byte =>
            match selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory byte.activeWords
                kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen r a n mu with
            | none => none
            | some rest => some (.next byte rest)

/-- The complete byte loop is total with one unit of byte fuel per remaining exponent byte and
eight units of bit fuel. The explicit first-byte bound also covers its scanned top bit. -/
theorem selectBarrettByteLoop_exists
    {byteFuel bitFuel callFuel kWords fp : Nat}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen r a n mu : UInt256}
    (hkPos : 0 < kWords) (hcallFuel : kWords ≤ callFuel)
    (hremaining : expLen.toNat - byteIdx.toNat ≤ byteFuel)
    (htopFuel : (topBit + ⟨1⟩).toNat ≤ bitFuel)
    (hbyteBits : 8 ≤ bitFuel) :
    ∃ selected,
      selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
        byteIdx exponent topBit expLen r a n mu = some selected := by
  induction byteFuel generalizing mem aw byteIdx topBit with
  | zero =>
      have hge : expLen.toNat ≤ byteIdx.toNat := by omega
      have hguard : byteIdx.lt expLen = ⟨0⟩ := ult_zero hge
      simp [selectBarrettByteLoop, hguard]
  | succ byteFuel ih =>
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp [selectBarrettByteLoop, hguard]
      · have hidxLt : byteIdx.toNat < expLen.toNat := by
          by_contra hnot
          exact hguard (ult_zero (by omega))
        have hexpFit : expLen.toNat < UInt256.size := expLen.val.isLt
        have hnextFit : byteIdx.toNat + 1 < UInt256.size := by omega
        have hnextNat : (byteIdx + ⟨1⟩).toNat = byteIdx.toNat + 1 := by
          rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
            Nat.mod_eq_of_lt hnextFit]
        have hremainingNext : expLen.toNat - (byteIdx + ⟨1⟩).toNat ≤ byteFuel := by
          rw [hnextNat]
          omega
        rcases selectBarrettByte_exists (mem := mem) (aw := aw) (byteIdx := byteIdx)
          (exponent := exponent) (topBit := topBit) (r := r) (a := a) (n := n)
          (mu := mu) (fp := fp) hkPos hcallFuel htopFuel with ⟨byte, hbyte⟩
        have hnextTop : ((⟨7⟩ : UInt256) + ⟨1⟩).toNat ≤ bitFuel := by
          have height : ((⟨7⟩ : UInt256) + ⟨1⟩).toNat = 8 := by native_decide
          rw [height]
          exact hbyteBits
        rcases ih (mem := byte.memory) (aw := byte.activeWords)
          (byteIdx := byteIdx + ⟨1⟩) (topBit := ⟨7⟩) hremainingNext hnextTop
          with ⟨rest, hrest⟩
        rw [selectBarrettByteLoop, if_neg hguard]
        simp only [hbyte]
        rw [hrest]
        exact ⟨_, rfl⟩

inductive BarrettByteLoopValid (I : ExecutionEnv) (callFuel : Nat) (kWords fp : Nat)
    (r a n mu exponent expLen : UInt256) :
    ByteArray → UInt256 → UInt256 → UInt256 → BarrettByteLoopSelection → Prop where
  | done (mem : ByteArray) (aw byteIdx topBit : UInt256)
      (guardZero : byteIdx.lt expLen = ⟨0⟩) :
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        mem aw byteIdx topBit (.done mem aw byteIdx topBit)
  | next {mem : ByteArray} {aw byteIdx topBit : UInt256}
      {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
      (byteValid : BarrettByteValid I callFuel kWords fp r a n mu
        mem aw byteIdx exponent topBit expLen byte)
      (restValid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        byte.memory byte.activeWords (byteIdx + ⟨1⟩) ⟨7⟩ rest) :
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        mem aw byteIdx topBit (.next byte rest)

/-- Concrete, state-independent geometry for Solidity's checked exponent-byte reads.  Unlike the
legacy access callback, this records one real header and quantifies only over actual indices. -/
structure BarrettExponentAccessFrame
    (mem : ByteArray) (exponent expLen r : UInt256) : Prop where
  exponentBase : 96 <= exponent.toNat
  exponentBelowAccumulator : exponent.toNat + 32 <= r.toNat
  headerConcrete : exponent.toNat + 32 <= mem.size
  header : mem.readWithPadding exponent.toNat 32 = expLen.toByteArray
  exponentFit : exponent.toNat + 32 + 31 < UInt256.size
  byteFit : forall idx, idx.lt expLen ≠ ⟨0⟩ ->
    (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size

/-- A complete covered exponent header decodes to its recorded dynamic-array length. -/
theorem exponentArrayLength_eq_of_header
    {mem : ByteArray} {aw exponent expLen : UInt256}
    (hcovered : MemoryCovered mem aw) (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : exponent.toNat + 32 <= mem.size)
    (hheader : mem.readWithPadding exponent.toNat 32 = expLen.toByteArray) :
    exponentArrayLength mem aw exponent = expLen := by
  have hpast : ¬ exponent.toNat >= mem.size := by omega
  have hactive : ¬ exponent >= aw * ⟨32⟩ :=
    wordBelowActive_of_covered mem aw exponent hcovered hawFit hword
  unfold exponentArrayLength
  rw [if_neg (not_or.mpr ⟨hpast, hactive⟩), hheader,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem BarrettExponentInvariant.exponentHeaderConcrete
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw r a n mu exponent : UInt256}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hbelow : exponent.toNat + 32 <= r.toNat) :
    exponent.toNat + 32 <= mem.size := by
  apply le_trans hbelow
  apply le_trans _ invariant.scratchConcrete
  have hr := invariant.rBeforeScratch
  unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
  omega

/-- Framed byte-loop validity.  Every recursive checked load is proved from the one concrete
header and the exact memory frame exported by the selected Barrett computations. -/
theorem selectBarrettByteLoop_validInvariantFramedReadBelow
    {I : ExecutionEnv} {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection} {read : Nat}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    exists finalValue,
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
          mem aw byteIdx topBit selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding exponent.toNat 32 =
        mem.readWithPadding exponent.toNat 32 /\
      selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction byteFuel generalizing mem aw byteIdx topBit selected rValue with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw byteIdx topBit hguard, invariant, rfl, rfl⟩
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw byteIdx topBit hguard, invariant, rfl, rfl⟩
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            have htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hsmall : 8 < UInt256.size := by decide
                  omega)]
              omega
            have hword : exponent.toNat + 32 <= mem.size := by
              apply le_trans access.exponentBelowAccumulator
              apply le_trans _ invariant.scratchConcrete
              have hr := invariant.rBeforeScratch
              unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
              omega
            have hlength : exponentArrayLength mem aw exponent = expLen :=
              exponentArrayLength_eq_of_header invariant.covered invariant.activeWordsFit
                hword access.header
            have hindex :
                (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩ := by
              rw [hlength]
              exact isZero_eq_zero_of_ne hguard
            rcases selectBarrettByte_validInvariantReadBelow invariant hguard hindex htop
                access.exponentFit (access.byteFit byteIdx hguard) access.exponentBase
                access.exponentBelowAccumulator hbyte with
              ⟨nextValue, byteValid, byteInvariant, byteFrame⟩
            rcases selectBarrettByte_validInvariantReadBelow invariant hguard hindex htop
                access.exponentFit (access.byteFit byteIdx hguard) hread hbelow hbyte with
              ⟨_, _, _, byteReadFrame⟩
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                have nextAccess : BarrettExponentAccessFrame byte.memory exponent expLen r := {
                  access with
                  headerConcrete := byteInvariant.exponentHeaderConcrete
                    access.exponentBelowAccumulator
                  header := byteFrame.trans access.header }
                rcases ih byteInvariant (by decide) nextAccess hrest with
                  ⟨finalValue, restValid, finalInvariant, restFrame, restReadFrame⟩
                exact ⟨finalValue, .next byteValid restValid, finalInvariant,
                  restFrame.trans byteFrame, restReadFrame.trans byteReadFrame⟩

/-- Framed byte-loop validity specialized to preservation of the exponent header. -/
theorem selectBarrettByteLoop_validInvariantFramed
    {I : ExecutionEnv} {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    exists finalValue,
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
          mem aw byteIdx topBit selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      selected.memory.readWithPadding exponent.toNat 32 =
        mem.readWithPadding exponent.toNat 32 := by
  rcases selectBarrettByteLoop_validInvariantFramedReadBelow invariant htopBound access
      access.exponentBase access.exponentBelowAccumulator hselect with
    ⟨finalValue, valid, finalInvariant, headerFrame, _⟩
  exact ⟨finalValue, valid, finalInvariant, headerFrame⟩

theorem selectBarrettByteLoop_valid
    {I : ExecutionEnv} {byteFuel bitFuel callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : BarrettByteLoopSelection}
    (hbyteValid : ∀ (mem' : ByteArray) (aw' byteIdx' topBit' : UInt256)
      (byte : BarrettByteSelection),
      byteIdx'.lt expLen ≠ ⟨0⟩ →
      selectBarrettByte bitFuel callFuel mem' aw' kWords fp byteIdx' exponent topBit'
        r a n mu = some byte →
      BarrettByteValid I callFuel kWords fp r a n mu
        mem' aw' byteIdx' exponent topBit' expLen byte)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected := by
  induction byteFuel generalizing mem aw byteIdx topBit selected with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw byteIdx topBit hguard
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw byteIdx topBit hguard
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                exact .next (hbyteValid mem aw byteIdx topBit byte hguard hbyte) (ih hrest)

/-- The byte-loop selector proves every modular operation internally.  `haccess` is deliberately
limited to Solidity's checked dynamic-array read and non-wrapping MLOAD address conditions. -/
theorem selectBarrettByteLoop_validInvariant
    {I : ExecutionEnv} {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    exists finalValue,
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
          mem aw byteIdx topBit selected /\
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  induction byteFuel generalizing mem aw byteIdx topBit selected rValue with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw byteIdx topBit hguard, invariant⟩
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact ⟨rValue, .done mem aw byteIdx topBit hguard, invariant⟩
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            have htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hsmall : 8 < UInt256.size := by decide
                  omega)]
              omega
            rcases haccess mem aw byteIdx hguard with ⟨hindex, hexponentFit, hbyteFit⟩
            rcases selectBarrettByte_validInvariant invariant hguard hindex htop
                hexponentFit hbyteFit hbyte with ⟨nextValue, byteValid, byteInvariant⟩
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                rcases ih byteInvariant (by decide) hrest with
                  ⟨finalValue, restValid, finalInvariant⟩
                exact ⟨finalValue, .next byteValid restValid, finalInvariant⟩

theorem validBarrettByteLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : BarrettByteLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected)
    (hdepth : tail.length + 36 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack selected.byteIdx exponent selected.topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  induction valid generalizing steps gasUsed with
  | done mem aw byteIdx topBit guardZero =>
      simpa [BarrettByteLoopSelection.byteIdx, BarrettByteLoopSelection.topBit,
        BarrettByteLoopSelection.memory, BarrettByteLoopSelection.activeWords,
        BarrettByteLoopSelection.steps, BarrettByteLoopSelection.gas] using h
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      have rdNext := validBarrettByteExact byteValid hdepth h
      have rdFinal := ih (steps := steps + byte.steps) (gasUsed := gasUsed + byte.gas) rdNext
      simpa [BarrettByteLoopSelection.byteIdx, BarrettByteLoopSelection.topBit,
        BarrettByteLoopSelection.memory, BarrettByteLoopSelection.activeWords,
        BarrettByteLoopSelection.steps, BarrettByteLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

theorem BarrettByteLoopValid.finalGuardZero
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected) :
    selected.byteIdx.lt expLen = ⟨0⟩ := by
  induction valid with
  | done _ _ _ _ guardZero => simpa [BarrettByteLoopSelection.byteIdx] using guardZero
  | next _ _ ih => simpa [BarrettByteLoopSelection.byteIdx] using ih

theorem validBarrettByteLoopReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen returnPc : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected)
    (hdepth : tail.length + 37 ≤ 1016)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu (UInt256.ofNat fp) a
        (UInt256.ofNat kWords) expLen n r (returnPc :: tail))
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc (r :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps + 17) (gasUsed + selected.gas + 52) := by
  have rdDone := validBarrettByteLoopExact valid (by
    simp only [List.length_cons]
    omega) h
  have rdReturn := barrettByteGuardReturn (by omega) valid.finalGuardZero hreturn rdDone
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

def BarrettSquareGeometryProvider
    (I : ExecutionEnv) (callFuel kWords fp : Nat) (r n mu : UInt256)
    (modulus : Nat) : Prop :=
  ∀ {mem : ByteArray} {aw : UInt256} {square : BarrettSquareSelection},
    BarrettSquareValid I callFuel mem aw kWords fp r n mu square →
    BarrettSquareSemanticGeometry I callFuel mem aw kWords fp r n mu square
      (barrettAccumulatorValue kWords r mem) modulus

def BarrettMultiplyGeometryProvider
    (I : ExecutionEnv) (callFuel kWords fp : Nat) (r a n mu : UInt256)
    (base modulus : Nat) : Prop :=
  ∀ {mem : ByteArray} {aw : UInt256} {multiply : BarrettMultiplySelection},
    BarrettMultiplyValid I callFuel mem aw kWords fp r a n mu multiply →
    BarrettMultiplySemanticGeometry I callFuel mem aw kWords fp r a n mu multiply
      (barrettAccumulatorValue kWords r mem) base modulus

theorem BarrettBitLoopValid.value_eq_pow_of_geometry
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu byte bit : UInt256}
    {mem : ByteArray} {aw : UInt256} {selected : BarrettBitLoopSelection}
    (valid : BarrettBitLoopValid I callFuel kWords fp r a n mu byte mem aw bit selected)
    (modulus base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ pfx % modulus)
    (hsquare : BarrettSquareGeometryProvider I callFuel kWords fp r n mu modulus)
    (hmultiply : BarrettMultiplyGeometryProvider I callFuel kWords fp r a n mu
      base modulus) :
    barrettAccumulatorValue kWords r selected.memory =
      base ^ ((barrettBitLoopDecisions selected).foldl
        (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  apply valid.value_eq_pow modulus base pfx hmodulus hinitial
  · intro mem' aw' bit' square rest step
    cases step with
    | unset _ squareValid _ _ => exact hsquare squareValid
  · intro mem' aw' bit' square multiply rest step
    cases step with
    | set _ squareValid _ _ _ => exact hsquare squareValid
  · intro mem' aw' bit' square multiply rest step
    cases step with
    | set _ _ multiplyValid _ _ => exact hmultiply multiplyValid

/-- Bit decisions of all selected exponent bytes in execution order. -/
def barrettByteLoopDecisions : BarrettByteLoopSelection → List Bool
  | .done _ _ _ _ => []
  | .next byte rest =>
      barrettBitLoopDecisions byte.bits ++ barrettByteLoopDecisions rest

theorem msbPowScan_append_local {A : Type} (mul : A → A → A) (base : A)
    (state : Modexp.MsbPowState A) (left right : List Bool) :
    Modexp.msbPowScan mul base state (left ++ right) =
      Modexp.msbPowScan mul base (Modexp.msbPowScan mul base state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons bit left ih =>
      simp only [List.cons_append, Modexp.msbPowScan]
      exact ih _

/-- Concatenating selected bytes gives one pure MSB scan over the complete selected decision
stream. Modular validity is internal; `haccess` contains only checked-array/MLOAD geometry. -/
theorem selectBarrettByteLoop_valueInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx }
        (barrettByteLoopDecisions selected)).value := by
  induction byteFuel generalizing mem aw byteIdx topBit selected rValue pfx with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
          invariant.rValueEq]
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
          invariant.rValueEq]
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            have htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hsmall : 8 < UInt256.size := by decide
                  omega)]
              omega
            rcases haccess mem aw byteIdx hguard with ⟨hindex, hexponentFit, hbyteFit⟩
            rcases selectBarrettByte_validInvariant invariant hguard hindex htop
                hexponentFit hbyteFit hbyte with ⟨nextValue, byteValid, byteInvariant⟩
            have hbyteValue := selectBarrettByte_valueInvariant (pfx := pfx) invariant
              hexponentFit hbyteFit hbyte
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                let firstState := Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
                  { value := rValue, exponent := pfx }
                  (barrettBitLoopDecisions byte.bits)
                have hfirstValue : nextValue = firstState.value :=
                  byteInvariant.rValueEq.symm.trans hbyteValue
                have hstate : ({ value := nextValue, exponent := firstState.exponent } :
                    Modexp.MsbPowState Nat) = firstState := by
                  rw [hfirstValue]
                have hrestValue := ih (pfx := firstState.exponent) byteInvariant
                  (by decide) hrest
                simp only [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
                  msbPowScan_append_local]
                rw [hrestValue, hstate]

/-- Pure scan semantics for the framed byte loop, with checked loads recovered from the
preserved concrete exponent header rather than an arbitrary-memory callback. -/
theorem selectBarrettByteLoop_valueInvariantFramed
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx }
        (barrettByteLoopDecisions selected)).value := by
  induction byteFuel generalizing mem aw byteIdx topBit selected rValue pfx with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
          invariant.rValueEq]
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        simpa [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
          invariant.rValueEq]
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            have htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hsmall : 8 < UInt256.size := by decide
                  omega)]
              omega
            have hword : exponent.toNat + 32 <= mem.size := by
              apply le_trans access.exponentBelowAccumulator
              apply le_trans _ invariant.scratchConcrete
              have hr := invariant.rBeforeScratch
              unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
              omega
            have hlength : exponentArrayLength mem aw exponent = expLen :=
              exponentArrayLength_eq_of_header invariant.covered invariant.activeWordsFit
                hword access.header
            have hindex :
                (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩ := by
              rw [hlength]
              exact isZero_eq_zero_of_ne hguard
            rcases selectBarrettByte_validInvariantReadBelow invariant hguard hindex htop
                access.exponentFit (access.byteFit byteIdx hguard) access.exponentBase
                access.exponentBelowAccumulator hbyte with
              ⟨nextValue, byteValid, byteInvariant, byteFrame⟩
            have hbyteValue := selectBarrettByte_valueInvariant (pfx := pfx) invariant
              access.exponentFit (access.byteFit byteIdx hguard) hbyte
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                let firstState := Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
                  { value := rValue, exponent := pfx }
                  (barrettBitLoopDecisions byte.bits)
                have hfirstValue : nextValue = firstState.value :=
                  byteInvariant.rValueEq.symm.trans hbyteValue
                have hstate : ({ value := nextValue, exponent := firstState.exponent } :
                    Modexp.MsbPowState Nat) = firstState := by
                  rw [hfirstValue]
                have nextAccess : BarrettExponentAccessFrame byte.memory exponent expLen r := {
                  access with
                  headerConcrete := byteInvariant.exponentHeaderConcrete
                    access.exponentBelowAccumulator
                  header := byteFrame.trans access.header }
                have hrestValue := ih (pfx := firstState.exponent) byteInvariant
                  (by decide) nextAccess hrest
                simp only [BarrettByteLoopSelection.memory, barrettByteLoopDecisions,
                  msbPowScan_append_local]
                rw [hrestValue, hstate]

/-- The fresh first byte and the ordinary remaining-byte loop form one pure scan. Both selected
execution fragments are consumed directly, so the final memory is the concrete selector output. -/
theorem selectFreshBarrettByteAndLoop_valueInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest) :
    barrettAccumulatorValue kWords r rest.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx }
        (freshBarrettByteDecisions first ++ barrettByteLoopDecisions rest)).value := by
  rcases selectFreshBarrettByte_validInvariant invariant hguard hindex htop hcounter
      hexponentFit hbyteFit hfirst with ⟨firstValue, firstValid, firstInvariant⟩
  have hfirstValue := selectFreshBarrettByte_valueInvariant (pfx := pfx) invariant
    hexponentFit hbyteFit hfirst
  let firstState := Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
    { value := rValue, exponent := pfx } (freshBarrettByteDecisions first)
  have hfirstValue' : firstValue = firstState.value :=
    firstInvariant.rValueEq.symm.trans hfirstValue
  have hstate : ({ value := firstValue, exponent := firstState.exponent } :
      Modexp.MsbPowState Nat) = firstState := by
    rw [hfirstValue']
  have hrestValue := selectBarrettByteLoop_valueInvariant
    (pfx := firstState.exponent) firstInvariant (by decide) haccess hrest
  rw [msbPowScan_append_local, hrestValue, hstate]

/-- Framed validity for the first fresh byte followed by the ordinary remaining-byte loop. -/
theorem selectFreshBarrettByteAndLoop_validInvariantFramedReadBelow
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection} {read : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hread : 96 <= read) (hbelow : read + 32 <= r.toNat)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest) :
    exists firstValue finalValue,
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen first /\
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        first.memory first.activeWords (byteIdx + ⟨1⟩) ⟨7⟩ rest /\
      BarrettExponentInvariant I rest.memory rest.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      BarrettExponentInvariant I first.memory first.activeWords kWords fp r a n mu
        firstValue baseValue nValue /\
      rest.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  rcases selectFreshBarrettByte_validInvariantReadBelow invariant hguard hindex htop hcounter
      access.exponentFit (access.byteFit byteIdx hguard) access.exponentBase
      access.exponentBelowAccumulator hfirst with
    ⟨firstValue, firstValid, firstInvariant, firstFrame⟩
  rcases selectFreshBarrettByte_validInvariantReadBelow invariant hguard hindex htop hcounter
      access.exponentFit (access.byteFit byteIdx hguard) hread hbelow hfirst with
    ⟨_, _, _, firstReadFrame⟩
  have firstAccess : BarrettExponentAccessFrame first.memory exponent expLen r := {
    access with
    headerConcrete := firstInvariant.exponentHeaderConcrete
      access.exponentBelowAccumulator
    header := firstFrame.trans access.header }
  rcases selectBarrettByteLoop_validInvariantFramedReadBelow firstInvariant (by decide)
      firstAccess hread hbelow hrest with
    ⟨finalValue, restValid, finalInvariant, _, restReadFrame⟩
  exact ⟨firstValue, finalValue, firstValid, restValid, finalInvariant, firstInvariant,
    restReadFrame.trans firstReadFrame⟩

/-- Framed validity for the first fresh byte and remaining loop, preserving the exponent header. -/
theorem selectFreshBarrettByteAndLoop_validInvariantFramed
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest) :
    exists firstValue finalValue,
      FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent
        topBit expLen first /\
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        first.memory first.activeWords (byteIdx + ⟨1⟩) ⟨7⟩ rest /\
      BarrettExponentInvariant I rest.memory rest.activeWords kWords fp r a n mu
        finalValue baseValue nValue /\
      BarrettExponentInvariant I first.memory first.activeWords kWords fp r a n mu
        firstValue baseValue nValue := by
  rcases selectFreshBarrettByteAndLoop_validInvariantFramedReadBelow invariant hguard hindex
      htop hcounter access access.exponentBase access.exponentBelowAccumulator hfirst hrest with
    ⟨firstValue, finalValue, firstValid, restValid, finalInvariant, firstInvariant, _⟩
  exact ⟨firstValue, finalValue, firstValid, restValid, finalInvariant, firstInvariant⟩

/-- Framed pure-scan semantics for the first fresh byte and all remaining bytes. -/
theorem selectFreshBarrettByteAndLoop_valueInvariantFramed
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest) :
    barrettAccumulatorValue kWords r rest.memory =
      (Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
        { value := rValue, exponent := pfx }
        (freshBarrettByteDecisions first ++ barrettByteLoopDecisions rest)).value := by
  rcases selectFreshBarrettByte_validInvariantReadBelow invariant hguard hindex htop hcounter
      access.exponentFit (access.byteFit byteIdx hguard) access.exponentBase
      access.exponentBelowAccumulator hfirst with
    ⟨firstValue, _, firstInvariant, firstFrame⟩
  have hfirstValue := selectFreshBarrettByte_valueInvariant (pfx := pfx) invariant
    access.exponentFit (access.byteFit byteIdx hguard) hfirst
  let firstState := Modexp.msbPowScan (fun x y => x * y % nValue) baseValue
    { value := rValue, exponent := pfx } (freshBarrettByteDecisions first)
  have hfirstValue' : firstValue = firstState.value :=
    firstInvariant.rValueEq.symm.trans hfirstValue
  have hstate : ({ value := firstValue, exponent := firstState.exponent } :
      Modexp.MsbPowState Nat) = firstState := by
    rw [hfirstValue']
  have firstAccess : BarrettExponentAccessFrame first.memory exponent expLen r := {
    access with
    headerConcrete := firstInvariant.exponentHeaderConcrete
      access.exponentBelowAccumulator
    header := firstFrame.trans access.header }
  have hrestValue := selectBarrettByteLoop_valueInvariantFramed
    (pfx := firstState.exponent) firstInvariant (by decide) firstAccess hrest
  rw [msbPowScan_append_local, hrestValue, hstate]

/-- The selected byte loop computes ordinary modular exponentiation by its complete concrete
decision stream. -/
theorem selectBarrettByteLoop_value_eq_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue pfx : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hmodulus : 0 < nValue)
    (hinitial : rValue = baseValue ^ pfx % nValue)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    barrettAccumulatorValue kWords r selected.memory =
      baseValue ^ ((barrettByteLoopDecisions selected).foldl
        (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % nValue := by
  have hvalue := selectBarrettByteLoop_valueInvariant (pfx := pfx) invariant
    htopBound haccess hselect
  let state : Modexp.MsbPowState Nat := { value := rValue, exponent := pfx }
  have hcorrect := Modexp.msbPowScan_correct id (fun x y => x * y % nValue)
    baseValue nValue hmodulus (by intro x y; rfl) state
    (barrettByteLoopDecisions selected) (by simpa [state] using hinitial)
  rw [hvalue]
  simpa [state, Modexp.msbPowScan_exponent] using hcorrect

theorem BarrettByteValid.decisions_eq
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : BarrettByteSelection}
    (valid : BarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx exponent topBit
      expLen selected)
    (htop : topBit.toNat < 8) :
    barrettBitLoopDecisions selected.bits =
      exponentBitDecisions (selected.byte.land ⟨255⟩) (topBit.toNat + 1) := by
  have hfit : topBit.toNat + 1 < UInt256.size :=
    lt_of_lt_of_le (by omega : topBit.toNat + 1 < 10) (by native_decide)
  have hadd : (topBit + ⟨1⟩).toNat = topBit.toNat + 1 := by
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt hfit]
  rw [← hadd]
  exact valid.bitsValid.decisions_eq

def expectedBarrettByteLoopDecisions : Nat → BarrettByteLoopSelection → List Bool
  | _, .done _ _ _ _ => []
  | topBit, .next byte rest =>
      exponentBitDecisions (byte.byte.land ⟨255⟩) (topBit + 1) ++
        expectedBarrettByteLoopDecisions 7 rest

theorem BarrettByteLoopValid.decisions_eq
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected)
    (htop : topBit.toNat < 8) :
    barrettByteLoopDecisions selected =
      expectedBarrettByteLoopDecisions topBit.toNat selected := by
  induction valid with
  | done => rfl
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      simp only [barrettByteLoopDecisions, expectedBarrettByteLoopDecisions]
      rw [byteValid.decisions_eq htop]
      congr 1
      simpa using ih (by native_decide)

def selectedBarrettByteLoopValue : Nat → BarrettByteLoopSelection → Nat → Nat
  | _, .done _ _ _ _, pfx => pfx
  | topBit, .next byte rest, pfx =>
      selectedBarrettByteLoopValue 7 rest
        (appendWordBits (byte.byte.land ⟨255⟩).toNat (topBit + 1) pfx)

theorem expectedBarrettByteLoopDecisions_fold
    (topBit : Nat) (selected : BarrettByteLoopSelection) (pfx : Nat)
    (htop : topBit < 256) :
    (expectedBarrettByteLoopDecisions topBit selected).foldl
        (fun acc decision => 2 * acc + if decision then 1 else 0) pfx =
      selectedBarrettByteLoopValue topBit selected pfx := by
  induction selected generalizing topBit pfx with
  | done => rfl
  | next byte rest ih =>
      rw [expectedBarrettByteLoopDecisions, List.foldl_append,
        exponentBitDecisions_fold (byte.byte.land ⟨255⟩) (topBit + 1) pfx (by omega)]
      exact ih 7 _ (by omega)

theorem BarrettByteLoopValid.decisions_toNat
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected)
    (htop : topBit.toNat < 8) :
    bitsToNatMSB (barrettByteLoopDecisions selected) =
      selectedBarrettByteLoopValue topBit.toNat selected 0 := by
  rw [valid.decisions_eq htop]
  exact expectedBarrettByteLoopDecisions_fold topBit.toNat selected 0 (by omega)

/-- The selected masked bytes match a suffix of the trusted padded exponent field. -/
inductive BarrettByteLoopMatches (I : ExecutionEnv) (baseSize exponentSize : Nat) :
    Nat → BarrettByteLoopSelection → Prop where
  | done (mem : ByteArray) (aw byteIdx topBit : UInt256) :
      BarrettByteLoopMatches I baseSize exponentSize exponentSize
        (.done mem aw byteIdx topBit)
  | next {start : Nat} {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
      (startLt : start < exponentSize)
      (byteEq : (byte.byte.land ⟨255⟩).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
      (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest) :
      BarrettByteLoopMatches I baseSize exponentSize start (.next byte rest)

theorem BarrettByteLoopMatches.fullBytesValue
    {I : ExecutionEnv} {baseSize exponentSize start : Nat}
    {selected : BarrettByteLoopSelection}
    (matching : BarrettByteLoopMatches I baseSize exponentSize start selected)
    (pfx : Nat) :
    selectedBarrettByteLoopValue 7 selected pfx =
      pfx * 256 ^ (exponentSize - start) +
        Model.bytesToNatPadded I.calldata (96 + baseSize + start)
          (exponentSize - start) := by
  induction matching generalizing pfx with
  | done =>
      simp [selectedBarrettByteLoopValue, model_bytesToNatPadded_zero_width]
  | @next start byte rest startLt byteEq restMatches ih =>
      have hbyteLt : (byte.byte.land ⟨255⟩).toNat < 256 := by
        rw [byteEq]
        have h := model_bytesToNatPadded_lt_pow I.calldata (96 + baseSize + start) 1
        simpa using h
      have hsplit := model_bytesToNatPadded_split I.calldata
        (96 + baseSize + start) 1 (exponentSize - (start + 1))
      have hwidth : exponentSize - start = 1 + (exponentSize - (start + 1)) := by omega
      simp only [selectedBarrettByteLoopValue]
      rw [appendWordBits_eight (byte.byte.land ⟨255⟩).toNat pfx hbyteLt, ih]
      rw [hwidth, hsplit, ← byteEq]
      simp only [pow_add, pow_one]
      ring

theorem BarrettByteLoopMatches.significantValue_of_lt_pow
    {I : ExecutionEnv} {baseSize exponentSize start topBit : Nat}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (htop : topBit < 8)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (topBit + 1)) :
    selectedBarrettByteLoopValue topBit (.next byte rest) 0 =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  have hfirst := appendWordBits_zero_eq_of_lt_pow
    (byte.byte.land ⟨255⟩).toNat (topBit + 1) (by omega) hbyte
  have htail := restMatches.fullBytesValue (byte.byte.land ⟨255⟩).toNat
  have hsplit := model_bytesToNatPadded_split I.calldata
    (96 + baseSize + start) 1 (exponentSize - (start + 1))
  have hwidth : exponentSize - start = 1 + (exponentSize - (start + 1)) := by omega
  simp only [selectedBarrettByteLoopValue, hfirst]
  rw [htail, hwidth, hsplit, ← byteEq]
  ring

/-- The fresh first-byte decisions followed by the ordinary byte loop denote exactly the trusted
significant exponent suffix. The first byte may start below bit seven; every later byte is full. -/
theorem FreshBarrettByteValid.decisions_with_rest_to_model
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection} {baseSize exponentSize start : Nat}
    (firstValid : FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx
      exponent topBit expLen first)
    (restValid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      first.memory first.activeWords (byteIdx + ⟨1⟩) ⟨7⟩ rest)
    (htop : topBit.toNat < 8)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    bitsToNatMSB (freshBarrettByteDecisions first ++ barrettByteLoopDecisions rest) =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  have hfirst := appendWordBits_zero_eq_of_lt_pow
    (first.byte.land ⟨255⟩).toNat (topBit.toNat + 1) (by omega) hbyte
  have htail := restMatches.fullBytesValue (first.byte.land ⟨255⟩).toNat
  have hsplit := model_bytesToNatPadded_split I.calldata
    (96 + baseSize + start) 1 (exponentSize - (start + 1))
  have hwidth : exponentSize - start = 1 + (exponentSize - (start + 1)) := by omega
  have hseven : (⟨7⟩ : UInt256).toNat = 7 := by decide
  unfold bitsToNatMSB
  rw [List.foldl_append, firstValid.decisions_eq htop,
    exponentBitDecisions_fold (first.byte.land ⟨255⟩) (topBit.toNat + 1) 0 (by omega),
    restValid.decisions_eq (by decide), hseven,
    expectedBarrettByteLoopDecisions_fold 7 rest _ (by omega), hfirst, htail,
    hwidth, hsplit, ← byteEq]
  ring

/-- The fresh first byte plus all remaining selected bytes computes the trusted significant
exponent suffix directly from the persistent Barrett invariant. -/
theorem selectFreshBarrettByteAndLoop_value_eq_model_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection} {baseSize exponentSize start : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htopGuard : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (htop : topBit.toNat < 8)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : (exponentByteAddress exponent byteIdx).toNat + 32 + 31 < UInt256.size)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r rest.memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  rcases selectFreshBarrettByte_validInvariant invariant hguard hindex htopGuard hcounter
      hexponentFit hbyteFit hfirst with ⟨firstValue, firstValid, firstInvariant⟩
  rcases selectBarrettByteLoop_validInvariant firstInvariant (by decide) haccess hrest with
    ⟨finalValue, restValid, finalInvariant⟩
  have hvalue := selectFreshBarrettByteAndLoop_valueInvariant (pfx := 0) invariant
    hguard hindex htopGuard hcounter hexponentFit hbyteFit haccess hfirst hrest
  have hdecision := firstValid.decisions_with_rest_to_model restValid htop startLt
    byteEq restMatches hbyte
  let state : Modexp.MsbPowState Nat := { value := rValue, exponent := 0 }
  have hcorrect := Modexp.msbPowScan_correct id (fun x y => x * y % nValue)
    baseValue nValue invariant.nPos (by intro x y; rfl) state
    (freshBarrettByteDecisions first ++ barrettByteLoopDecisions rest)
    (by simpa [state] using hinitial)
  rw [hvalue]
  rw [Modexp.msbPowScan_exponent] at hcorrect
  unfold bitsToNatMSB at hdecision
  rw [hdecision] at hcorrect
  simpa [state] using hcorrect

/-- Framed selector-to-model theorem for a fresh first byte and all remaining bytes. -/
theorem selectFreshBarrettByteAndLoop_value_eq_model_powInvariantFramed
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {first : FreshBarrettByteSelection}
    {rest : BarrettByteLoopSelection} {baseSize exponentSize start : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htopGuard : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hcounter : topBit + ⟨1⟩ ≠ ⟨0⟩)
    (htop : topBit.toNat < 8)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hfirst : selectFreshBarrettByte bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r rest.memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  rcases selectFreshBarrettByteAndLoop_validInvariantFramed invariant hguard hindex
      htopGuard hcounter access hfirst hrest with
    ⟨_, _, firstValid, restValid, _, _⟩
  have hvalue := selectFreshBarrettByteAndLoop_valueInvariantFramed (pfx := 0) invariant
    hguard hindex htopGuard hcounter access hfirst hrest
  have hdecision := firstValid.decisions_with_rest_to_model restValid htop startLt
    byteEq restMatches hbyte
  let state : Modexp.MsbPowState Nat := { value := rValue, exponent := 0 }
  have hcorrect := Modexp.msbPowScan_correct id (fun x y => x * y % nValue)
    baseValue nValue invariant.nPos (by intro x y; rfl) state
    (freshBarrettByteDecisions first ++ barrettByteLoopDecisions rest)
    (by simpa [state] using hinitial)
  rw [hvalue]
  rw [Modexp.msbPowScan_exponent] at hcorrect
  unfold bitsToNatMSB at hdecision
  rw [hdecision] at hcorrect
  simpa [state] using hcorrect

theorem BarrettByteLoopValid.decisions_to_model
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit (.next byte rest))
    (htop : topBit.toNat < 8)
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    bitsToNatMSB (barrettByteLoopDecisions (.next byte rest)) =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  rw [valid.decisions_toNat htop]
  exact BarrettByteLoopMatches.significantValue_of_lt_pow startLt byteEq restMatches
    htop hbyte

/-- Combined selector-to-model theorem without modular geometry providers.  The only remaining
provider is the explicitly isolated Solidity array-access alignment contract. -/
theorem selectBarrettByteLoop_value_eq_model_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray}
    {aw byteIdx topBit : UInt256} {byte : BarrettByteSelection}
    {rest : BarrettByteLoopSelection} {baseSize exponentSize start : Nat}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (htopBound : topBit.toNat <= 7)
    (haccess : forall (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some (.next byte rest))
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r (BarrettByteLoopSelection.next byte rest).memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  rcases selectBarrettByteLoop_validInvariant invariant htopBound haccess hselect with
    ⟨finalValue, valid, finalInvariant⟩
  have hpow := selectBarrettByteLoop_value_eq_powInvariant invariant htopBound haccess
    invariant.nPos hinitial hselect
  have hdecision := valid.decisions_to_model (by omega) startLt byteEq restMatches hbyte
  unfold bitsToNatMSB at hdecision
  rw [hdecision] at hpow
  exact hpow

/-- Every selected byte loop computes modular exponentiation by its concatenated branch bits. -/
theorem BarrettByteLoopValid.value_eq_pow_of_geometry
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit selected)
    (modulus base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ pfx % modulus)
    (hsquare : BarrettSquareGeometryProvider I callFuel kWords fp r n mu modulus)
    (hmultiply : BarrettMultiplyGeometryProvider I callFuel kWords fp r a n mu
      base modulus) :
    barrettAccumulatorValue kWords r selected.memory =
      base ^ ((barrettByteLoopDecisions selected).foldl
        (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  induction valid generalizing pfx with
  | done => simpa [barrettByteLoopDecisions] using hinitial
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      have hbits := byteValid.bitsValid.value_eq_pow_of_geometry modulus base pfx hmodulus
        hinitial hsquare hmultiply
      have hrest := ih
        ((barrettBitLoopDecisions byte.bits).foldl
          (fun acc decision => 2 * acc + if decision then 1 else 0) pfx)
        (by simpa [byteValid.memoryEq] using hbits)
      simpa [barrettByteLoopDecisions, byteValid.memoryEq, List.foldl_append] using hrest

/-- Combined execution-to-model theorem for a nonempty significant exponent suffix. -/
theorem BarrettByteLoopValid.value_eq_model_pow_of_geometry
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start modulus base : Nat}
    (valid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
      mem aw byteIdx topBit (.next byte rest))
    (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ 0 % modulus)
    (hsquare : BarrettSquareGeometryProvider I callFuel kWords fp r n mu modulus)
    (hmultiply : BarrettMultiplyGeometryProvider I callFuel kWords fp r a n mu
      base modulus)
    (htop : topBit.toNat < 8)
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r (BarrettByteLoopSelection.next byte rest).memory =
      base ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % modulus := by
  have hpow := valid.value_eq_pow_of_geometry modulus base 0 hmodulus hinitial
    hsquare hmultiply
  have hexponent := valid.decisions_to_model htop startLt byteEq restMatches hbyte
  rw [bitsToNatMSB] at hexponent
  rw [hexponent] at hpow
  exact hpow

end Modexp.MultiLimbBarrettExponentLoop
