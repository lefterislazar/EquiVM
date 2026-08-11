import Examples.Precompiles.Modexp.MultiLimbBarrettAccumulatorContract
import Examples.Precompiles.Modexp.MultiLimbBarrettExponentSetup

/-!
# Barrett accumulator and exponent-loop composition

This file joins the real `new uint256[](k); r[0] = 1` caller segment at PC 1718 to the exposed
setup/byte/bit/correction selection for `_barrettModexpLoop`. The resulting exact theorem reaches
the caller's dynamic continuation with no existential gas total.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettExponentContract

open Modexp.MultiLimbBarrettAccumulator
open Modexp.MultiLimbBarrettExponentSetup
open Modexp.MultiLimbExponentTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def executionSteps (selected : BarrettLoopSetupSelection) : Nat :=
  104 + selected.steps

def executionGas (aw : UInt256) (fp k : Nat) (exponent : UInt256)
    (selected : BarrettLoopSetupSelection) : Nat :=
  setupGas aw fp k + selected.gas (allocatedWords aw fp k) exponent

def freshExecutionSteps (selected : FreshBarrettLoopSetupSelection) : Nat :=
  104 + selected.steps

def freshExecutionGas (aw : UInt256) (fp k : Nat) (exponent : UInt256)
    (selected : FreshBarrettLoopSetupSelection) : Nat :=
  setupGas aw fp k + selected.gas (allocatedWords aw fp k) exponent

/-- The deployed `new uint256[](k); r[0] = 1` sequence establishes the compact invariant needed
by the first, scratch-materializing Barrett square. All persistent arrays are inherited from the
pre-allocation memory by concrete non-overlap lemmas. -/
theorem initializedInvariant
    {I : ExecutionEnv} {mem : ByteArray} {aw a n mu : UInt256}
    {rFp k baseValue nValue : Nat}
    (hkTwo : 2 <= k) (hk : k <= 32) (hrFp : 96 <= rFp)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (rFp + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= rFp)
    (hgap : rFp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haBase : 96 <= a.toNat) (hnBase : 96 <= n.toNat) (hmuBase : 96 <= mu.toNat)
    (haBeforeR : a.toNat + 32 * (k + 1) <= rFp)
    (hnBeforeR : n.toNat + 32 * (k + 2) <= rFp)
    (hmuBeforeR : mu.toNat + 32 * (k + 3) <= rFp)
    (haHeader : mem.readWithPadding a.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hnHeader : mem.readWithPadding n.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hmuHeader : mem.readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (k + 2)))
    (hbaseValue : Modexp.wordLimbsToNat
      (Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (a.toNat + 32) k) =
        baseValue)
    (hnValue : Modexp.wordLimbsToNat
      (Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (n.toNat + 32) k) =
        nValue)
    (hmuValue : Modexp.wordLimbsToNat
      (Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (mu.toNat + 32) (k + 2)) =
        UInt256.size ^ (2 * k) / nValue)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (k - 1) <= nValue)
    (hnFits : nValue < UInt256.size ^ k) :
    Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory mem rFp k) (allocatedWords aw rFp k) k
      (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp) a n mu
      1 baseValue nValue := by
  have hkPos : 0 < k := by omega
  have hfit : rFp + wordArrayAllocationSize k + 31 < UInt256.size := by
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    unfold wordArrayAllocationSize wordArrayPayloadSize at hscratch ⊢
    unfold UInt256.size
    omega
  have hrWord : rFp < UInt256.size := by omega
  have hrNat : (UInt256.ofNat rFp).toNat = rFp := UInt256.toNat_ofNat_of_lt hrWord
  have hcoverage := initializedMemory_coverage mem aw rFp k hkPos hmemSize hmemLe hgap
    hawFit hfit
  refine {
    wordsPos := hkPos
    words := hk
    scratchBound := hscratch
    calldataBound := hcalldata
    freePointerBase := by omega
    covered := hcoverage.1
    activeWordsFit := hcoverage.2
    memorySize := by
      rw [initializedMemory_size mem rFp k hmemSize hmemLe hgap]
      omega
    memoryBeforeScratch := by
      rw [initializedMemory_size mem rFp k hmemSize hmemLe hgap]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    memoryGap := by
      rw [initializedMemory_size mem rFp k hmemSize hmemLe hgap]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      apply lt_usize
      omega
    rBase := by rw [hrNat]; exact hrFp
    aBase := haBase
    nBase := hnBase
    muBase := hmuBase
    aBeforeR := by rw [hrNat]; exact haBeforeR
    nBeforeR := by rw [hrNat]; exact hnBeforeR
    muBeforeR := by rw [hrNat]; exact hmuBeforeR
    rBeforeScratch := by
      rw [hrNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    rHeader := by
      rw [hrNat]
      exact initializedMemory_header mem rFp k hmemSize hmemLe hgap
    aHeader := by
      rw [initializedMemory_read_below mem rFp k a.toNat hmemSize hmemLe hgap haBase
        (by omega)]
      exact haHeader
    nHeader := by
      rw [initializedMemory_read_below mem rFp k n.toNat hmemSize hmemLe hgap hnBase
        (by omega)]
      exact hnHeader
    muHeader := by
      rw [initializedMemory_read_below mem rFp k mu.toNat hmemSize hmemLe hgap hmuBase
        (by omega)]
      exact hmuHeader
    rValueEq := initializedMemory_value mem rFp k hkPos (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
      omega)
      hmemSize hmemLe hgap
    baseValueEq := by
      rw [initializedMemory_words_below mem rFp k (a.toNat + 32) k hmemSize hmemLe hgap
        (by omega) (by omega)]
      exact hbaseValue
    nValueEq := by
      rw [initializedMemory_words_below mem rFp k (n.toNat + 32) k hmemSize hmemLe hgap
        (by omega) (by omega)]
      exact hnValue
    muValueEq := by
      rw [initializedMemory_words_below mem rFp k (mu.toNat + 32) (k + 2)
        hmemSize hmemLe hgap (by omega) (by omega)]
      exact hmuValue
    nPos := hnPos
    nNormalized := hnNormalized
    nFits := hnFits }

/-- Fresh-scratch counterpart of `exact`. The first selected square materializes the full Barrett
workspace, while every later operation reuses that concrete range. -/
theorem freshExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced returnPc : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (hkTwo : 2 <= k) (hk : k <= 32) (hfp : 96 <= fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 <= aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) >= aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : FreshBarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hdepth : tail.length + 37 <= 1015)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp :: tail) selected.memory selected.activeWords rdata acc
      (steps + freshExecutionSteps selected)
      (gasUsed + freshExecutionGas aw fp k exponent selected) := by
  have rd3154 := setupExact hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit
    hfit hread hcalldata (by
      simp only [List.length_cons]
      omega) h
  have rdReturn := valid.exact rfl (by omega) hreturn rd3154
  simpa [freshExecutionSteps, freshExecutionGas, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using rdReturn

/-- Allocate and initialize the persistent accumulator, execute every selected Barrett operation,
and return the accumulator pointer to the caller continuation. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced returnPc : UInt256}
    {selected : BarrettLoopSetupSelection}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : BarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced
      modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hdepth : tail.length + 37 ≤ 1015)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp :: tail) selected.memory selected.activeWords rdata acc
      (steps + executionSteps selected)
      (gasUsed + executionGas aw fp k exponent selected) := by
  have rd3154 := setupExact hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit
    hfit hread hcalldata (by
      simp only [List.length_cons]
      omega) h
  have rdReturn := valid.exact rfl (by omega) hreturn rd3154
  simpa [executionSteps, executionGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using rdReturn

end Modexp.MultiLimbBarrettExponentContract
