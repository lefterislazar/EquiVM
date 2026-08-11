import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationContract

/-!
# Complete Knuth normalization paths

This module composes the local normalization contracts from the `_clz` return at PC 5368 to the
outer quotient-loop cursor at PC 5450.  The zero-shift path executes Solidity's `MCOPY`; the
positive-shift path executes every checked limb load, shift, store, and final carry write.  Keeping
the paths separate is necessary for their exact, path-sensitive gas, not a computational shortcut.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookNormalizationFunction

open MultiLimbSchoolbookNormalization

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

def positiveDivisorResult (mem : ByteArray) (aw divisor v : UInt256)
    (kEff shift : Nat) : DivisorShiftResult :=
  shiftDivisor aw divisor v shift 0 kEff mem ⟨0⟩

def positiveDividendResult (mem : ByteArray) (aw divisor v u : UInt256)
    (kEff m shift : Nat) : DivisorShiftResult :=
  let divisorResult := positiveDivisorResult mem aw divisor v kEff shift
  shiftDivisor aw u u shift 0 m divisorResult.memory ⟨0⟩

def positiveMemory (mem : ByteArray) (aw divisor v u : UInt256)
    (kEff m shift : Nat) : ByteArray :=
  let result := positiveDividendResult mem aw divisor v u kEff m shift
  storeDividendTopCarry result.memory u m result.carry

def positiveSteps (mem : ByteArray) (aw divisor v u : UInt256)
    (kEff m shift : Nat) : Nat :=
  (positiveDivisorResult mem aw divisor v kEff shift).steps +
    (positiveDividendResult mem aw divisor v u kEff m shift).steps + 182

def positiveGas (mem : ByteArray) (aw divisor v u : UInt256)
    (fp kEff m shift : Nat) : Nat :=
  vAllocationGas aw fp kEff +
    (positiveDivisorResult (vMemory mem fp kEff) (vWords aw fp kEff)
      divisor v kEff shift).gas +
    (positiveDividendResult (vMemory mem fp kEff) (vWords aw fp kEff)
      divisor v u kEff m shift).gas + 337

/-- Complete the positive-shift normalization path, including all limb computations. -/
theorem positiveExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kEff m numQ ret shift : Nat} {tail : List UInt256}
    {rem quotient u divisor vTop : UInt256}
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hkEffPos : 0 < kEff) (hkEffLe : kEff ≤ 32)
    (hkEffWord : kEff < UInt256.size)
    (hmWord : m < UInt256.size) (hmSuccWord : m + 1 < UInt256.size)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kEff < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdivisorValid : ValidDivisorShift (vWords aw fp kEff) divisor
      (UInt256.ofNat fp) kEff shift 0 kEff (vMemory mem fp kEff) ⟨0⟩)
    (hdividendValid : ValidDivisorShift (vWords aw fp kEff) u u (m + 1)
      shift 0 m
      (positiveDivisorResult (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) kEff shift).memory ⟨0⟩)
    (huHeader : arrayHeader
      (positiveDividendResult (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift).memory
      (vWords aw fp kEff) u = UInt256.ofNat (m + 1))
    (huHeaderAw : arrayAfterHeader (vWords aw fp kEff) u = vWords aw fp kEff)
    (huTopAw : arrayAfterWord (vWords aw fp kEff) u m = vWords aw fp kEff)
    (hvHeader : arrayHeader
      (positiveMemory (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (vWords aw fp kEff) (UInt256.ofNat fp) = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader (vWords aw fp kEff) (UInt256.ofNat fp) =
      vWords aw fp kEff)
    (hvTopAw : arrayAfterWord (vWords aw fp kEff) (UInt256.ofNat fp) (kEff - 1) =
      vWords aw fp kEff)
    (hvTop : arrayWord
      (positiveMemory (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (vWords aw fp kEff) (UInt256.ofNat fp) (kEff - 1) = vTop)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat shift :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff ::
        UInt256.ofNat m :: quotient :: u :: UInt256.ofNat numQ :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5450⟩
      (UInt256.ofNat shift :: UInt256.ofNat ret :: rem :: UInt256.ofNat numQ ::
        UInt256.ofNat kEff :: UInt256.ofNat fp :: quotient :: u :: vTop :: ⟨1⟩ :: tail)
      (positiveMemory (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (vWords aw fp kEff) rdata acc
      (steps + positiveSteps (vMemory mem fp kEff) (vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (gasUsed + positiveGas mem aw divisor (UInt256.ofNat fp) u fp kEff m shift) := by
  have rd5378 := vAllocationExact hkEffLe hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by omega) h
  have rd5391 := dispatchShiftNonzeroExact hshiftPos
    (lt_trans hshift (by decide)) (by omega) rd5378
  have rd5402 := shiftAllDivisorLimbsExact hkEffWord hshift hdivisorValid
    (by omega) rd5391
  have rd5416 := shiftAllDividendLimbsExact (mCount := m) (uCount := m + 1)
    (by omega) hmSuccWord hmWord hshift hdividendValid (by omega) rd5402
  have rd5428 := storeDividendTopCarryExact (mCount := m) (uCount := m + 1)
    (by omega) hmWord hmSuccWord huHeader huHeaderAw huTopAw (by omega) rd5416
  have rd5450 := loadNormalizedTopExact (tail := tail) hkEffPos hkEffWord hvHeader hvHeaderAw
    hvTopAw hvTop (by omega) rd5428
  have normalized := rd5450.withIndices
    (k' := steps + positiveSteps (vMemory mem fp kEff) (vWords aw fp kEff)
      divisor (UInt256.ofNat fp) u kEff m shift)
    (C' := gasUsed + positiveGas mem aw divisor (UInt256.ofNat fp) u fp kEff m shift)
    (by simp [positiveSteps, positiveDivisorResult, positiveDividendResult]; omega)
    (by simp [positiveGas, positiveDivisorResult, positiveDividendResult]; omega)
  simpa [positiveMemory, positiveDividendResult, positiveDivisorResult] using normalized

def zeroMemory (mem : ByteArray) (divisor fp kEff : Nat) : ByteArray :=
  shiftZeroMemory (vMemory mem fp kEff) divisor fp kEff

def zeroWords (aw : UInt256) (divisor fp kEff : Nat) : UInt256 :=
  shiftZeroWords (vWords aw fp kEff) divisor fp kEff

def zeroGas (aw : UInt256) (divisor fp kEff : Nat) : Nat :=
  vAllocationGas aw fp kEff +
    shiftZeroCopyGas (vWords aw fp kEff) divisor fp kEff + 230

/-- Complete the zero-shift normalization path through the actual `MCOPY`. -/
theorem zeroExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp divisor kEff m numQ ret : Nat} {tail : List UInt256}
    {rem quotient u vTop : UInt256}
    (hkEffPos : 0 < kEff) (hkEffLe : kEff ≤ 32)
    (hkEffWord : kEff < UInt256.size)
    (hkBytes : 32 * kEff < UInt256.size)
    (hdivisor32 : divisor + 32 < UInt256.size) (hfp32 : fp + 32 < UInt256.size)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kEff < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvHeader : arrayHeader (zeroMemory mem divisor fp kEff)
      (zeroWords aw divisor fp kEff) (UInt256.ofNat fp) = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader (zeroWords aw divisor fp kEff) (UInt256.ofNat fp) =
      zeroWords aw divisor fp kEff)
    (hvTopAw : arrayAfterWord (zeroWords aw divisor fp kEff) (UInt256.ofNat fp)
      (kEff - 1) = zeroWords aw divisor fp kEff)
    (hvTop : arrayWord (zeroMemory mem divisor fp kEff) (zeroWords aw divisor fp kEff)
      (UInt256.ofNat fp) (kEff - 1) = vTop)
    (htail : tail.length ≤ 1003)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (⟨0⟩ :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff :: UInt256.ofNat m ::
        quotient :: u :: UInt256.ofNat numQ :: UInt256.ofNat divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5450⟩
      (⟨0⟩ :: UInt256.ofNat ret :: rem :: UInt256.ofNat numQ :: UInt256.ofNat kEff ::
        UInt256.ofNat fp :: quotient :: u :: vTop :: ⟨0⟩ :: tail)
      (zeroMemory mem divisor fp kEff) (zeroWords aw divisor fp kEff)
      rdata acc (steps + 152) (gasUsed + zeroGas aw divisor fp kEff) := by
  have rd5378 := vAllocationExact hkEffLe hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by omega) h
  have rd6194 := dispatchShiftZeroExact (by omega) rd5378
  have rd5428 := shiftZeroCopyExact hkBytes hdivisor32 hfp32 (by omega) rd6194
  have rd5450 := loadNormalizedTopExact (tail := tail) hkEffPos hkEffWord hvHeader hvHeaderAw
    hvTopAw hvTop (by omega) rd5428
  have normalized := rd5450.withIndices
    (k' := steps + 152) (C' := gasUsed + zeroGas aw divisor fp kEff)
    (by omega) (by simp [zeroGas]; omega)
  simpa [zeroMemory, zeroWords] using normalized

end Modexp.MultiLimbSchoolbookNormalizationFunction
