import Examples.Precompiles.Modexp.MultiLimbSchoolbookDenormalizationContract

/-!
# Zero-shift schoolbook remainder extraction

When normalization computes `shift = 0`, the deployed division code copies `u[0..kEff)` directly
to the remainder array.  This module covers that separate loop and its exact return path.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookZeroShiftRemainder

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookDenormalization

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem arrayGuardExact
    (mem : ByteArray) (aw array : UInt256) (index count : Nat)
    (hindex : index < count)
    (hindexWord : index < UInt256.size)
    (hcountWord : count < UInt256.size)
    (hheader : arrayHeader mem aw array = UInt256.ofNat count) :
    ((UInt256.ofNat index).lt
      (MultiLimbOddCompare.headerWord mem aw array)).isZero = ⟨0⟩ := by
  have hbound : (UInt256.ofNat index).toNat <
      (MultiLimbOddCompare.headerWord mem aw array).toNat := by
    rw [show MultiLimbOddCompare.headerWord mem aw array = UInt256.ofNat count from
        hheader,
      UInt256.toNat_ofNat_of_lt hindexWord,
      UInt256.toNat_ofNat_of_lt hcountWord]
    exact hindex
  rw [ult_one hbound]
  native_decide

/-- Exit the quotient loop through the zero-normalization dispatch and initialize the direct-copy
loop at index zero. -/
theorem zeroShiftLoopSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ret rem kEff v quotient u vTop : UInt256}
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: ⟨0⟩ :: ret :: rem :: ⟨0⟩ ::
        kEff :: v :: quotient :: u :: vTop :: ⟨0⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (⟨0⟩ : UInt256).lt kEff :: ⟨0⟩ :: u :: kEff :: ret :: rem ::
        quotient :: tail)
      mem aw rdata acc (k + 25) (C + 76) := by
  have houter : (⟨0⟩ : UInt256).isZero ≠ ⟨0⟩ := by native_decide
  have rd5894 := h.jumpiT (by native_decide) houter (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5911 := GeneratedTraces.trace_5894_body (by omega) rd5894
  have hzeroShift : (⟨0⟩ : UInt256).isZero ≠ ⟨0⟩ := by native_decide
  have rd6032 := rd5911.jumpiT (by native_decide) hzeroShift (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6042 := GeneratedTraces.trace_6032_body
    (by simp only [List.length_cons]; omega) rd6032
  exact rd6042.withIndices (by omega) (by omega)

/-- Execute one direct-copy remainder limb and expose the next loop guard. -/
theorem copyCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i uCount kEff : Nat} {tail : List UInt256}
    {ret rem quotient u word : UInt256}
    (hi : i < kEff)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : arrayAfterWord aw u i = aw)
    (huWord : arrayWord mem aw u i = word)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : arrayAfterWord aw rem i = aw)
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (UInt256.ofNat i).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat i :: u :: UInt256.ofNat kEff :: ret :: rem :: quotient :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (UInt256.ofNat (i + 1)).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat (i + 1) :: u :: UInt256.ofNat kEff :: ret :: rem :: quotient :: tail)
      (storeRemainderWord mem rem i word) aw rdata acc (k + 58) (C + 208) := by
  have hiWord : i < UInt256.size := lt_trans hi hkEffWord
  have hiSuccWord : i + 1 < UInt256.size := by omega
  have hloop : (UInt256.ofNat i).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
  have huGuard := arrayGuardExact mem aw u i uCount (by omega) hiWord huCountWord huHeader
  have hremGuard := arrayGuardExact mem aw rem i kEff hi hiWord hkEffWord hremHeader
  have huGuardRaw :
      ((UInt256.ofNat i).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact huGuard
  have hremGuardRaw :
      ((UInt256.ofNat i).lt
        (if rem.toNat ≥ mem.size ∨ rem ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding rem.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hremGuard
  have huWordRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + u + ⟨32⟩) = word := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huWord
  have huWordAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huWordAw
  have hremWordAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + rem + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hremWordAw
  have huHeaderAwRaw : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have hremHeaderAwRaw : MultiLimbOddCompare.afterHeader aw rem = aw := hremHeaderAw
  have rd6047 := h.jumpiT (by native_decide) hloop (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1538a := GeneratedTraces.trace_6047_body
    (by simp only [List.length_cons]; omega) rd6047
  have rd1539a := rd1538a.jumpiNT (by native_decide) huGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAwRaw] at rd1539a
  have rd6060 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1538b := GeneratedTraces.trace_6060_body
    (by simp only [List.length_cons]; omega) rd6060
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538b
  rw [huWordRaw] at rd1538b
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538b
  rw [huWordAwRaw, hremHeaderAwRaw] at rd1538b
  have rd1539b := rd1538b.jumpiNT (by native_decide) hremGuardRaw
    (by simp only [List.length_cons]; omega)
  have rd6071 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd6042 := GeneratedTraces.trace_6071_body
    (by simp only [List.length_cons]; omega) rd6071
  rw [← MultiLimbOddCompare.afterHeader_generated, hremWordAwRaw] at rd6042
  have hiAdd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) :=
    ofNat_add_bounded hiSuccWord
  rw [hiAdd] at rd6042
  have normalized := rd6042.withIndices
    (k' := k + 58) (C' := C + 208) (by omega) (by omega)
  simpa only [storeRemainderWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

structure CopyResult where
  memory : ByteArray
  steps : Nat
  gas : Nat

def copyRange (aw u rem : UInt256) : Nat → Nat → ByteArray → CopyResult
  | _, 0, mem => ⟨mem, 0, 0⟩
  | index, count + 1, mem =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      let rest := copyRange aw u rem (index + 1) count nextMem
      ⟨rest.memory, 58 + rest.steps, 208 + rest.gas⟩

@[simp] theorem copyRange_steps
    (aw u rem : UInt256) (index count : Nat) (mem : ByteArray) :
    (copyRange aw u rem index count mem).steps = 58 * count := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      simp only [copyRange, ih]
      omega

@[simp] theorem copyRange_gas
    (aw u rem : UInt256) (index count : Nat) (mem : ByteArray) :
    (copyRange aw u rem index count mem).gas = 208 * count := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      simp only [copyRange, ih]
      omega

/-- Memory and bounds facts for each state of the direct-copy recurrence. -/
inductive ValidCopy (aw u rem : UInt256) (uCount kEff : Nat) :
    Nat → Nat → ByteArray → Prop
  | zero (index : Nat) (mem : ByteArray) : ValidCopy aw u rem uCount kEff index 0 mem
  | step (index count : Nat) (mem : ByteArray)
      (hi : index < kEff)
      (hkEffLe : kEff ≤ uCount)
      (hkEffWord : kEff < UInt256.size)
      (huCountWord : uCount < UInt256.size)
      (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
      (huHeaderAw : arrayAfterHeader aw u = aw)
      (huWordAw : arrayAfterWord aw u index = aw)
      (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
      (hremHeaderAw : arrayAfterHeader aw rem = aw)
      (hremWordAw : arrayAfterWord aw rem index = aw)
      (hrest :
        let word := arrayWord mem aw u index
        let nextMem := storeRemainderWord mem rem index word
        ValidCopy aw u rem uCount kEff (index + 1) count nextMem) :
      ValidCopy aw u rem uCount kEff index (count + 1) mem

/-- Execute any valid consecutive range of direct-copy iterations. -/
theorem copyCyclesExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C index count uCount kEff : Nat} {tail : List UInt256}
    {ret rem quotient u : UInt256} {mem : ByteArray}
    (hvalid : ValidCopy aw u rem uCount kEff index count mem)
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (UInt256.ofNat index).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat index :: u :: UInt256.ofNat kEff :: ret :: rem :: quotient :: tail)
      mem aw rdata acc k C) :
    let result := copyRange aw u rem index count mem
    RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (UInt256.ofNat (index + count)).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat (index + count) :: u :: UInt256.ofNat kEff :: ret :: rem ::
        quotient :: tail)
      result.memory aw rdata acc (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | zero current currentMem =>
      simpa [copyRange] using h
  | step current remaining currentMem hi hkEffLe hkEffWord huCountWord huHeader huHeaderAw huWordAw
      hremHeader hremHeaderAw hremWordAw hrest ih =>
      let word := arrayWord currentMem aw u current
      let nextMem := storeRemainderWord currentMem rem current word
      have rdCycle := copyCycleExact hi hkEffLe hkEffWord huCountWord huHeader huHeaderAw huWordAw rfl
        hremHeader hremHeaderAw hremWordAw (by omega) h
      have rdRest := ih (k := k + 58) (C := C + 208) rdCycle
      have hindex : current + 1 + remaining = current + (remaining + 1) := by omega
      rw [hindex] at rdRest
      simpa [copyRange, word, nextMem, Nat.add_assoc] using rdRest

/-- Leave the completed direct-copy loop and return the remainder/quotient pair to the caller. -/
theorem copyLoopExitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff retPc : Nat} {tail : List UInt256}
    {rem quotient u : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat kEff :: u :: UInt256.ofNat kEff :: UInt256.ofNat retPc :: rem ::
        quotient :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) mem aw rdata acc (k + 5) (C + 24) := by
  have hexit : (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hkEffWord]
  have rd6043 := h.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_6043_jump
    (by simp only [List.length_cons]; omega) rd6043
    (by native_decide) hret
  exact rdret.withIndices (by omega) (by omega)

/-- Execute all `kEff` direct-copy limbs and return. -/
theorem copyAllExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C uCount kEff retPc : Nat} {tail : List UInt256}
    {rem quotient u : UInt256} {mem : ByteArray}
    (hkEffWord : kEff < UInt256.size)
    (hvalid : ValidCopy aw u rem uCount kEff 0 kEff mem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨6042⟩
      (⟨6047⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: ⟨0⟩ :: u ::
        UInt256.ofNat kEff :: UInt256.ofNat retPc :: rem :: quotient :: tail)
      mem aw rdata acc k C) :
    let result := copyRange aw u rem 0 kEff mem
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) result.memory aw rdata acc
      (k + 58 * kEff + 5) (C + 208 * kEff + 24) := by
  have rdEnd := copyCyclesExact hvalid hdepth h
  simp only [zero_add] at rdEnd
  have rdReturn := copyLoopExitExact hkEffWord hret (by omega) rdEnd
  simp only [copyRange_steps, copyRange_gas] at rdReturn
  exact rdReturn.withIndices (by omega) (by omega)

/-- Complete the zero-shift remainder extraction directly from the terminal quotient guard. -/
theorem zeroShiftRemainderExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C uCount kEff retPc : Nat} {tail : List UInt256}
    {rem quotient u v vTop : UInt256} {mem : ByteArray}
    (hkEffWord : kEff < UInt256.size)
    (hvalid : ValidCopy aw u rem uCount kEff 0 kEff mem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: ⟨0⟩ ::
        UInt256.ofNat retPc :: rem :: ⟨0⟩ :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: ⟨0⟩ :: tail) mem aw rdata acc k C) :
    let result := copyRange aw u rem 0 kEff mem
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) result.memory aw rdata acc
      (k + 58 * kEff + 30) (C + 208 * kEff + 100) := by
  have rd6042 := zeroShiftLoopSetupExact (by omega) h
  have rdReturn := copyAllExact hkEffWord hvalid hret hdepth rd6042
  exact rdReturn.withIndices (by omega) (by omega)

end Modexp.MultiLimbSchoolbookZeroShiftRemainder
