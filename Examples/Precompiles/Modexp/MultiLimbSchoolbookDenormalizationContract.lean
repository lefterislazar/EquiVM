import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionContract

/-!
# Normalized schoolbook remainder extraction

This module covers the normalized division exit and the right-shift loop that writes the
denormalized remainder.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDenormalization

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

open Modexp.MultiLimbSchoolbookNormalization

def denormalizedLowWord (word : UInt256) (shift : Nat) : UInt256 :=
  word.shiftRight (UInt256.ofNat shift)

def denormalizedWord (word next : UInt256) (shift : Nat) : UInt256 :=
  UInt256.lor (denormalizedLowWord word shift)
    (next.shiftLeft (UInt256.ofNat (256 - shift)))

def storeRemainderWord
    (mem : ByteArray) (rem : UInt256) (index : Nat) (value : UInt256) : ByteArray :=
  value.toByteArray.write 0 mem (arrayAddress rem index).toNat 32

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

/-- Finish the successful checked `x + 1` helper after a trace has reached its guard. -/
private theorem checkedAddOneContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x ret : Nat} {tail : List UInt256}
    (hx : x + 1 < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨1335⟩
      (⟨1037⟩ :: (UInt256.ofNat (x + 1)).lt (UInt256.ofNat x) ::
        UInt256.ofNat ret :: UInt256.ofNat (x + 1) :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x + 1) :: tail) mem aw rdata acc (k + 2) (C + 18) := by
  have hxWord : x < UInt256.size := by omega
  have hcondition : UInt256.lt (UInt256.ofNat (x + 1)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hx, UInt256.toNat_ofNat_of_lt hxWord]
    omega
  have rd1336 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 2) (C' := C + 18) (by omega) (by omega)
  simpa using normalized

/-- Exit the completed quotient loop, select the normalized remainder path, and initialize its
index at zero.  The trailing `1` is the normalization marker established by the normalized setup
path. -/
theorem normalizedLoopSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {shift ret rem kEff v quotient u vTop : UInt256}
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: shift :: ret :: rem :: ⟨0⟩ ::
        kEff :: v :: quotient :: u :: vTop :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (⟨0⟩ : UInt256).lt kEff :: ⟨0⟩ :: shift :: u :: kEff ::
        ret :: rem :: quotient :: tail)
      mem aw rdata acc (k + 23) (C + 73) := by
  have houter : (⟨0⟩ : UInt256).isZero ≠ ⟨0⟩ := by native_decide
  have rd5901 := h.jumpiT (by native_decide) houter (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5918 := GeneratedTraces.trace_5894_body
    (by omega) rd5901
  have hnormalized : (⟨1⟩ : UInt256).isZero = ⟨0⟩ := by native_decide
  have rd5919 := rd5918.jumpiNT (by native_decide) hnormalized
    (by simp only [List.length_cons]; omega)
  have rd5927 := GeneratedTraces.trace_5912_body
    (by simp only [List.length_cons]; omega) rd5919
  have normalized := rd5927.withIndices
    (k' := k + 23) (C' := C + 73) (by omega) (by omega)
  simpa using normalized

/-- Execute the terminal normalized-remainder limb.  Since `i + 1 = kEff`, this path stores
only the right-shifted current limb and skips the neighboring-limb contribution. -/
theorem denormalizeTerminalCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i uCount kEff shift : Nat} {tail : List UInt256}
    {ret rem quotient u word : UInt256}
    (hi : i < kEff)
    (hterminal : i + 1 = kEff)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hshift : 0 < shift)
    (hshiftBound : shift < 256)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : arrayAfterWord aw u i = aw)
    (huWord : arrayWord mem aw u i = word)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : arrayAfterWord aw rem i = aw)
    (hdepth : tail.length ≤ 1010)
    (h : RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat i).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat i :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        ret :: rem :: quotient :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat (i + 1)).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat (i + 1) :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        ret :: rem :: quotient :: tail)
      (storeRemainderWord mem rem i (denormalizedLowWord word shift)) aw rdata acc
      (k + 81) (C + 295) := by
  have hiUCount : i < uCount := lt_of_lt_of_le hi hkEffLe
  have hiWord : i < UInt256.size := lt_trans hiUCount huCountWord
  have hiSuccWord : i + 1 < UInt256.size := by omega
  have hloopNe : (UInt256.ofNat i).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
  have huGuard := arrayGuardExact mem aw u i uCount hiUCount hiWord huCountWord huHeader
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
  have rd5933 := h.jumpiT (by native_decide) hloopNe (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1538a := GeneratedTraces.trace_5926_body
    (by simp only [List.length_cons]; omega) rd5933
  have rd1539a := rd1538a.jumpiNT (by native_decide) huGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAwRaw] at rd1539a
  have rd5946 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1538b := GeneratedTraces.trace_5939_body
    (by simp only [List.length_cons]; omega) rd5946
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538b
  rw [huWordRaw] at rd1538b
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538b
  rw [huWordAwRaw, hremHeaderAwRaw] at rd1538b
  have rd1539b := rd1538b.jumpiNT (by native_decide) hremGuardRaw
    (by simp only [List.length_cons]; omega)
  have rd5959 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd1335 := GeneratedTraces.trace_5952_body
    (by simp only [List.length_cons]; omega) rd5959
  rw [← MultiLimbOddCompare.afterHeader_generated, hremWordAwRaw] at rd1335
  have hiAdd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) :=
    ofNat_add_bounded hiSuccWord
  rw [hiAdd] at rd1335
  have rd5970 := checkedAddOneContinueExact (x := i) (ret := 5963)
    hiSuccWord (by native_decide) (by simp only [List.length_cons]; omega) rd1335
  have hterminalBranch :
      (UInt256.ofNat (i + 1)).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hiSuccWord,
      UInt256.toNat_ofNat_of_lt hkEffWord]
    omega
  have rd5976 := GeneratedTraces.trace_5963_notTaken
    (by simp only [List.length_cons]; omega) rd5970
    (by native_decide) hterminalBranch
  have rd5927 := GeneratedTraces.trace_5969_body
    (by simp only [List.length_cons]; omega) rd5976
  rw [hiAdd] at rd5927
  have normalized := rd5927.withIndices
    (k' := k + 81) (C' := C + 295) (by omega) (by omega)
  simpa only [denormalizedLowWord, storeRemainderWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

/-- Execute a nonterminal normalized-remainder limb.  The first store writes the shifted current
limb; the second store ORs in the high contribution from `u[i+1]`. -/
theorem denormalizeContinueCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i uCount kEff shift : Nat} {tail : List UInt256}
    {ret rem quotient u word next : UInt256}
    (hi : i + 1 < kEff)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hshift : 0 < shift)
    (hshiftBound : shift < 256)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : arrayAfterWord aw u i = aw)
    (huWord : arrayWord mem aw u i = word)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : arrayAfterWord aw rem i = aw)
    (huHeaderAfterLow :
      arrayHeader (storeRemainderWord mem rem i (denormalizedLowWord word shift)) aw u =
        UInt256.ofNat uCount)
    (huNextAfterLow :
      arrayWord (storeRemainderWord mem rem i (denormalizedLowWord word shift)) aw u (i + 1) =
        next)
    (huNextAw : arrayAfterWord aw u (i + 1) = aw)
    (hremHeaderAfterLow :
      arrayHeader (storeRemainderWord mem rem i (denormalizedLowWord word shift)) aw rem =
        UInt256.ofNat kEff)
    (hremLowAfterLow :
      arrayWord (storeRemainderWord mem rem i (denormalizedLowWord word shift)) aw rem i =
        denormalizedLowWord word shift)
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat i).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat i :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        ret :: rem :: quotient :: tail) mem aw rdata acc k C) :
    let lowMem := storeRemainderWord mem rem i (denormalizedLowWord word shift)
    RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat (i + 1)).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat (i + 1) :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        ret :: rem :: quotient :: tail)
      (storeRemainderWord lowMem rem i (denormalizedWord word next shift)) aw rdata acc
      (k + 185) (C + 675) := by
  have hiCurrent : i < kEff := by omega
  have hiCurrentUCount : i < uCount := lt_of_lt_of_le hiCurrent hkEffLe
  have hiSuccUCount : i + 1 < uCount := lt_of_lt_of_le hi hkEffLe
  have hiWord : i < UInt256.size := lt_trans hiCurrentUCount huCountWord
  have hiSuccWord : i + 1 < UInt256.size := lt_trans hiSuccUCount huCountWord
  have hloopNe : (UInt256.ofNat i).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hiCurrent
  have hcontinueNe :
      (UInt256.ofNat (i + 1)).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSuccWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
  have huGuard := arrayGuardExact mem aw u i uCount hiCurrentUCount hiWord huCountWord huHeader
  have hremGuard :=
    arrayGuardExact mem aw rem i kEff hiCurrent hiWord hkEffWord hremHeader
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
  have rd5933 := h.jumpiT (by native_decide) hloopNe (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1538a := GeneratedTraces.trace_5926_body
    (by simp only [List.length_cons]; omega) rd5933
  have rd1539a := rd1538a.jumpiNT (by native_decide) huGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAwRaw] at rd1539a
  have rd5946 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1538b := GeneratedTraces.trace_5939_body
    (by simp only [List.length_cons]; omega) rd5946
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538b
  rw [huWordRaw] at rd1538b
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538b
  rw [huWordAwRaw, hremHeaderAwRaw] at rd1538b
  have rd1539b := rd1538b.jumpiNT (by native_decide) hremGuardRaw
    (by simp only [List.length_cons]; omega)
  have rd5959 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd1335 := GeneratedTraces.trace_5952_body
    (by simp only [List.length_cons]; omega) rd5959
  rw [← MultiLimbOddCompare.afterHeader_generated, hremWordAwRaw] at rd1335
  have hiAdd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) :=
    ofNat_add_bounded hiSuccWord
  rw [hiAdd] at rd1335
  have rd5970 := checkedAddOneContinueExact (x := i) (ret := 5963)
    hiSuccWord (by native_decide) (by simp only [List.length_cons]; omega) rd1335
  have rd5982 := GeneratedTraces.trace_5963_taken
    (by simp only [List.length_cons]; omega) rd5970
    (by native_decide) hcontinueNe (by native_decide)
  have rd1335b := GeneratedTraces.trace_5975_body
    (by simp only [List.length_cons]; omega) rd5982
  rw [hiAdd] at rd1335b
  have rd5994 := checkedAddOneContinueExact (x := i) (ret := 5987)
    hiSuccWord (by native_decide) (by simp only [List.length_cons]; omega) rd1335b
  let lowMem := storeRemainderWord mem rem i (denormalizedLowWord word shift)
  have huNextGuard := arrayGuardExact lowMem aw u (i + 1) uCount hiSuccUCount
    hiSuccWord huCountWord huHeaderAfterLow
  have huNextGuardRaw :
      ((UInt256.ofNat (i + 1)).lt
        (if u.toNat ≥ lowMem.size ∨ u ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (lowMem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact huNextGuard
  have huNextRaw :
      MultiLimbOddCompare.headerWord lowMem aw
        ((UInt256.ofNat (i + 1)).shiftLeft ⟨5⟩ + u + ⟨32⟩) = next := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huNextAfterLow
  simp only [lowMem, storeRemainderWord, denormalizedLowWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] at huNextRaw
  unfold MultiLimbOddCompare.elementPtr at huNextRaw
  have huNextAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat (i + 1)).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huNextAw
  have huHeaderAfterLowAw : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have rd1538c := GeneratedTraces.trace_5987_body
    (by simp only [List.length_cons]; omega) rd5994
  have rd1539c := rd1538c.jumpiNT (by native_decide) huNextGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAfterLowAw] at rd1539c
  have rd6000 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539c
    (by native_decide) (by native_decide)
  have rd1056 := GeneratedTraces.trace_5993_body
    (by simp only [List.length_cons]; omega) rd6000
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1056
  rw [huNextRaw] at rd1056
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1056
  rw [huNextAwRaw] at rd1056
  have rd6010 := MultiLimbSchoolbookNormalization.checked256SubContinueExact
    (shift := shift) (ret := 6003) (Nat.le_of_lt hshiftBound) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1056
  have hremGuardAfterLow := arrayGuardExact lowMem aw rem i kEff hiCurrent
    hiWord hkEffWord hremHeaderAfterLow
  have hremGuardAfterLowRaw :
      ((UInt256.ofNat i).lt
        (if rem.toNat ≥ lowMem.size ∨ rem ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (lowMem.readWithPadding rem.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hremGuardAfterLow
  have hremLowRaw :
      MultiLimbOddCompare.headerWord lowMem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + rem + ⟨32⟩) =
          denormalizedLowWord word shift := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hremLowAfterLow
  simp only [lowMem, storeRemainderWord, denormalizedLowWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] at hremLowRaw
  unfold MultiLimbOddCompare.elementPtr at hremLowRaw
  have hremHeaderAfterLowAw : MultiLimbOddCompare.afterHeader aw rem = aw := hremHeaderAw
  have rd1538d := GeneratedTraces.trace_6003_body
    (by simp only [List.length_cons]; omega) rd6010
  have rd1539d := rd1538d.jumpiNT (by native_decide) hremGuardAfterLowRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, hremHeaderAfterLowAw] at rd1539d
  have rd6021 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539d
    (by native_decide) (by native_decide)
  have rd1538e := GeneratedTraces.trace_6014_body
    (by simp only [List.length_cons]; omega) rd6021
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538e
  rw [hremLowRaw] at rd1538e
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538e
  rw [hremWordAwRaw, hremHeaderAfterLowAw] at rd1538e
  have rd1539e := rd1538e.jumpiNT (by native_decide) hremGuardAfterLowRaw
    (by simp only [List.length_cons]; omega)
  have rd6033 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539e
    (by native_decide) (by native_decide)
  have rd5927 := GeneratedTraces.trace_6026_body
    (by simp only [List.length_cons]; omega) rd6033
  rw [← MultiLimbOddCompare.afterHeader_generated, hremWordAwRaw] at rd5927
  rw [hiAdd] at rd5927
  have normalized := rd5927.withIndices
    (k' := k + 185) (C' := C + 675) (by omega) (by omega)
  simpa only [lowMem, denormalizedWord, denormalizedLowWord, storeRemainderWord,
    arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

structure DenormalizeResult where
  memory : ByteArray
  steps : Nat
  gas : Nat

/-- Pure execution recurrence for a consecutive normalized-remainder range. -/
def denormalizeRange (aw u rem : UInt256) (shift : Nat) :
    Nat → Nat → ByteArray → DenormalizeResult
  | _, 0, mem => ⟨mem, 0, 0⟩
  | index, 1, mem =>
      let word := arrayWord mem aw u index
      ⟨storeRemainderWord mem rem index (denormalizedLowWord word shift), 81, 295⟩
  | index, count + 2, mem =>
      let word := arrayWord mem aw u index
      let lowMem := storeRemainderWord mem rem index (denormalizedLowWord word shift)
      let next := arrayWord lowMem aw u (index + 1)
      let nextMem := storeRemainderWord lowMem rem index (denormalizedWord word next shift)
      let rest := denormalizeRange aw u rem shift (index + 1) (count + 1) nextMem
      ⟨rest.memory, 185 + rest.steps, 675 + rest.gas⟩

/-- Memory and bounds facts needed by every state of the denormalization recurrence. -/
inductive ValidDenormalize
    (aw u rem : UInt256) (uCount kEff shift : Nat) : Nat → Nat → ByteArray → Prop
  | zero (index : Nat) (mem : ByteArray) :
      ValidDenormalize aw u rem uCount kEff shift index 0 mem
  | terminal (index : Nat) (mem : ByteArray)
      (hterminal : index + 1 = kEff)
      (hkEffLe : kEff ≤ uCount)
      (hkEffWord : kEff < UInt256.size)
      (huCountWord : uCount < UInt256.size)
      (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
      (huHeaderAw : arrayAfterHeader aw u = aw)
      (huWordAw : arrayAfterWord aw u index = aw)
      (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
      (hremHeaderAw : arrayAfterHeader aw rem = aw)
      (hremWordAw : arrayAfterWord aw rem index = aw) :
      ValidDenormalize aw u rem uCount kEff shift index 1 mem
  | step (index count : Nat) (mem : ByteArray)
      (hi : index + 1 < kEff)
      (hkEffLe : kEff ≤ uCount)
      (hkEffWord : kEff < UInt256.size)
      (huCountWord : uCount < UInt256.size)
      (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
      (huHeaderAw : arrayAfterHeader aw u = aw)
      (huWordAw : arrayAfterWord aw u index = aw)
      (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
      (hremHeaderAw : arrayAfterHeader aw rem = aw)
      (hremWordAw : arrayAfterWord aw rem index = aw)
      (huHeaderAfterLow :
        let word := arrayWord mem aw u index
        arrayHeader (storeRemainderWord mem rem index (denormalizedLowWord word shift)) aw u =
          UInt256.ofNat uCount)
      (huNextAw : arrayAfterWord aw u (index + 1) = aw)
      (hremHeaderAfterLow :
        let word := arrayWord mem aw u index
        arrayHeader (storeRemainderWord mem rem index (denormalizedLowWord word shift)) aw rem =
          UInt256.ofNat kEff)
      (hremLowAfterLow :
        let word := arrayWord mem aw u index
        arrayWord (storeRemainderWord mem rem index (denormalizedLowWord word shift)) aw rem index =
          denormalizedLowWord word shift)
      (hrest :
        let word := arrayWord mem aw u index
        let lowMem := storeRemainderWord mem rem index (denormalizedLowWord word shift)
        let next := arrayWord lowMem aw u (index + 1)
        let nextMem := storeRemainderWord lowMem rem index (denormalizedWord word next shift)
        ValidDenormalize aw u rem uCount kEff shift (index + 1) (count + 1) nextMem) :
      ValidDenormalize aw u rem uCount kEff shift index (count + 2) mem

/-- Execute any valid consecutive range of normalized-remainder iterations. -/
theorem denormalizeCyclesExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C index count uCount kEff shift : Nat} {tail : List UInt256}
    {ret rem quotient u : UInt256} {mem : ByteArray}
    (hshift : 0 < shift)
    (hshiftBound : shift < 256)
    (hvalid : ValidDenormalize aw u rem uCount kEff shift index count mem)
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat index).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat index :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        ret :: rem :: quotient :: tail) mem aw rdata acc k C) :
    let result := denormalizeRange aw u rem shift index count mem
    RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat (index + count)).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat (index + count) :: UInt256.ofNat shift :: u ::
        UInt256.ofNat kEff :: ret :: rem :: quotient :: tail)
      result.memory aw rdata acc (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | zero current currentMem =>
      simpa [denormalizeRange] using h
  | terminal current currentMem hterminal hkEffLe hkEffWord huCountWord huHeader huHeaderAw huWordAw
      hremHeader hremHeaderAw hremWordAw =>
      let word := arrayWord currentMem aw u current
      have rd := denormalizeTerminalCycleExact
        (i := current) (kEff := kEff) (shift := shift) (word := word)
        (by omega) hterminal hkEffLe hkEffWord huCountWord hshift hshiftBound
        huHeader huHeaderAw
        huWordAw rfl hremHeader hremHeaderAw hremWordAw
        (by omega) h
      simpa [denormalizeRange] using rd
  | step current remaining currentMem hi hkEffLe hkEffWord huCountWord huHeader huHeaderAw huWordAw
      hremHeader hremHeaderAw hremWordAw huHeaderAfterLow huNextAw
      hremHeaderAfterLow hremLowAfterLow hrest ih =>
      let word := arrayWord currentMem aw u current
      let lowMem := storeRemainderWord currentMem rem current
        (denormalizedLowWord word shift)
      let next := arrayWord lowMem aw u (current + 1)
      let nextMem := storeRemainderWord lowMem rem current
        (denormalizedWord word next shift)
      have rdCycle := denormalizeContinueCycleExact
        (i := current) (kEff := kEff) (shift := shift) (word := word) (next := next)
        hi hkEffLe hkEffWord huCountWord hshift hshiftBound huHeader huHeaderAw huWordAw rfl
        hremHeader hremHeaderAw hremWordAw huHeaderAfterLow rfl huNextAw
        hremHeaderAfterLow hremLowAfterLow (by omega) h
      have rdRest := ih (k := k + 185) (C := C + 675) rdCycle
      have hindex : current + 1 + (remaining + 1) = current + (remaining + 2) := by
        omega
      rw [hindex] at rdRest
      simpa [denormalizeRange, word, lowMem, next, nextMem, Nat.add_assoc] using rdRest

/-- Leave the completed denormalization loop and return the remainder/quotient pair to the
caller. -/
theorem denormalizeLoopExitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff shift retPc : Nat} {tail : List UInt256}
    {rem quotient u : UInt256}
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 1015)
    (h : RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) ::
        UInt256.ofNat kEff :: UInt256.ofNat shift :: u :: UInt256.ofNat kEff ::
        UInt256.ofNat retPc :: rem :: quotient :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) mem aw rdata acc (k + 6) (C + 26) := by
  have hexit : (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    omega
  have rd5928 := h.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_5921_jump
    (by simp only [List.length_cons]; omega) rd5928
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 6) (C' := C + 26) (by omega) (by omega)
  simpa using normalized

/-- Execute the complete normalized-remainder loop and return to its caller. -/
theorem denormalizeAllExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C uCount kEff shift retPc : Nat} {tail : List UInt256}
    {rem quotient u : UInt256} {mem : ByteArray}
    (hshift : 0 < shift)
    (hshiftBound : shift < 256)
    (hvalid : ValidDenormalize aw u rem uCount kEff shift 0 kEff mem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode ee g s0 ⟨5920⟩
      (⟨5926⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: ⟨0⟩ ::
        UInt256.ofNat shift :: u :: UInt256.ofNat kEff :: UInt256.ofNat retPc ::
        rem :: quotient :: tail) mem aw rdata acc k C) :
    let result := denormalizeRange aw u rem shift 0 kEff mem
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) result.memory aw rdata acc
      (k + result.steps + 6) (C + result.gas + 26) := by
  have rdFinal := denormalizeCyclesExact hshift hshiftBound hvalid hdepth h
  simp only [Nat.zero_add] at rdFinal
  have rdret := denormalizeLoopExitExact (kEff := kEff) (shift := shift)
    (retPc := retPc) (tail := tail)
    hret (by omega) rdFinal
  have normalized := rdret.withIndices
    (k' := k + (denormalizeRange aw u rem shift 0 kEff mem).steps + 6)
    (C' := C + (denormalizeRange aw u rem shift 0 kEff mem).gas + 26)
    (by omega) (by omega)
  simpa using normalized

end Modexp.MultiLimbSchoolbookDenormalization
