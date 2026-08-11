import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationContract
import Examples.Precompiles.Modexp.MultiLimbDiv512Contract
import Examples.Precompiles.Modexp.MultiLimbQhatLoop
import Examples.Precompiles.Modexp.MultiLimbAdditionModel

/-!
# Normalized schoolbook-division outer loop

This module connects the normalized `u` and `v` arrays to the quotient-digit loop.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDivision

open MultiLimbSchoolbookNormalization

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

-- The normalization marker is carried untouched through every quotient iteration.
variable {normalizationMarker : UInt256}

/-- Finish the successful compiler helper for checked addition after a generated trace reaches
its overflow guard. -/
theorem checkedAddContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x y ret : Nat} {tail : List UInt256}
    (hxy : x + y < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1432⟩
      (⟨1037⟩ :: (UInt256.ofNat x).gt (UInt256.ofNat x + UInt256.ofNat y) ::
        UInt256.ofNat ret :: (UInt256.ofNat x + UInt256.ofNat y) :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x + y) :: tail) mem aw rdata acc (k + 2) (C + 18) := by
  have hxWord : x < UInt256.size := by omega
  have hyWord : y < UInt256.size := by omega
  have hadd : UInt256.ofNat x + UInt256.ofNat y = UInt256.ofNat (x + y) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hxWord,
      UInt256.toNat_ofNat_of_lt hyWord, UInt256.toNat_ofNat_of_lt hxy,
      Nat.mod_eq_of_lt hxy]
  have hcondition : UInt256.gt (UInt256.ofNat x) (UInt256.ofNat (x + y)) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxWord, UInt256.toNat_ofNat_of_lt hxy]
    omega
  rw [hadd] at h
  have rd1433 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_1433_jump
    (by simp only [List.length_cons]; omega) rd1433
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 2) (C' := C + 18) (by omega) (by omega)
  simpa using normalized

/-- Finish the successful compiler helper for checked subtraction by two. -/
theorem checkedSubTwoContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x ret : Nat} {tail : List UInt256}
    (hxTwo : 2 ≤ x)
    (hxWord : x < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨1101⟩
      (⟨1037⟩ ::
        (UInt256.ofNat x +
          ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩).gt
          (UInt256.ofNat x) ::
        UInt256.ofNat ret ::
        (UInt256.ofNat x + ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩) ::
        tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x - 2) :: tail) mem aw rdata acc (k + 2) (C + 18) := by
  have hxPredWord : x - 2 < UInt256.size := by omega
  have hconst :
      (⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩ :
        UInt256).toNat = UInt256.size - 2 := by native_decide
  have hsum : x + (UInt256.size - 2) = UInt256.size + (x - 2) := by omega
  have hsub :
      UInt256.ofNat x +
          ⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩ =
        UInt256.ofNat (x - 2) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hxWord, hconst,
      UInt256.toNat_ofNat_of_lt hxPredWord, hsum, Nat.add_mod,
      Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hxPredWord]
  have hcondition : UInt256.gt (UInt256.ofNat (x - 2)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxPredWord,
      UInt256.toNat_ofNat_of_lt hxWord]
    omega
  rw [hsub] at h
  have rd1102 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_1102_jump
    (by simp only [List.length_cons]; omega) rd1102
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 2) (C' := C + 18) (by omega) (by omega)
  simpa using normalized

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

/-- Starting at the common outer-loop body, decrement the positive cursor, load
`u[jj+kEff]` and `u[jj+kEff-1]`, and reach the exact branch deciding which q-hat estimate
construction is used.  The first iteration and every continuation share this deployed body. -/
theorem outerOperandsBodyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cursor kEff uCount : Nat} {tail : List UInt256}
    {shift ret rem v quotient u vTop uHi uLo : UInt256}
    (hcursorPos : 0 < cursor)
    (hcursorWord : cursor < UInt256.size)
    (hkEffPos : 0 < kEff)
    (hsumWord : cursor - 1 + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hhiIndex : cursor - 1 + kEff < uCount)
    (hloIndex : cursor - 1 + kEff - 1 < uCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huHiAw : arrayAfterWord aw u (cursor - 1 + kEff) = aw)
    (huLoAw : arrayAfterWord aw u (cursor - 1 + kEff - 1) = aw)
    (huHi : arrayWord mem aw u (cursor - 1 + kEff) = uHi)
    (huLo : arrayWord mem aw u (cursor - 1 + kEff - 1) = uLo)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5458⟩
      (UInt256.ofNat cursor :: shift :: ret :: rem :: UInt256.ofNat cursor ::
        UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat (cursor - 1) :: vTop ::
        UInt256.ofNat cursor :: uLo :: u :: shift :: ret :: rem ::
        UInt256.ofNat (cursor - 1) :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 108) (C + 387) := by
  let jj := cursor - 1
  let hiIndex := jj + kEff
  let loIndex := hiIndex - 1
  have hjjWord : jj < UInt256.size := by simp only [jj]; omega
  have hhiWord : hiIndex < UInt256.size := by simpa [hiIndex, jj] using hsumWord
  have hloWord : loIndex < UInt256.size := by simp only [loIndex]; omega
  have hpred : UInt256.ofNat cursor + (⟨0⟩ : UInt256).lnot = UInt256.ofNat jj := by
    rw [show cursor = jj + 1 by simp only [jj]; omega, u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (jj + 1)) = UInt256.ofNat jj
    exact MultiLimbOddCompare.scanIndex_ofNat_succ jj (by omega)
  have rd1432a := GeneratedTraces.trace_5458_body
    (by simp only [List.length_cons]; omega) h
  rw [hpred] at rd1432a
  have rd5476 := checkedAddContinueExact (x := jj) (y := kEff) (ret := 5476)
    (by simpa [jj] using hsumWord) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1432a
  have hhiGuard := arrayGuardExact mem aw u hiIndex uCount
    (by simpa [hiIndex, jj] using hhiIndex) hhiWord huCountWord huHeader
  have hhiGuardRaw :
      ((UInt256.ofNat hiIndex).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hhiGuard
  have huHeaderAw' : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have huHiRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat hiIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = uHi := by
    simpa only [hiIndex, jj, arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huHi
  have huHiAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat hiIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [hiIndex, jj, arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huHiAw
  have rd1538a := GeneratedTraces.trace_5476_body
    (by simp only [List.length_cons]; omega) rd5476
  have rd1539a := rd1538a.jumpiNT (by native_decide) hhiGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539a
  have rd5482 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1432b := GeneratedTraces.trace_5482_body
    (by simp only [List.length_cons]; omega) rd5482
  rw [← MultiLimbOddCompare.headerWord_generated, huHiRaw,
    ← MultiLimbOddCompare.afterHeader_generated, huHiAwRaw] at rd1432b
  have rd5502 := checkedAddContinueExact (x := jj) (y := kEff) (ret := 5502)
    (by simpa [jj] using hsumWord) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1432b
  have rd1035 := GeneratedTraces.trace_5502_body
    (by simp only [List.length_cons]; omega) rd5502
  have rd5440 := checkedSubOneContinueExact (x := hiIndex) (ret := 5440)
    (by simp only [hiIndex]; exact Nat.add_pos_right jj hkEffPos) hhiWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1035
  have hloGuard := arrayGuardExact mem aw u loIndex uCount
    (by simpa [loIndex, hiIndex, jj] using hloIndex) hloWord huCountWord huHeader
  have hloGuardRaw :
      ((UInt256.ofNat loIndex).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hloGuard
  have huLoRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat loIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = uLo := by
    simpa only [loIndex, hiIndex, jj, arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huLo
  have huLoAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat loIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [loIndex, hiIndex, jj, arrayAfterWord,
      MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huLoAw
  have rd1538b := GeneratedTraces.trace_5440_body
    (by simp only [List.length_cons]; omega) rd5440
  have rd1539b := rd1538b.jumpiNT (by native_decide) hloGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539b
  have rd5507 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd5516 := GeneratedTraces.trace_5507_body
    (by simp only [List.length_cons]; omega) rd5507
  rw [← MultiLimbOddCompare.headerWord_generated, huLoRaw,
    ← MultiLimbOddCompare.afterHeader_generated, huLoAwRaw] at rd5516
  have normalized := rd5516.withIndices
    (k' := k + 108) (C' := C + 387) (by omega) (by omega)
  simpa only [jj, hiIndex, loIndex] using normalized

/-- Enter the first quotient iteration and execute its common operand-loading body. -/
theorem outerOperandsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C numQ kEff uCount : Nat} {tail : List UInt256}
    {shift ret rem v quotient u vTop uHi uLo : UInt256}
    (hnumQPos : 0 < numQ)
    (hnumQWord : numQ < UInt256.size)
    (hkEffPos : 0 < kEff)
    (hsumWord : numQ - 1 + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hhiIndex : numQ - 1 + kEff < uCount)
    (hloIndex : numQ - 1 + kEff - 1 < uCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huHiAw : arrayAfterWord aw u (numQ - 1 + kEff) = aw)
    (huLoAw : arrayAfterWord aw u (numQ - 1 + kEff - 1) = aw)
    (huHi : arrayWord mem aw u (numQ - 1 + kEff) = uHi)
    (huLo : arrayWord mem aw u (numQ - 1 + kEff - 1) = uLo)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (shift :: ret :: rem :: UInt256.ofNat numQ :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat (numQ - 1) :: vTop ::
        UInt256.ofNat numQ :: uLo :: u :: shift :: ret :: rem ::
        UInt256.ofNat (numQ - 1) :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 114) (C + 410) := by
  have hloop : (UInt256.ofNat numQ).isZero = ⟨0⟩ := by
    apply isZero_eq_zero_of_ne
    intro heq
    have hzero := congrArg UInt256.toNat heq
    rw [UInt256.toNat_ofNat_of_lt hnumQWord] at hzero
    simp at hzero
    omega
  have rd5458 := GeneratedTraces.trace_5450_notTaken
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloop
  have rd5516 := outerOperandsBodyExact hnumQPos hnumQWord hkEffPos hsumWord
    huCountWord hhiIndex hloIndex huHeader huHeaderAw huHiAw huLoAw huHi huLo
    hdepth rd5458
  exact rd5516.withIndices (by omega) (by omega)

/-- Continue a nonterminal quotient loop from the guard emitted after storing digit `cursor`.
The deployed `JUMPI` falls through directly to the common body at PC 5458. -/
theorem outerOperandsContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cursor kEff uCount : Nat} {tail : List UInt256}
    {shift ret rem v quotient u vTop uHi uLo : UInt256}
    (hcursorPos : 0 < cursor)
    (hcursorWord : cursor < UInt256.size)
    (hkEffPos : 0 < kEff)
    (hsumWord : cursor - 1 + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hhiIndex : cursor - 1 + kEff < uCount)
    (hloIndex : cursor - 1 + kEff - 1 < uCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huHiAw : arrayAfterWord aw u (cursor - 1 + kEff) = aw)
    (huLoAw : arrayAfterWord aw u (cursor - 1 + kEff - 1) = aw)
    (huHi : arrayWord mem aw u (cursor - 1 + kEff) = uHi)
    (huLo : arrayWord mem aw u (cursor - 1 + kEff - 1) = uLo)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat cursor).isZero :: UInt256.ofNat cursor :: shift ::
        ret :: rem :: UInt256.ofNat cursor :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat (cursor - 1) :: vTop ::
        UInt256.ofNat cursor :: uLo :: u :: shift :: ret :: rem ::
        UInt256.ofNat (cursor - 1) :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 109) (C + 397) := by
  have hcondition : (UInt256.ofNat cursor).isZero = ⟨0⟩ := by
    apply isZero_eq_zero_of_ne
    intro heq
    have hzero := congrArg UInt256.toNat heq
    rw [UInt256.toNat_ofNat_of_lt hcursorWord] at hzero
    simp at hzero
    omega
  have rd5458 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rd5516 := outerOperandsBodyExact hcursorPos hcursorWord hkEffPos hsumWord
    huCountWord hhiIndex hloIndex huHeader huHeaderAw huHiAw huLoAw huHi huLo
    hdepth rd5458
  exact rd5516.withIndices (by omega) (by omega)

/-- Take the ordinary 512-by-256 estimate path when `uHi < vTop`. -/
theorem enterDivEstimateExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient : UInt256}
    (hlt : uHi.toNat < vTop.toNat)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat jj :: vTop ::
        UInt256.ofNat numQ :: uLo :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5869⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 1) (C + 10) := by
  have hcondition : uHi.lt vTop = ⟨1⟩ := ult_one hlt
  have rd5876 := h.jumpiT (by native_decide) (by rw [hcondition]; native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  exact rd5876.withIndices (by omega) (by omega)

/-- Take the saturated q-hat estimate path when `uHi >= vTop`. -/
theorem enterSaturatedEstimateExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient : UInt256}
    (hge : vTop.toNat ≤ uHi.toNat)
    (hdepth : tail.length ≤ 1007)
    (h : RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat jj :: vTop ::
        UInt256.ofNat numQ :: uLo :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5517⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 1) (C + 10) := by
  have hcondition : uHi.lt vTop = ⟨0⟩ := ult_zero hge
  have rd5517 := h.jumpiNT (by native_decide) (by simpa [hcondition])
    (by simp only [List.length_cons]; omega)
  exact rd5517.withIndices (by omega) (by omega)

/-- Complete the saturated estimate path when `uLo + vTop` does not overflow.  The wrapped
addition's carry test proves `doRefinement`, and the normalized multi-limb case enters the same
second-limb setup as an ordinary 512-by-256 estimate. -/
theorem saturatedEstimateRefinementExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient : UInt256}
    (hsum : uLo.toNat + vTop.toNat < UInt256.size)
    (hkEffTwo : 2 ≤ kEff)
    (hkEffWord : kEff < UInt256.size)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5517⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u ::
        shift :: ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: (uLo + vTop) :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: (⟨0⟩ : UInt256).lnot :: u :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 29) (C + 97) := by
  have rd5536 := GeneratedTraces.trace_5517_body
    (by simp only [List.length_cons]; omega) h
  have haddNat : (uLo + vTop).toNat = uLo.toNat + vTop.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hsum]
  have hrHatGe : uLo.toNat ≤ (uLo + vTop).toNat := by rw [haddNat]; omega
  have hdoRefinement : ((uLo + vTop).lt uLo).isZero = ⟨1⟩ := by
    rw [ult_zero hrHatGe]
    native_decide
  have rd5858 := rd5536.jumpiT (by native_decide)
    (by rw [hdoRefinement]; native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5541 := GeneratedTraces.trace_5858_body
    (by simp only [List.length_cons]; omega) rd5858
  have hkEffGe : (⟨2⟩ : UInt256).toNat ≤ (UInt256.ofNat kEff).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hkEffWord]
    norm_num
    exact hkEffTwo
  have hkEffCondition : ((UInt256.ofNat kEff).lt ⟨2⟩).isZero = ⟨1⟩ := by
    rw [ult_zero hkEffGe]
    native_decide
  have rd5799 := rd5541.jumpiT (by native_decide)
    (by rw [hkEffCondition]; native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact rd5799.withIndices (by omega) (by omega)

/-- When the saturated `rHat` addition wraps, Algorithm D's carry test disables refinement and
the generated code enters multiply-subtract with the saturated q-hat unchanged. -/
theorem saturatedEstimateWrappedExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient : UInt256}
    (hwrap : UInt256.size ≤ uLo.toNat + vTop.toNat)
    (hdepth : tail.length ≤ 1002)
    (h : RDx runtimeBytecode ee g s0 ⟨5517⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u ::
        shift :: ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: (⟨0⟩ : UInt256).lnot ::
        shift :: ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 40) (C + 115) := by
  have hcarry : (uLo + vTop).lt uLo = ⟨1⟩ := by
    have hsumLt : uLo.toNat + vTop.toNat < 2 * UInt256.size := by
      have hu : uLo.toNat < UInt256.size := uLo.val.isLt
      have hv : vTop.toNat < UInt256.size := vTop.val.isLt
      omega
    have hmod : (uLo.toNat + vTop.toNat) % UInt256.size =
        uLo.toNat + vTop.toNat - UInt256.size := by
      rw [Nat.mod_eq_sub_mod hwrap]
      rw [Nat.mod_eq_of_lt (by omega)]
    apply ult_one
    rw [uadd_toNat, hmod]
    have hv : vTop.toNat < UInt256.size := vTop.val.isLt
    omega
  have hdoRefinement : ((uLo + vTop).lt uLo).isZero = ⟨0⟩ := by
    rw [hcarry]
    native_decide
  have rd5536 := GeneratedTraces.trace_5517_body
    (by simp only [List.length_cons]; omega) h
  have rd5537 := rd5536.jumpiNT (by native_decide)
    (by rw [hdoRefinement])
    (by simp only [List.length_cons]; omega)
  have rd5541 := GeneratedTraces.trace_5537_body
    (by simp only [List.length_cons]; omega) rd5537
  have rd5542 := rd5541.jumpiNT (by native_decide)
    (by rw [hdoRefinement])
    (by simp only [List.length_cons]; omega)
  have rd5563 := GeneratedTraces.trace_5542_body
    (by simp only [List.length_cons]; omega) rd5542
  exact rd5563.withIndices (by omega) (by omega)

/-- Call the nonzero-high-word 512-by-256 helper and return the exact q-hat estimate. -/
theorem divEstimateNonzeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient : UInt256}
    (hhi : uHi ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 999)
    (h : RDx runtimeBytecode ee g s0 ⟨5869⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5882⟩
      (MultiLimbDiv512.nonzeroRemainder uHi uLo vTop ::
        MultiLimbDiv512.nonzeroQuotient uHi uLo vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: vTop :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 120) (C + 422) := by
  have rd7905 := evm_run h with [
    jumpdest,
    swap2,
    dup1,
    swap5,
    pushCanonical 2 .PUSH2 ⟨5882⟩ (by decide),
    swap3,
    swap4,
    pushCanonical 2 .PUSH2 ⟨7898⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5889 := MultiLimbDiv512.nonzeroHighExact
    (by simp only [List.length_cons]; omega) hhi (by native_decide) rd7905
  have normalized := rd5889.withIndices
    (k' := k + 120) (C' := C + 422) (by omega) (by omega)
  simpa using normalized

/-- Call the zero-high-word 512-by-256 helper and return the exact q-hat estimate. -/
theorem divEstimateZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {vTop uLo u shift ret rem v quotient : UInt256}
    (hdepth : tail.length ≤ 999)
    (h : RDx runtimeBytecode ee g s0 ⟨5869⟩
      (⟨0⟩ :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u ::
        shift :: ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5882⟩
      (UInt256.mod uLo vTop :: UInt256.div uLo vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: vTop :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 43) (C + 147) := by
  have rd7905 := evm_run h with [
    jumpdest,
    swap2,
    dup1,
    swap5,
    pushCanonical 2 .PUSH2 ⟨5882⟩ (by decide),
    swap3,
    swap4,
    pushCanonical 2 .PUSH2 ⟨7898⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5889 := MultiLimbDiv512.zeroHighExact
    (by simp only [List.length_cons]; omega) (by native_decide) rd7905
  have normalized := rd5889.withIndices
    (k' := k + 43) (C' := C + 147) (by omega) (by omega)
  simpa using normalized

/-- Dispatch a completed ordinary q-hat estimate to the second-limb refinement setup. -/
theorem enterRefinementFromDivExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {rHat qHat vTop u shift ret rem v quotient : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hkEffTwo : 2 ≤ kEff)
    (hdepth : tail.length ≤ 1003)
    (h : RDx runtimeBytecode ee g s0 ⟨5882⟩
      (rHat :: qHat :: UInt256.ofNat jj :: UInt256.ofNat numQ :: vTop :: u ::
        shift :: ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: rHat :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: qHat :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 24) (C + 87) := by
  have hkEffGe : (UInt256.ofNat kEff).toNat ≥ (⟨2⟩ : UInt256).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hkEffWord]
    norm_num
    exact hkEffTwo
  have hlt : (UInt256.ofNat kEff).lt ⟨2⟩ = ⟨0⟩ := ult_zero hkEffGe
  have hcondition : ((UInt256.ofNat kEff).lt ⟨2⟩).isZero = ⟨1⟩ := by
    rw [hlt]
    native_decide
  have rd5548 := GeneratedTraces.trace_5882_body
    (by simp only [List.length_cons]; omega) h
  have rd5799 := rd5548.jumpiT (by native_decide)
    (by rw [hcondition]; native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have normalized := rd5799.withIndices
    (k' := k + 24) (C' := C + 87) (by omega) (by omega)
  simpa using normalized

/-- Load the second divisor and dividend limbs and enter the existing generated q-hat loop. -/
theorem refinementSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {rHat qHat vTop u shift ret rem v quotient vSecond uSecond : UInt256}
    (hkEffTwo : 2 ≤ kEff)
    (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: rHat :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: qHat :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8511⟩
      (⟨8519⟩ ::
        MultiLimbDivisionTrace.qhatNeedsRefinement qHat rHat vSecond uSecond ::
        vTop :: vSecond :: uSecond :: rHat :: qHat :: ⟨5846⟩ ::
        UInt256.ofNat numQ :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 135) (C + 475) := by
  let vIndex := kEff - 2
  let uSum := jj + kEff
  let uIndex := uSum - 2
  have hvIndexWord : vIndex < UInt256.size := by simp only [vIndex]; omega
  have huIndexWord : uIndex < UInt256.size := by simp only [uIndex, uSum]; omega
  have hvIndexBound : vIndex < kEff := by simp only [vIndex]; omega
  have hvGuard := arrayGuardExact mem aw v vIndex kEff hvIndexBound
    hvIndexWord hkEffWord hvHeader
  have hvGuardRaw :
      ((UInt256.ofNat vIndex).lt
        (if v.toNat ≥ mem.size ∨ v ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding v.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hvGuard
  have hvHeaderAw' : MultiLimbOddCompare.afterHeader aw v = aw := hvHeaderAw
  have hvSecondRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat vIndex).shiftLeft ⟨5⟩ + v + ⟨32⟩) = vSecond := by
    simpa only [vIndex, arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvSecond
  have hvSecondAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat vIndex).shiftLeft ⟨5⟩ + v + ⟨32⟩) = aw := by
    simpa only [vIndex, arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        hvSecondAw
  have rd1101a := GeneratedTraces.trace_5792_body
    (by simp only [List.length_cons]; omega) h
  have rd5828a := checkedSubTwoContinueExact (x := kEff) (ret := 5821)
    hkEffTwo hkEffWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1101a
  have rd1538a := GeneratedTraces.trace_5821_body
    (by simp only [List.length_cons]; omega) rd5828a
  have rd1539a := rd1538a.jumpiNT (by native_decide) hvGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, hvHeaderAw'] at rd1539a
  have rd5834 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1432 := GeneratedTraces.trace_5827_body
    (by simp only [List.length_cons]; omega) rd5834
  rw [← MultiLimbOddCompare.headerWord_generated, hvSecondRaw,
    ← MultiLimbOddCompare.afterHeader_generated, hvSecondAwRaw] at rd1432
  have rd5841 := checkedAddContinueExact (x := jj) (y := kEff) (ret := 5834)
    (by simpa only [uSum] using hindexWord) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1432
  have rd1101b := GeneratedTraces.trace_5834_body
    (by simp only [List.length_cons]; omega) rd5841
  have rd5828b := checkedSubTwoContinueExact (x := uSum) (ret := 5821)
    (by simp only [uSum]; omega) (by simpa only [uSum] using hindexWord)
    (by native_decide) (by simp only [List.length_cons]; omega) rd1101b
  have huGuard := arrayGuardExact mem aw u uIndex uCount
    (by simpa only [uIndex, uSum] using huIndex) huIndexWord huCountWord huHeader
  have huGuardRaw :
      ((UInt256.ofNat uIndex).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact huGuard
  have huHeaderAw' : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have huSecondRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat uIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = uSecond := by
    simpa only [uIndex, uSum, arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using huSecond
  have huSecondAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat uIndex).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [uIndex, uSum, arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        huSecondAw
  have rd1538b := GeneratedTraces.trace_5821_body
    (by simp only [List.length_cons]; omega) rd5828b
  have rd1539b := rd1538b.jumpiNT (by native_decide) huGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539b
  have rd5846 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd8482 := evm_run rd5846 with [
    jumpdest,
    mloadCanonical,
    swap4,
    pushCanonical 2 .PUSH2 ⟨8475⟩ (by decide),
    jump (by native_decide)
  ]
  rw [← MultiLimbOddCompare.headerWord_generated, huSecondRaw,
    ← MultiLimbOddCompare.afterHeader_generated, huSecondAwRaw] at rd8482
  have rd8518 := MultiLimbDivisionTrace.qhatCompareBody
    (by simp only [List.length_cons]; omega) rd8482
  have normalized := rd8518.withIndices
    (k' := k + 135) (C' := C + 475) (by omega) (by omega)
  simpa only [vIndex, uSum, uIndex] using normalized

/-- Execute an arbitrary valid q-hat refinement path and return to the quotient iteration. -/
theorem qhatPathReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {vTop vSecond uSecond shift ret rem v quotient u : UInt256}
    (state : MultiLimbDivisionTrace.QhatState)
    (path : MultiLimbDivisionTrace.QhatRefinementPath
      vTop vSecond uSecond state states)
    (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd state states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd state states).rHat
      vSecond uSecond = ⟨0⟩)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (MultiLimbDivisionTrace.qhatLoopStack state vTop vSecond uSecond
        (⟨5846⟩ :: UInt256.ofNat numQ :: shift :: ret :: rem ::
          UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
          normalizationMarker :: tail)) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5846⟩
      ((MultiLimbDivisionTrace.qhatPathEnd state states).qHat ::
        UInt256.ofNat numQ :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 8)
        (C + 185 * states.length + 30) := by
  have rd8525 := MultiLimbDivisionTrace.qhatRefinementPathExit state
    (by simp only [List.length_cons]; omega) path hdone h
  have rd5853 := evm_run rd8525 with [jump (by native_decide)]
  have normalized := rd5853.withIndices
    (k' := k + 55 * states.length + 8)
    (C' := C + 185 * states.length + 30) (by omega) (by omega)
  simpa using normalized

/-- Execute the source-level q-hat overflow break and return the decremented estimate to the
quotient iteration.  This is distinct from normal false-condition loop termination. -/
theorem qhatOverflowReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {vTop vSecond uSecond shift ret rem v quotient u : UInt256}
    (state : MultiLimbDivisionTrace.QhatState)
    (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
      state.qHat state.rHat vSecond uSecond ≠ ⟨0⟩)
    (hoverflow :
      (MultiLimbDivisionTrace.qhatAdvance vTop state).rHat.lt vTop ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (MultiLimbDivisionTrace.qhatLoopStack state vTop vSecond uSecond
        (⟨5846⟩ :: UInt256.ofNat numQ :: shift :: ret :: rem ::
          UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
          normalizationMarker :: tail)) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5846⟩
      ((MultiLimbDivisionTrace.qhatAdvance vTop state).qHat ::
        UInt256.ofNat numQ :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 28) (C + 97) := by
  have rd8525 := MultiLimbDivisionTrace.qhatRefinementOverflowExit state
    (by simp only [List.length_cons]; omega) hrefine hoverflow h
  have rd5846 := evm_run rd8525 with [jump (by native_decide)]
  exact rd5846.withIndices (by omega) (by omega)

/-- Execute any non-overflowing refinement prefix followed by the source-level overflow break. -/
theorem qhatPathOverflowReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {vTop vSecond uSecond shift ret rem v quotient u : UInt256}
    (state : MultiLimbDivisionTrace.QhatState)
    (path : MultiLimbDivisionTrace.QhatRefinementPath
      vTop vSecond uSecond state states)
    (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd state states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd state states).rHat vSecond uSecond ≠ ⟨0⟩)
    (hoverflow :
      (MultiLimbDivisionTrace.qhatAdvance vTop
        (MultiLimbDivisionTrace.qhatPathEnd state states)).rHat.lt vTop ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (MultiLimbDivisionTrace.qhatLoopStack state vTop vSecond uSecond
        (⟨5846⟩ :: UInt256.ofNat numQ :: shift :: ret :: rem ::
          UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
          normalizationMarker :: tail)) mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatPathEnd state states
    RDx runtimeBytecode ee g s0 ⟨5846⟩
      ((MultiLimbDivisionTrace.qhatAdvance vTop final).qHat ::
        UInt256.ofNat numQ :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 28)
        (C + 185 * states.length + 97) := by
  have rdEnd := MultiLimbDivisionTrace.qhatRefinementIterations state
    (by simp only [List.length_cons]; omega) path h
  have rd5846 := qhatOverflowReturnExact
    (MultiLimbDivisionTrace.qhatPathEnd state states) hrefine hoverflow
    (by omega) rdEnd
  exact rd5846.withIndices (by omega) (by omega)

/-- Initialize the generated multiply-subtract loop.  The frame preserves `numQ`, while the
branch condition is computed from the farther saved `kEff` word. -/
theorem multiplySubtractSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C numQ jj kEff : Nat} {tail : List UInt256}
    {qHat shift ret rem v quotient u vTop : UInt256}
    (hdepth : tail.length ≤ 1005)
    (h : RDx runtimeBytecode ee g s0 ⟨5846⟩
      (qHat :: UInt256.ofNat numQ :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 29) (C + 76) := by
  have rd5570 := GeneratedTraces.trace_5846_body
    (by simp only [List.length_cons]; omega) h
  have normalized := rd5570.withIndices
    (k' := k + 29) (C' := C + 76) (by omega) (by omega)
  simpa using normalized

def multiplySubtractVAddress (v i : UInt256) : UInt256 :=
  MultiLimbOddCompare.elementPtr v i

def multiplySubtractUAddress (u current i : UInt256) : UInt256 :=
  (current + i + (⟨0⟩ : UInt256).lnot).shiftLeft ⟨5⟩ + u + ⟨32⟩

def multiplySubtractVi
    (mem : ByteArray) (aw v i : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWord mem aw (multiplySubtractVAddress v i)

def multiplySubtractAw1 (aw v i : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 aw (multiplySubtractVAddress v i)

def multiplySubtractUVal
    (mem : ByteArray) (aw v i u current : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWord mem (multiplySubtractAw1 aw v i)
    (multiplySubtractUAddress u current i)

def multiplySubtractAw2 (aw v i u current : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 (multiplySubtractAw1 aw v i)
    (multiplySubtractUAddress u current i)

structure MultiplySubtractResult where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256
  borrow : UInt256

def multiplySubtractStep
    (mem : ByteArray) (aw v i u current qHat carry borrow : UInt256) :
    MultiplySubtractResult :=
  let vi := multiplySubtractVi mem aw v i
  let pLo := qHat * vi
  let pMM := UInt256.mulMod qHat vi (⟨0⟩ : UInt256).lnot
  let withCarry := pLo + carry
  let nextCarry := (pMM - pLo - pMM.lt pLo) + withCarry.lt pLo
  let uVal := multiplySubtractUVal mem aw v i u current
  let subtraction := evmSubBorrow uVal withCarry borrow
  let address := multiplySubtractUAddress u current i
  let aw2 := multiplySubtractAw2 aw v i u current
  {
    memory := subtraction.1.toByteArray.write 0 mem address.toNat 32
    activeWords := MultiLimbDivisionTrace.readWords1 aw2 address
    carry := nextCarry
    borrow := subtraction.2
  }

def multiplySubtractGas (aw v i u current : UInt256) : Nat :=
  let aw1 := multiplySubtractAw1 aw v i
  let aw2 := multiplySubtractAw2 aw v i u current
  let aw3 := MultiLimbDivisionTrace.readWords1 aw2
    (multiplySubtractUAddress u current i)
  237 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

/-- One exact limb of `u -= qHat * v`, including high-product recovery, carry, borrow,
the in-place write, and the next `i < kEff` guard. -/
theorem multiplySubtractCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {v i u carry borrow numQ qHat shift ret rem jj kEff quotient vTop : UInt256}
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5715⟩
      (v :: i :: u :: borrow :: carry :: numQ :: qHat :: shift :: ret :: rem ::
        jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let result := multiplySubtractStep mem aw v i u numQ qHat carry borrow
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (i + ⟨1⟩).lt kEff :: v :: (i + ⟨1⟩) :: u ::
        result.borrow :: result.carry :: numQ :: qHat :: shift :: ret :: rem :: jj ::
        kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + 77)
        (C + multiplySubtractGas aw v i u numQ) := by
  let vAddress := multiplySubtractVAddress v i
  let aw1 := multiplySubtractAw1 aw v i
  let vi := multiplySubtractVi mem aw v i
  let pLo := qHat * vi
  let pMM := UInt256.mulMod qHat vi (⟨0⟩ : UInt256).lnot
  let withCarry := pLo + carry
  let nextCarry := (pMM - pLo - pMM.lt pLo) + withCarry.lt pLo
  let uAddress := multiplySubtractUAddress u numQ i
  let aw2 := multiplySubtractAw2 aw v i u numQ
  let uVal := multiplySubtractUVal mem aw v i u numQ
  let subtraction := evmSubBorrow uVal withCarry borrow
  let nextMemory := subtraction.1.toByteArray.write 0 mem uAddress.toNat 32
  let aw3 := MultiLimbDivisionTrace.readWords1 aw2 uAddress
  have rd5739 := evm_run h with [
    jumpdest, swap3, pushCanonical 1 .PUSH1 ⟨32⟩ (by decide), dup1,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide), swap5, swap7, swap6, dup5,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide), shl, add, add, mloadCanonical
  ]
  have rd5739N := rd5739
  change RDx runtimeBytecode ee g s0 ⟨5732⟩
    (vi :: ⟨32⟩ :: borrow :: i :: ⟨1⟩ :: carry :: u :: numQ :: qHat ::
      shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
    mem aw1 rdata acc _ _ at rd5739N
  have rd5751 := evm_run rd5739N with [
    push0, not, dup2, dup11, mul, swap2, dup11, mulmod, swap6, dup2, add, swap6
  ]
  have rd5751N := rd5751
  change RDx runtimeBytecode ee g s0 ⟨5744⟩
    (pMM :: pLo :: ⟨32⟩ :: borrow :: i :: ⟨1⟩ :: withCarry :: u :: numQ ::
      qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u :: vTop ::
      normalizationMarker :: tail) mem aw1 rdata acc _ _ at rd5751N
  have rd5763 := evm_run rd5751N with [
    dup2, dup8, lt, swap2, dup1, dup3, lt, swap2, sub, sub, add, swap6
  ]
  have rd5763N := rd5763
  change RDx runtimeBytecode ee g s0 ⟨5756⟩
    (u :: ⟨32⟩ :: borrow :: i :: ⟨1⟩ :: withCarry :: nextCarry :: numQ ::
      qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u :: vTop ::
      normalizationMarker :: tail) mem aw1 rdata acc _ _ at rd5763N
  have rd5777 := evm_run rd5763N with [
    push0, not, dup5, dup10, add, add,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide), shl, add, add, swap4, dup5,
    mloadCanonical
  ]
  have rd5777N := rd5777
  change RDx runtimeBytecode ee g s0 ⟨5770⟩
    (uVal :: withCarry :: borrow :: i :: ⟨1⟩ :: uAddress :: nextCarry ::
      numQ :: qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u ::
      vTop :: normalizationMarker :: tail) mem aw2 rdata acc _ _ at rd5777N
  have rd5792 := evm_run rd5777N with [
    swap1, dup1, dup3, sub, swap3, dup1, dup5, sub, swap4, lt, swap2, lt, or,
    swap4, mstoreCanonical
  ]
  have rd5792N := rd5792
  change RDx runtimeBytecode ee g s0 ⟨5785⟩
    (i :: ⟨1⟩ :: subtraction.2 :: nextCarry :: numQ :: qHat :: shift :: ret ::
      rem :: jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
    nextMemory aw3 rdata acc _ _ at rd5792N
  have rd5562 := evm_run rd5792N with [
    add, dup13, swap1, pushCanonical 2 .PUSH2 ⟨5555⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5570 := evm_run rd5562 with [
    jumpdest, dup12Canonical, dup12Canonical, dup3, lt,
    pushCanonical 2 .PUSH2 ⟨5715⟩ (by decide)
  ]
  change RDx runtimeBytecode ee g s0 ⟨5563⟩
    (⟨5715⟩ :: (i + ⟨1⟩).lt kEff :: v :: (i + ⟨1⟩) :: u ::
      subtraction.2 :: nextCarry :: numQ :: qHat :: shift :: ret :: rem :: jj ::
      kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
    nextMemory aw3 rdata acc _ _ at rd5570
  have normalized := rd5570.withIndices
    (k' := k + 77) (C' := C + multiplySubtractGas aw v i u numQ)
    (by omega) (by
      simp [multiplySubtractGas, aw1, aw2, aw3, uAddress,
        multiplySubtractAw1, multiplySubtractAw2,
        multiplySubtractVAddress, multiplySubtractUAddress,
        MultiLimbOddCompare.elementPtr,
        MultiLimbDivisionTrace.readWords1]
      omega)
  simpa only [multiplySubtractStep, vi, withCarry, nextCarry, uVal,
    subtraction, nextMemory, aw1, aw2, aw3, uAddress] using normalized

structure MultiplySubtractState where
  index : UInt256
  carry : UInt256
  borrow : UInt256
  memory : ByteArray
  activeWords : UInt256

def multiplySubtractAdvance
    (v u current qHat : UInt256) (state : MultiplySubtractState) :
    MultiplySubtractState :=
  let result := multiplySubtractStep state.memory state.activeWords v state.index u
    current qHat state.carry state.borrow
  {
    index := state.index + ⟨1⟩
    carry := result.carry
    borrow := result.borrow
    memory := result.memory
    activeWords := result.activeWords
  }

def multiplySubtractIterate
    (v u current qHat : UInt256) : Nat → MultiplySubtractState → MultiplySubtractState
  | 0, state => state
  | count + 1, state =>
      multiplySubtractIterate v u current qHat count
        (multiplySubtractAdvance v u current qHat state)

def multiplySubtractLoopGas
    (v u current qHat : UInt256) : Nat → MultiplySubtractState → Nat
  | 0, _ => 0
  | count + 1, state =>
      10 + multiplySubtractGas state.activeWords v state.index u current +
        multiplySubtractLoopGas v u current qHat count
          (multiplySubtractAdvance v u current qHat state)

def ValidMultiplySubtractPath
    (v u current qHat kEff : UInt256) : Nat → MultiplySubtractState → Prop
  | 0, _ => True
  | count + 1, state =>
      state.index.lt kEff ≠ ⟨0⟩ ∧
        ValidMultiplySubtractPath v u current qHat kEff count
          (multiplySubtractAdvance v u current qHat state)

/-- Compose an arbitrary exact path through the generated multiply-subtract loop. -/
theorem multiplySubtractIterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {v u current qHat shift ret rem jj kEff quotient vTop : UInt256}
    (state : MultiplySubtractState)
    (hvalid : ValidMultiplySubtractPath v u current qHat kEff count state)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: state.index.lt kEff :: v :: state.index :: u :: state.borrow ::
        state.carry :: current :: qHat :: shift :: ret :: rem :: jj :: kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := multiplySubtractIterate v u current qHat count state
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: final.index.lt kEff :: v :: final.index :: u :: final.borrow ::
        final.carry :: current :: qHat :: shift :: ret :: rem :: jj :: kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      final.memory final.activeWords rdata acc (k + 78 * count)
        (C + multiplySubtractLoopGas v u current qHat count state) := by
  induction count generalizing state k C with
  | zero => simpa [multiplySubtractIterate, multiplySubtractLoopGas]
  | succ count ih =>
      have hcondition := hvalid.1
      have rd5722 := h.jumpiT (by native_decide) hcondition
        (by native_decide) (by simp only [List.length_cons]; omega)
      have rdNext := multiplySubtractCycleExact
        (by omega) rd5722
      have rdFinal := ih (state := multiplySubtractAdvance v u current qHat state)
        hvalid.2 rdNext
      have normalized := rdFinal.withIndices
        (k' := k + 78 * (count + 1))
        (C' := C + multiplySubtractLoopGas v u current qHat (count + 1) state)
        (by omega) (by simp [multiplySubtractLoopGas]; omega)
      simpa only [multiplySubtractIterate] using normalized

theorem multiplySubtractAdvance_index
    (v u current qHat : UInt256) (state : MultiplySubtractState) :
    (multiplySubtractAdvance v u current qHat state).index = state.index + ⟨1⟩ := by
  rfl

private theorem ofNat_succ_word {n : Nat} (h : n + 1 < UInt256.size) :
    UInt256.ofNat n + ⟨1⟩ = UInt256.ofNat (n + 1) := by
  have hn : n < UInt256.size := by omega
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hn,
    show (⟨1⟩ : UInt256).toNat = 1 by decide,
    UInt256.toNat_ofNat_of_lt h, Nat.mod_eq_of_lt h]

theorem validMultiplySubtractPathOfNat
    (v u current qHat : UInt256) {start count kEff : Nat}
    (state : MultiplySubtractState)
    (hindex : state.index = UInt256.ofNat start)
    (hrange : start + count ≤ kEff)
    (hkEffWord : kEff < UInt256.size) :
    ValidMultiplySubtractPath v u current qHat (UInt256.ofNat kEff) count state := by
  induction count generalizing start state with
  | zero => simp [ValidMultiplySubtractPath]
  | succ count ih =>
      have hstart : start < kEff := by omega
      have hstartWord : start < UInt256.size := lt_trans hstart hkEffWord
      have hcondition : state.index.lt (UInt256.ofNat kEff) = ⟨1⟩ := by
        rw [hindex]
        apply ult_one
        rw [UInt256.toNat_ofNat_of_lt hstartWord,
          UInt256.toNat_ofNat_of_lt hkEffWord]
        exact hstart
      have hnextIndex :
          (multiplySubtractAdvance v u current qHat state).index =
            UInt256.ofNat (start + 1) := by
        rw [multiplySubtractAdvance_index, hindex]
        exact ofNat_succ_word (by omega)
      constructor
      · rw [hcondition]
        native_decide
      · exact ih (start := start + 1)
          (multiplySubtractAdvance v u current qHat state) hnextIndex (by omega)

theorem multiplySubtractIterate_index_ofNat
    (v u current qHat : UInt256) {start count : Nat}
    (state : MultiplySubtractState)
    (hindex : state.index = UInt256.ofNat start)
    (hbound : start + count < UInt256.size) :
    (multiplySubtractIterate v u current qHat count state).index =
      UInt256.ofNat (start + count) := by
  induction count generalizing start state with
  | zero => simpa [multiplySubtractIterate] using hindex
  | succ count ih =>
      rw [multiplySubtractIterate]
      have hnextIndex :
          (multiplySubtractAdvance v u current qHat state).index =
            UInt256.ofNat (start + 1) := by
        rw [multiplySubtractAdvance_index, hindex]
        exact ofNat_succ_word (by omega)
      have hrest := ih (start := start + 1)
        (multiplySubtractAdvance v u current qHat state) hnextIndex (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Execute all `kEff` multiply-subtract limbs from zero carry and borrow and take the normal
loop exit. -/
theorem multiplySubtractAllExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff : Nat} {tail : List UInt256}
    {v u current qHat shift ret rem jj quotient vTop : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: current :: qHat :: shift :: ret :: rem :: jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let initial : MultiplySubtractState := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, mem, aw⟩
    let final := multiplySubtractIterate v u current qHat kEff initial
    RDx runtimeBytecode ee g s0 ⟨5564⟩
      (v :: UInt256.ofNat kEff :: u :: final.borrow :: final.carry :: current ::
        qHat :: shift :: ret :: rem :: jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      final.memory final.activeWords rdata acc (k + 78 * kEff + 1)
        (C + multiplySubtractLoopGas v u current qHat kEff initial + 10) := by
  let initial : MultiplySubtractState := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, mem, aw⟩
  have hvalid : ValidMultiplySubtractPath v u current qHat (UInt256.ofNat kEff)
      kEff initial := validMultiplySubtractPathOfNat v u current qHat initial
        (start := 0) (count := kEff) (kEff := kEff) (by rfl) (by omega) hkEffWord
  have rdFinal := multiplySubtractIterationsExact initial hvalid hdepth h
  let final := multiplySubtractIterate v u current qHat kEff initial
  have hfinalIndex : final.index = UInt256.ofNat kEff := by
    dsimp only [final]
    simpa using (multiplySubtractIterate_index_ofNat v u current qHat initial
      (start := 0) (count := kEff) (by rfl) (by simpa using hkEffWord))
  change RDx runtimeBytecode ee g s0 ⟨5563⟩
    (⟨5715⟩ :: final.index.lt (UInt256.ofNat kEff) :: v :: final.index :: u ::
      final.borrow :: final.carry :: current :: qHat :: shift :: ret :: rem :: jj ::
      UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
    final.memory final.activeWords rdata acc (k + 78 * kEff)
      (C + multiplySubtractLoopGas v u current qHat kEff initial) at rdFinal
  rw [hfinalIndex] at rdFinal
  have hcondition : (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    omega
  have rd5571 := rdFinal.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have normalized := rd5571.withIndices
    (k' := k + 78 * kEff + 1)
    (C' := C + multiplySubtractLoopGas v u current qHat kEff initial + 10)
    (by omega) (by omega)
  simpa only [initial, final] using normalized

structure TopSubtractResult where
  address : UInt256
  memory : ByteArray
  activeWords : UInt256
  negative : UInt256

def topSubtractAw1 (aw u current kEff : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 aw
    (multiplySubtractUAddress u current kEff)

def topSubtractAw2 (aw u current kEff : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 (topSubtractAw1 aw u current kEff)
    (multiplySubtractUAddress u current kEff)

def topSubtractStep
    (mem : ByteArray) (aw u current kEff carry borrow : UInt256) :
    TopSubtractResult :=
  let address := multiplySubtractUAddress u current kEff
  let uTop := MultiLimbDivisionTrace.readWord mem aw address
  let subtraction := evmSubBorrow uTop carry borrow
  {
    address := address
    memory := subtraction.1.toByteArray.write 0 mem address.toNat 32
    activeWords := topSubtractAw2 aw u current kEff
    negative := subtraction.2
  }

def topSubtractGas (aw u current kEff : UInt256) : Nat :=
  let aw1 := topSubtractAw1 aw u current kEff
  let aw2 := topSubtractAw2 aw u current kEff
  92 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- Subtract the final carry and borrow from `u[jj + kEff]`, write the top limb,
and expose the exact Knuth add-back condition. -/
theorem topSubtractExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {v kEff u borrow carry current qHat shift ret rem jj quotient vTop : UInt256}
    (hdepth : tail.length ≤ 1005)
    (h : RDx runtimeBytecode ee g s0 ⟨5564⟩
      (v :: kEff :: u :: borrow :: carry :: current :: qHat :: shift :: ret ::
        rem :: jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let result := topSubtractStep mem aw u current kEff carry borrow
    RDx runtimeBytecode ee g s0 ⟨5600⟩
      (⟨5619⟩ :: result.negative :: result.address :: current :: qHat :: shift ::
        ret :: rem :: jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + 32)
        (C + topSubtractGas aw u current kEff) := by
  have rd5607 := GeneratedTraces.trace_5564_body
    (by simp only [List.length_cons]; omega) h
  have normalized := rd5607.withIndices
    (k' := k + 32) (C' := C + topSubtractGas aw u current kEff)
    (by omega) (by
      simp [topSubtractGas, topSubtractAw1, topSubtractAw2,
        MultiLimbDivisionTrace.readWords1, multiplySubtractUAddress,
        u256_add_comm, u256_add_assoc]
      omega)
  simpa [topSubtractStep, multiplySubtractUAddress, evmSubBorrow,
    topSubtractAw1, topSubtractAw2, MultiLimbDivisionTrace.readWord,
    MultiLimbDivisionTrace.readWords1, u256_add_comm, u256_add_assoc] using normalized

/-- Skip Knuth correction when the top subtraction is nonnegative. -/
theorem skipAddBackExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address current qHat shift ret rem jj kEff v quotient u vTop : UInt256}
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5600⟩
      (⟨5619⟩ :: ⟨0⟩ :: address :: current :: qHat :: shift :: ret :: rem :: jj ::
        kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5601⟩
      (address :: current :: qHat :: shift :: ret :: rem :: jj :: kEff :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 1) (C + 10) := by
  have rd5601 := h.jumpiNT (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact rd5601.withIndices (by omega) (by omega)

/-- Enter the correction path, perform Solidity's checked `qHat--`, and initialize the
add-back loop. -/
theorem enterAddBackExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {negative address current qHat shift ret rem jj kEff v quotient u vTop : UInt256}
    (hnegative : negative ≠ ⟨0⟩)
    (hqHat : qHat ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 1006)
    (h : RDx runtimeBytecode ee g s0 ⟨5600⟩
      (⟨5619⟩ :: negative :: address :: current :: qHat :: shift :: ret :: rem ::
        jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5644⟩
      (⟨5659⟩ :: (⟨0⟩ : UInt256).lt kEff :: u :: current :: ⟨0⟩ :: ⟨0⟩ ::
        address :: (qHat + (⟨0⟩ : UInt256).lnot) :: shift :: ret :: rem :: jj ::
        kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc (k + 30) (C + 103) := by
  have rd5626 := h.jumpiT (by native_decide) hnegative (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3148 := GeneratedTraces.trace_5619_body
    (by simp only [List.length_cons]; omega) rd5626
  have hqHatGuard : qHat.isZero = ⟨0⟩ := isZero_eq_zero_of_ne hqHat
  have rd3149 := rd3148.jumpiNT (by native_decide) hqHatGuard
    (by simp only [List.length_cons]; omega)
  have rd5637 := GeneratedTraces.trace_3149_jump
    (by simp only [List.length_cons]; omega) rd3149
    (by native_decide) (by native_decide)
  have rd5651 := GeneratedTraces.trace_5630_body
    (by simp only [List.length_cons]; omega) rd5637
  have normalized := rd5651.withIndices
    (k' := k + 30) (C' := C + 103) (by omega) (by omega)
  simpa [u256_add_comm] using normalized

def addBackVAddress (v i : UInt256) : UInt256 :=
  MultiLimbOddCompare.elementPtr v i

def addBackUAddress (u current i : UInt256) : UInt256 :=
  multiplySubtractUAddress u current i

def addBackAw1 (aw v i : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 aw (addBackVAddress v i)

def addBackAw2 (aw v i u current : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 (addBackAw1 aw v i)
    (addBackUAddress u current i)

def addBackAw3 (aw v i u current : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 (addBackAw2 aw v i u current)
    (addBackUAddress u current i)

structure AddBackResult where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256

def addBackStep
    (mem : ByteArray) (aw v i u current carry : UInt256) : AddBackResult :=
  let vValue := MultiLimbDivisionTrace.readWord mem aw (addBackVAddress v i)
  let uValue := MultiLimbDivisionTrace.readWord mem (addBackAw1 aw v i)
    (addBackUAddress u current i)
  let addition := evmAddCarryStep uValue vValue carry
  {
    memory := addition.1.toByteArray.write 0 mem
      (addBackUAddress u current i).toNat 32
    activeWords := addBackAw3 aw v i u current
    carry := addition.2
  }

def addBackGas (aw v i u current : UInt256) : Nat :=
  let aw1 := addBackAw1 aw v i
  let aw2 := addBackAw2 aw v i u current
  let aw3 := addBackAw3 aw v i u current
  165 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

/-- One exact correction limb `u[jj+i] += v[i] + carry`, including the next guard. -/
theorem addBackCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {u current i carry topAddress qHat shift ret rem jj kEff v quotient vTop : UInt256}
    (hdepth : tail.length ≤ 1003)
    (h : RDx runtimeBytecode ee g s0 ⟨5659⟩
      (u :: current :: i :: carry :: topAddress :: qHat :: shift :: ret :: rem ::
        jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let result := addBackStep mem aw v i u current carry
    RDx runtimeBytecode ee g s0 ⟨5644⟩
      (⟨5659⟩ :: (i + ⟨1⟩).lt kEff :: u :: current :: (i + ⟨1⟩) ::
        result.carry :: topAddress :: qHat :: shift :: ret :: rem :: jj :: kEff ::
        v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + 55)
        (C + addBackGas aw v i u current) := by
  have rd5651 := GeneratedTraces.trace_5659_body
    (by simp only [List.length_cons]; omega) h
  have normalized := rd5651.withIndices
    (k' := k + 55) (C' := C + addBackGas aw v i u current)
    (by omega) (by
      simp [addBackGas, addBackAw1, addBackAw2, addBackAw3,
        addBackVAddress, addBackUAddress, multiplySubtractUAddress,
        MultiLimbOddCompare.elementPtr, MultiLimbDivisionTrace.readWords1,
        u256_add_comm, u256_add_assoc]
      omega)
  simpa [addBackStep, evmAddCarryStep, addBackAw1, addBackAw2, addBackAw3,
    addBackVAddress, addBackUAddress, multiplySubtractUAddress,
    MultiLimbOddCompare.elementPtr, MultiLimbDivisionTrace.readWord,
    MultiLimbDivisionTrace.readWords1, u256_add_comm, u256_add_assoc,
    u256_lor_comm] using normalized

structure AddBackState where
  index : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def addBackAdvance (v u current : UInt256) (state : AddBackState) : AddBackState :=
  let result := addBackStep state.memory state.activeWords v state.index u current state.carry
  {
    index := state.index + ⟨1⟩
    carry := result.carry
    memory := result.memory
    activeWords := result.activeWords
  }

def addBackIterate (v u current : UInt256) : Nat → AddBackState → AddBackState
  | 0, state => state
  | count + 1, state =>
      addBackIterate v u current count (addBackAdvance v u current state)

def addBackLoopGas (v u current : UInt256) : Nat → AddBackState → Nat
  | 0, _ => 0
  | count + 1, state =>
      10 + addBackGas state.activeWords v state.index u current +
        addBackLoopGas v u current count (addBackAdvance v u current state)

def ValidAddBackPath
    (v u current kEff : UInt256) : Nat → AddBackState → Prop
  | 0, _ => True
  | count + 1, state =>
      state.index.lt kEff ≠ ⟨0⟩ ∧
        ValidAddBackPath v u current kEff count (addBackAdvance v u current state)

theorem addBackIterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {v u current kEff topAddress qHat shift ret rem jj quotient vTop : UInt256}
    (state : AddBackState)
    (hvalid : ValidAddBackPath v u current kEff count state)
    (hdepth : tail.length ≤ 1003)
    (h : RDx runtimeBytecode ee g s0 ⟨5644⟩
      (⟨5659⟩ :: state.index.lt kEff :: u :: current :: state.index :: state.carry ::
        topAddress :: qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := addBackIterate v u current count state
    RDx runtimeBytecode ee g s0 ⟨5644⟩
      (⟨5659⟩ :: final.index.lt kEff :: u :: current :: final.index :: final.carry ::
        topAddress :: qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail)
      final.memory final.activeWords rdata acc (k + 56 * count)
        (C + addBackLoopGas v u current count state) := by
  induction count generalizing state k C with
  | zero => simpa [addBackIterate, addBackLoopGas]
  | succ count ih =>
      have rd5666 := h.jumpiT (by native_decide) hvalid.1
        (by native_decide) (by simp only [List.length_cons]; omega)
      have rdNext := addBackCycleExact hdepth rd5666
      have rdFinal := ih (state := addBackAdvance v u current state)
        hvalid.2 rdNext
      have normalized := rdFinal.withIndices
        (k' := k + 56 * (count + 1))
        (C' := C + addBackLoopGas v u current (count + 1) state)
        (by omega) (by simp [addBackLoopGas]; omega)
      simpa only [addBackIterate] using normalized

theorem addBackAdvance_index (v u current : UInt256) (state : AddBackState) :
    (addBackAdvance v u current state).index = state.index + ⟨1⟩ := by
  rfl

theorem validAddBackPathOfNat
    (v u current : UInt256) {start count kEff : Nat}
    (state : AddBackState)
    (hindex : state.index = UInt256.ofNat start)
    (hrange : start + count ≤ kEff)
    (hkEffWord : kEff < UInt256.size) :
    ValidAddBackPath v u current (UInt256.ofNat kEff) count state := by
  induction count generalizing start state with
  | zero => simp [ValidAddBackPath]
  | succ count ih =>
      have hstart : start < kEff := by omega
      have hstartWord : start < UInt256.size := lt_trans hstart hkEffWord
      have hcondition : state.index.lt (UInt256.ofNat kEff) = ⟨1⟩ := by
        rw [hindex]
        apply ult_one
        rw [UInt256.toNat_ofNat_of_lt hstartWord,
          UInt256.toNat_ofNat_of_lt hkEffWord]
        exact hstart
      have hnextIndex :
          (addBackAdvance v u current state).index = UInt256.ofNat (start + 1) := by
        rw [addBackAdvance_index, hindex]
        exact ofNat_succ_word (by omega)
      constructor
      · rw [hcondition]
        native_decide
      · exact ih (start := start + 1) (addBackAdvance v u current state)
          hnextIndex (by omega)

theorem addBackIterate_index_ofNat
    (v u current : UInt256) {start count : Nat}
    (state : AddBackState)
    (hindex : state.index = UInt256.ofNat start)
    (hbound : start + count < UInt256.size) :
    (addBackIterate v u current count state).index =
      UInt256.ofNat (start + count) := by
  induction count generalizing start state with
  | zero => simpa [addBackIterate] using hindex
  | succ count ih =>
      rw [addBackIterate]
      have hnextIndex :
          (addBackAdvance v u current state).index = UInt256.ofNat (start + 1) := by
        rw [addBackAdvance_index, hindex]
        exact ofNat_succ_word (by omega)
      have hrest := ih (start := start + 1) (addBackAdvance v u current state)
        hnextIndex (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

theorem addBackAllExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff : Nat} {tail : List UInt256}
    {v u current topAddress qHat shift ret rem jj quotient vTop : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hdepth : tail.length ≤ 1003)
    (h : RDx runtimeBytecode ee g s0 ⟨5644⟩
      (⟨5659⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: u :: current :: ⟨0⟩ ::
        ⟨0⟩ :: topAddress :: qHat :: shift :: ret :: rem :: jj :: UInt256.ofNat kEff ::
        v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let initial : AddBackState := ⟨⟨0⟩, ⟨0⟩, mem, aw⟩
    let final := addBackIterate v u current kEff initial
    RDx runtimeBytecode ee g s0 ⟨5645⟩
      (u :: current :: UInt256.ofNat kEff :: final.carry :: topAddress :: qHat :: shift ::
        ret :: rem :: jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      final.memory final.activeWords rdata acc (k + 56 * kEff + 1)
        (C + addBackLoopGas v u current kEff initial + 10) := by
  let initial : AddBackState := ⟨⟨0⟩, ⟨0⟩, mem, aw⟩
  have hvalid := validAddBackPathOfNat v u current initial
    (start := 0) (count := kEff) (kEff := kEff) (by rfl) (by omega) hkEffWord
  have rdFinal := addBackIterationsExact initial hvalid hdepth h
  let final := addBackIterate v u current kEff initial
  have hfinalIndex : final.index = UInt256.ofNat kEff := by
    dsimp only [final]
    simpa using (addBackIterate_index_ofNat v u current initial
      (start := 0) (count := kEff) (by rfl) (by simpa using hkEffWord))
  change RDx runtimeBytecode ee g s0 ⟨5644⟩
    (⟨5659⟩ :: final.index.lt (UInt256.ofNat kEff) :: u :: current :: final.index ::
      final.carry :: topAddress :: qHat :: shift :: ret :: rem :: jj ::
      UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
    final.memory final.activeWords rdata acc (k + 56 * kEff)
      (C + addBackLoopGas v u current kEff initial) at rdFinal
  rw [hfinalIndex] at rdFinal
  have hcondition : (UInt256.ofNat kEff).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    omega
  have rd5652 := rdFinal.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have normalized := rd5652.withIndices
    (k' := k + 56 * kEff + 1)
    (C' := C + addBackLoopGas v u current kEff initial + 10)
    (by omega) (by omega)
  simpa only [initial, final] using normalized

structure TopAddResult where
  memory : ByteArray
  activeWords : UInt256

def topAddAw1 (aw address : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 aw address

def topAddAw2 (aw address : UInt256) : UInt256 :=
  MultiLimbDivisionTrace.readWords1 (topAddAw1 aw address) address

def topAddStep (mem : ByteArray) (aw address carry : UInt256) : TopAddResult :=
  let value := MultiLimbDivisionTrace.readWord mem aw address + carry
  {
    memory := value.toByteArray.write 0 mem address.toNat 32
    activeWords := topAddAw2 aw address
  }

def topAddGas (aw address : UInt256) : Nat :=
  let aw1 := topAddAw1 aw address
  let aw2 := topAddAw2 aw address
  37 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- Add the correction carry into the saved top limb and rejoin quotient storage. -/
theorem topAddExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {u current index carry address qHat shift ret rem jj kEff v quotient vTop : UInt256}
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5645⟩
      (u :: current :: index :: carry :: address :: qHat :: shift :: ret :: rem :: jj ::
        kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let result := topAddStep mem aw address carry
    RDx runtimeBytecode ee g s0 ⟨5601⟩
      (⟨0⟩ :: ⟨0⟩ :: qHat :: shift :: ret :: rem :: jj :: kEff :: v :: quotient ::
        u :: vTop :: normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + 12)
        (C + topAddGas aw address) := by
  have rd5608 := evm_run h with [
    pop, pop, pop, dup2, mloadCanonical, add, swap1, mstoreCanonical,
    push0, dup1, pushCanonical 2 .PUSH2 ⟨5601⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd5608.withIndices
    (k' := k + 12) (C' := C + topAddGas aw address)
    (by omega) (by
      simp [topAddGas, topAddAw1, topAddAw2,
        MultiLimbDivisionTrace.readWords1]
      omega)
  simpa [topAddStep, topAddAw1, topAddAw2,
    MultiLimbDivisionTrace.readWord, MultiLimbDivisionTrace.readWords1,
    u256_add_comm] using normalized

/-- Store one accepted quotient digit and return to the outer-loop guard.  The array facts state
that the already allocated quotient header and selected element are active in memory. -/
theorem storeQuotientAndGuardExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj quotientCount : Nat} {tail : List UInt256}
    {address current qHat shift ret rem kEff v quotient u vTop : UInt256}
    (hjj : jj < quotientCount)
    (hjjWord : jj < UInt256.size)
    (hquotientCountWord : quotientCount < UInt256.size)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hquotElementAw : arrayAfterWord aw quotient jj = aw)
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5601⟩
      (address :: current :: qHat :: shift :: ret :: rem :: UInt256.ofNat jj ::
        kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat jj).isZero :: UInt256.ofNat jj :: shift :: ret ::
        rem :: UInt256.ofNat jj :: kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      (MultiLimbSchoolbookSingle.storeQuotient mem quotient jj qHat) aw rdata acc
      (k + 33) (C + 111) := by
  have hguard := arrayGuardExact mem aw quotient jj quotientCount hjj hjjWord
    hquotientCountWord hquotHeader
  have hguardRaw :
      ((UInt256.ofNat jj).lt
        (if quotient.toNat ≥ mem.size ∨ quotient ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding quotient.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have rd1538 := GeneratedTraces.trace_5601_body
    (by simp only [List.length_cons]; omega) h
  have hquotHeaderAwRaw : MultiLimbOddCompare.afterHeader aw quotient = aw :=
    hquotHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotHeaderAwRaw] at rd1538
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd5620 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539
    (by native_decide) (by native_decide)
  have hquotElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat jj).shiftLeft ⟨5⟩ + quotient + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      MultiLimbSchoolbookSingle.arrayAddress, MultiLimbSchoolbookShort.arrayAddress,
      MultiLimbOddCompare.elementPtr] using hquotElementAw
  have rd5457 := GeneratedTraces.trace_5613_body
    (by simp only [List.length_cons]; omega) rd5620
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotElementAwRaw] at rd5457
  have normalized := rd5457.withIndices
    (k' := k + 33) (C' := C + 111) (by omega) (by omega)
  simpa only [MultiLimbSchoolbookSingle.storeQuotient,
    MultiLimbSchoolbookSingle.arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

end Modexp.MultiLimbSchoolbookDivision
