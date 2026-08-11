import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupContract

/-!
# Normalized Knuth-division arrays

This module covers allocation and construction of the normalized divisor `v` and dividend `u`
after the exact `_clz` helper returns.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def vMemory (mem : ByteArray) (fp kEff : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize kEff)) fp kEff

def vWords (aw : UInt256) (fp kEff : Nat) : UInt256 :=
  newWordArrayWords aw fp kEff

def vAllocationGas (aw : UInt256) (fp kEff : Nat) : Nat :=
  21 + newWordArrayGas aw fp kEff

/-- Allocate the normalized-divisor array `v`. -/
theorem vAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp kEff m numQ ret shift : Nat} {tail : List UInt256}
    {quotient rem u divisor : UInt256}
    (hkEff : kEff ≤ 32)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kEff < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1003)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat shift :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff ::
        UInt256.ofNat m :: quotient :: u :: UInt256.ofNat numQ :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5378⟩
      (UInt256.ofNat fp :: UInt256.ofNat ret :: rem :: UInt256.ofNat shift ::
        UInt256.ofNat kEff :: UInt256.ofNat m :: quotient :: u ::
        UInt256.ofNat numQ :: divisor :: tail)
      (vMemory mem fp kEff) (vWords aw fp kEff) rdata acc
      (k + 84) (C + vAllocationGas aw fp kEff) := by
  have rd1487 := evm_run h with [
    jumpdest,
    swap2,
    pushCanonical 2 .PUSH2 ⟨5378⟩ (by decide),
    dup5,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5378 := newWordArrayExact hkEff hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd5378.withIndices
    (k' := k + 84) (C' := C + vAllocationGas aw fp kEff)
    (by omega) (by simp [vAllocationGas]; omega)
  simpa only [vMemory, vWords] using normalized

/-- Enter the shifting normalization loops when `_clz` returned a positive count. -/
theorem dispatchShiftNonzeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C shift : Nat} {tail : List UInt256}
    {v ret rem kEff m quotient u numQ divisor : UInt256}
    (hshiftPos : 0 < shift)
    (hshiftWord : shift < UInt256.size)
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨5378⟩
      (v :: ret :: rem :: UInt256.ofNat shift :: kEff :: m :: quotient :: u ::
        numQ :: divisor :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5391⟩
      (divisor :: m :: ret :: rem :: UInt256.ofNat shift :: kEff :: v :: quotient ::
        u :: numQ :: ⟨1⟩ :: tail) mem aw rdata acc (k + 11) (C + 37) := by
  have hshiftNe : UInt256.ofNat shift ≠ ⟨0⟩ := by
    intro heq
    have hnat := congrArg UInt256.toNat heq
    rw [UInt256.toNat_ofNat_of_lt hshiftWord] at hnat
    simp at hnat
    omega
  have hnonzero : (UInt256.ofNat shift).isZero.isZero = ⟨1⟩ := by
    rw [isZero_eq_zero_of_ne hshiftNe]
    native_decide
  have hcondition : UInt256.eq ⟨0⟩ (UInt256.ofNat shift).isZero.isZero = ⟨0⟩ := by
    rw [hnonzero]
    native_decide
  have rd5391 := GeneratedTraces.trace_5378_notTaken
    (by omega) h (by native_decide) hcondition
  rw [hnonzero] at rd5391
  have normalized := rd5391.withIndices
    (k' := k + 11) (C' := C + 37) (by omega) (by omega)
  simpa using normalized

/-- Enter the exact-copy normalization path when `_clz` returned zero. -/
theorem dispatchShiftZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {v ret rem kEff m quotient u numQ divisor : UInt256}
    (hdepth : tail.length ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨5378⟩
      (v :: ret :: rem :: ⟨0⟩ :: kEff :: m :: quotient :: u :: numQ :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6194⟩
      (divisor :: m :: ret :: rem :: ⟨0⟩ :: kEff :: v :: quotient :: u :: numQ ::
        ⟨0⟩ :: tail) mem aw rdata acc (k + 11) (C + 37) := by
  have rd6201 := GeneratedTraces.trace_5378_taken
    (by omega) h (by native_decide) (by native_decide) (by native_decide)
  have normalized := rd6201.withIndices
    (k' := k + 11) (C' := C + 37) (by omega) (by omega)
  simpa using normalized

def shiftZeroMemory (mem : ByteArray) (divisor v kEff : Nat) : ByteArray :=
  mem.write (divisor + 32) mem (v + 32) (32 * kEff)

def shiftZeroWords (aw : UInt256) (divisor v kEff : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M aw.toNat (max (v + 32) (divisor + 32)) (32 * kEff))

def shiftZeroExpansionGas (aw : UInt256) (divisor v kEff : Nat) : Nat :=
  Cₘ (shiftZeroWords aw divisor v kEff) - Cₘ aw

def shiftZeroCopyGas (aw : UInt256) (divisor v kEff : Nat) : Nat :=
  shiftZeroExpansionGas aw divisor v kEff + GasConstants.Gverylow +
    GasConstants.Gcopy * kEff

def arrayHeader (mem : ByteArray) (aw array : UInt256) : UInt256 :=
  MultiLimbSchoolbookSingle.arrayHeader mem aw array

def arrayAfterHeader (aw array : UInt256) : UInt256 :=
  MultiLimbSchoolbookSingle.arrayAfterHeader aw array

def arrayAddress (array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookSingle.arrayAddress array index

def arrayWord (mem : ByteArray) (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookSingle.arrayWord mem aw array index

def arrayAfterWord (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookSingle.arrayAfterWord aw array index

def shiftedWord (word carry : UInt256) (shift : Nat) : UInt256 :=
  UInt256.lor (word.shiftLeft (UInt256.ofNat shift)) carry

def shiftedCarry (word : UInt256) (shift : Nat) : UInt256 :=
  word.shiftRight (UInt256.ofNat (256 - shift))

def storeShiftedWord (mem : ByteArray) (v : UInt256) (index shift : Nat)
    (word carry : UInt256) : ByteArray :=
  (shiftedWord word carry shift).toByteArray.write 0 mem
    (arrayAddress v index).toNat 32

/-- Exact successful path through the compiler's checked `256 - shift` helper. -/
theorem checked256SubExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C shift ret : Nat} {tail : List UInt256}
    (hshift : shift ≤ 256)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1042⟩
      (UInt256.ofNat shift :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (256 - shift) :: tail) mem aw rdata acc
      (k + 10) (C + 40) := by
  have h256Word : 256 < UInt256.size := by decide
  have hshiftWord : shift < UInt256.size := lt_of_le_of_lt hshift h256Word
  have hresultWord : 256 - shift < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le 256 shift) h256Word
  have hsub : UInt256.sub ⟨256⟩ (UInt256.ofNat shift) =
      UInt256.ofNat (256 - shift) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [show (⟨256⟩ : UInt256).toNat = 256 by decide,
        UInt256.toNat_ofNat_of_lt hshiftWord,
        UInt256.toNat_ofNat_of_lt hresultWord]
    · rw [show (⟨256⟩ : UInt256).toNat = 256 by decide,
        UInt256.toNat_ofNat_of_lt hshiftWord]
      exact hshift
  have hcondition : UInt256.gt (UInt256.ofNat (256 - shift)) ⟨256⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hresultWord,
      show (⟨256⟩ : UInt256).toNat = 256 by decide]
    omega
  have rd1057 := GeneratedTraces.trace_1042_notTaken
    (by omega) h (by native_decide) (by simpa [hsub] using hcondition)
  rw [hsub] at rd1057
  have rdret := GeneratedTraces.trace_1057_jump
    (by simp only [List.length_cons]; omega) rd1057
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 10) (C' := C + 40) (by omega) (by omega)
  simpa using normalized

/-- Finish the successful `256 - shift` helper after a generated trace reaches its guard. -/
theorem checked256SubContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C shift ret : Nat} {tail : List UInt256}
    (hshift : shift ≤ 256)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨1056⟩
      (⟨1037⟩ :: (UInt256.sub ⟨256⟩ (UInt256.ofNat shift)).gt ⟨256⟩ ::
        UInt256.ofNat ret :: UInt256.sub ⟨256⟩ (UInt256.ofNat shift) :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (256 - shift) :: tail) mem aw rdata acc
      (k + 2) (C + 18) := by
  have h256Word : 256 < UInt256.size := by decide
  have hshiftWord : shift < UInt256.size := lt_of_le_of_lt hshift h256Word
  have hresultWord : 256 - shift < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le 256 shift) h256Word
  have hsub : UInt256.sub ⟨256⟩ (UInt256.ofNat shift) =
      UInt256.ofNat (256 - shift) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [show (⟨256⟩ : UInt256).toNat = 256 by decide,
        UInt256.toNat_ofNat_of_lt hshiftWord,
        UInt256.toNat_ofNat_of_lt hresultWord]
    · rw [show (⟨256⟩ : UInt256).toNat = 256 by decide,
        UInt256.toNat_ofNat_of_lt hshiftWord]
      exact hshift
  have hcondition : UInt256.gt (UInt256.ofNat (256 - shift)) ⟨256⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hresultWord,
      show (⟨256⟩ : UInt256).toNat = 256 by decide]
    omega
  rw [hsub] at h
  have rd1057 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_1057_jump
    (by simp only [List.length_cons]; omega) rd1057
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 2) (C' := C + 18) (by omega) (by omega)
  simpa using normalized

/-- Finish the successful checked `x - 1` helper after its generated guard body. -/
theorem checkedSubOneContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x ret : Nat} {tail : List UInt256}
    (hxPos : 0 < x)
    (hx : x < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨1035⟩
      (⟨1037⟩ ::
        (UInt256.ofNat x + (⟨0⟩ : UInt256).lnot).gt (UInt256.ofNat x) ::
        UInt256.ofNat ret :: (UInt256.ofNat x + (⟨0⟩ : UInt256).lnot) :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x - 1) :: tail) mem aw rdata acc
      (k + 2) (C + 18) := by
  have hxPred : x - 1 < UInt256.size := by omega
  have hsub : UInt256.ofNat x + (⟨0⟩ : UInt256).lnot =
      UInt256.ofNat (x - 1) := by
    rw [show x = (x - 1) + 1 by omega, u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat ((x - 1) + 1)) =
      UInt256.ofNat (x - 1)
    exact MultiLimbOddCompare.scanIndex_ofNat_succ (x - 1) (by omega)
  have hcondition : UInt256.gt (UInt256.ofNat (x - 1)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxPred, UInt256.toNat_ofNat_of_lt hx]
    omega
  rw [hsub] at h
  have rd1036 := h.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have rdret := GeneratedTraces.trace_1036_jump
    (by simp only [List.length_cons]; omega) rd1036
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 2) (C' := C + 18) (by omega) (by omega)
  simpa using normalized

/-- One nonzero-shift divisor-normalization iteration, including all array bounds checks. -/
theorem divisorShiftCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i kEff shift : Nat} {tail : List UInt256}
    {divisor m ret rem v quotient u numQ carry value : UInt256}
    (hi : i < kEff)
    (hkEffWord : kEff < UInt256.size)
    (hshift : shift < 256)
    (hdivHeader : arrayHeader mem aw divisor = UInt256.ofNat kEff)
    (hdivHeaderAw : arrayAfterHeader aw divisor = aw)
    (hdivElementAw : arrayAfterWord aw divisor i = aw)
    (hvalue : arrayWord mem aw divisor i = value)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvElementAw : arrayAfterWord aw v i = aw)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5394⟩
      (carry :: divisor :: UInt256.ofNat i :: m :: ret :: rem ::
        UInt256.ofNat shift :: UInt256.ofNat kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5394⟩
      (shiftedCarry value shift :: divisor :: UInt256.ofNat (i + 1) :: m ::
        ret :: rem :: UInt256.ofNat shift :: UInt256.ofNat kEff :: v ::
        quotient :: u :: numQ :: ⟨1⟩ :: tail)
      (storeShiftedWord mem v i shift value carry) aw rdata acc
      (k + 103) (C + 369) := by
  have hiWord : i < UInt256.size := lt_trans hi hkEffWord
  have hiSuccWord : i + 1 < UInt256.size := by
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hi) hkEffWord
  have hloopNe : (UInt256.ofNat i).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
  have hguard : ((UInt256.ofNat i).lt
      (MultiLimbOddCompare.headerWord mem aw divisor)).isZero = ⟨0⟩ := by
    have hbound : (UInt256.ofNat i).toNat <
        (MultiLimbOddCompare.headerWord mem aw divisor).toNat := by
      rw [show MultiLimbOddCompare.headerWord mem aw divisor =
        UInt256.ofNat kEff from hdivHeader,
        UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
    rw [ult_one hbound]
    native_decide
  have hvGuard : ((UInt256.ofNat i).lt
      (MultiLimbOddCompare.headerWord mem aw v)).isZero = ⟨0⟩ := by
    have hbound : (UInt256.ofNat i).toNat <
        (MultiLimbOddCompare.headerWord mem aw v).toNat := by
      rw [show MultiLimbOddCompare.headerWord mem aw v =
        UInt256.ofNat kEff from hvHeader,
        UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      exact hi
    rw [ult_one hbound]
    native_decide
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = value := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvalue
  have hdivElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        hdivElementAw
  have hvElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + v + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        hvElementAw
  have hdivHeaderAw' : MultiLimbOddCompare.afterHeader aw divisor = aw :=
    hdivHeaderAw
  have hvHeaderAw' : MultiLimbOddCompare.afterHeader aw v = aw :=
    hvHeaderAw
  have rd6143 := GeneratedTraces.trace_5394_taken
    (tail := v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloopNe (by native_decide)
  have rd1538a := GeneratedTraces.trace_6136_body
    (by simp only [List.length_cons]; omega) rd6143
  have hguardRaw :
      ((UInt256.ofNat i).lt
        (if divisor.toNat ≥ mem.size ∨ divisor ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding divisor.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have rd1539a := rd1538a.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, hdivHeaderAw'] at rd1539a
  have rd6156 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1538b := GeneratedTraces.trace_6149_body
    (by simp only [List.length_cons]; omega) rd6156
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538b
  rw [hvalueRaw] at rd1538b
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538b
  rw [hdivElementAwRaw, hdivHeaderAw'] at rd1538b
  have rd1539b := rd1538b.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd6171 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd1056 := GeneratedTraces.trace_6164_body
    (by simp only [List.length_cons]; omega) rd6171
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1056
  rw [hvalueRaw] at rd1056
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1056
  rw [hdivElementAwRaw] at rd1056
  have rd6181 := checked256SubContinueExact (shift := shift) (ret := 6174)
    (tail := value :: UInt256.ofNat i :: ⟨1⟩ :: divisor ::
      shiftedWord value carry shift :: m :: ret :: rem :: UInt256.ofNat shift ::
      UInt256.ofNat kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
    (Nat.le_of_lt hshift) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1056
  have rd1538c := GeneratedTraces.trace_6174_body
    (by simp only [List.length_cons]; omega) rd6181
  have hvGuardRaw :
      ((UInt256.ofNat i).lt
        (if v.toNat ≥ mem.size ∨ v ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding v.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hvGuard
  have rd1539c := rd1538c.jumpiNT (by native_decide) hvGuardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, hvHeaderAw'] at rd1539c
  have rd6193 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539c
    (by native_decide) (by native_decide)
  have rd5394 := evm_run rd6193 with [
    jumpdest,
    mstoreCanonical,
    add,
    swap2,
    pushCanonical 2 .PUSH2 ⟨5394⟩ (by decide),
    jump (by native_decide)
  ]
  rw [← MultiLimbOddCompare.afterHeader_generated, hvElementAwRaw] at rd5394
  have hiAdd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) :=
    ofNat_add_bounded hiSuccWord
  rw [hiAdd] at rd5394
  have normalized := rd5394.withIndices
    (k' := k + 103) (C' := C + 369) (by omega) (by omega)
  simpa only [shiftedWord, shiftedCarry, storeShiftedWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress] using normalized

structure DivisorShiftResult where
  memory : ByteArray
  carry : UInt256
  steps : Nat
  gas : Nat

/-- Pure operational recurrence for consecutive low-to-high divisor normalization cycles. -/
def shiftDivisor
    (aw divisor v : UInt256) (shift : Nat) :
    Nat → Nat → ByteArray → UInt256 → DivisorShiftResult
  | _, 0, mem, carry => ⟨mem, carry, 0, 0⟩
  | index, count + 1, mem, carry =>
      let value := arrayWord mem aw divisor index
      let nextMemory := storeShiftedWord mem v index shift value carry
      let nextCarry := shiftedCarry value shift
      let rest := shiftDivisor aw divisor v shift (index + 1) count nextMemory nextCarry
      ⟨rest.memory, rest.carry, 103 + rest.steps, 369 + rest.gas⟩

/-- Array bounds and active-memory facts for every evolving divisor-normalization state. -/
inductive ValidDivisorShift
    (aw divisor v : UInt256) (kEff shift : Nat) :
    Nat → Nat → ByteArray → UInt256 → Prop
  | zero (index : Nat) (mem : ByteArray) (carry : UInt256) :
      ValidDivisorShift aw divisor v kEff shift index 0 mem carry
  | succ (index count : Nat) (mem : ByteArray) (carry : UInt256)
      (hdivHeader : arrayHeader mem aw divisor = UInt256.ofNat kEff)
      (hdivHeaderAw : arrayAfterHeader aw divisor = aw)
      (hdivElementAw : arrayAfterWord aw divisor index = aw)
      (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
      (hvHeaderAw : arrayAfterHeader aw v = aw)
      (hvElementAw : arrayAfterWord aw v index = aw)
      (rest : ValidDivisorShift aw divisor v kEff shift (index + 1) count
        (storeShiftedWord mem v index shift (arrayWord mem aw divisor index) carry)
        (shiftedCarry (arrayWord mem aw divisor index) shift)) :
      ValidDivisorShift aw divisor v kEff shift index (count + 1) mem carry

/-- Ordinary separated-array layout implies every evolving divisor-shift bounds invariant. -/
theorem validDivisorShiftOfLayout
    (aw divisor v : UInt256) (kEff shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hdivHeader : arrayHeader mem aw divisor = UInt256.ofNat kEff)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hdivHeaderAw : arrayAfterHeader aw divisor = aw)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hdivElementAw : ∀ j, index ≤ j → j < index + count →
      arrayAfterWord aw divisor j = aw)
    (hvElementAw : ∀ j, index ≤ j → j < index + count →
      arrayAfterWord aw v j = aw)
    (hwrite : ∀ j, index ≤ j → j < index + count →
      (arrayAddress v j).toNat + 32 ≤ mem.size)
    (hdivisorBelow : ∀ j, index ≤ j → j < index + count →
      divisor.toNat + 32 ≤ (arrayAddress v j).toNat)
    (hvBelow : ∀ j, index ≤ j → j < index + count →
      v.toNat + 32 ≤ (arrayAddress v j).toNat) :
    ValidDivisorShift aw divisor v kEff shift index count mem carry := by
  induction count generalizing index mem carry with
  | zero =>
      exact ValidDivisorShift.zero index mem carry
  | succ count ih =>
      let value := arrayWord mem aw divisor index
      let nextValue := shiftedWord value carry shift
      let nextMemory := storeShiftedWord mem v index shift value carry
      let nextCarry := shiftedCarry value shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size :=
        hwrite index (by omega) (by omega)
      have hnextSize : nextMemory.size = mem.size := by
        simpa [nextMemory, nextValue, storeShiftedWord,
          MultiLimbSchoolbookSingle.storeQuotient] using
          MultiLimbSchoolbookSingle.storeQuotient_size_eq
            mem v index nextValue hheadWrite
      have hdivHeaderNext : arrayHeader nextMemory aw divisor = UInt256.ofNat kEff := by
        calc
          arrayHeader nextMemory aw divisor = arrayHeader mem aw divisor := by
            simpa [nextMemory, nextValue, storeShiftedWord, arrayHeader,
              MultiLimbSchoolbookSingle.storeQuotient] using
              MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq
                mem aw v divisor index nextValue hheadWrite
                (hdivisorBelow index (by omega) (by omega))
          _ = UInt256.ofNat kEff := hdivHeader
      have hvHeaderNext : arrayHeader nextMemory aw v = UInt256.ofNat kEff := by
        calc
          arrayHeader nextMemory aw v = arrayHeader mem aw v := by
            simpa [nextMemory, nextValue, storeShiftedWord, arrayHeader,
              MultiLimbSchoolbookSingle.storeQuotient] using
              MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq
                mem aw v v index nextValue hheadWrite
                (hvBelow index (by omega) (by omega))
          _ = UInt256.ofNat kEff := hvHeader
      have htailDivElement : ∀ j, index + 1 ≤ j → j < index + 1 + count →
          arrayAfterWord aw divisor j = aw := by
        intro j hj hlt
        exact hdivElementAw j (by omega) (by omega)
      have htailVElement : ∀ j, index + 1 ≤ j → j < index + 1 + count →
          arrayAfterWord aw v j = aw := by
        intro j hj hlt
        exact hvElementAw j (by omega) (by omega)
      have htailWrite : ∀ j, index + 1 ≤ j → j < index + 1 + count →
          (arrayAddress v j).toNat + 32 ≤ nextMemory.size := by
        intro j hj hlt
        rw [hnextSize]
        exact hwrite j (by omega) (by omega)
      have htailDivisorBelow : ∀ j, index + 1 ≤ j → j < index + 1 + count →
          divisor.toNat + 32 ≤ (arrayAddress v j).toNat := by
        intro j hj hlt
        exact hdivisorBelow j (by omega) (by omega)
      have htailVBelow : ∀ j, index + 1 ≤ j → j < index + 1 + count →
          v.toNat + 32 ≤ (arrayAddress v j).toNat := by
        intro j hj hlt
        exact hvBelow j (by omega) (by omega)
      have rest := ih (index + 1) nextMemory nextCarry hdivHeaderNext hvHeaderNext
        htailDivElement htailVElement htailWrite
        htailDivisorBelow htailVBelow
      exact ValidDivisorShift.succ index count mem carry hdivHeader hdivHeaderAw
        (hdivElementAw index (by omega) (by omega)) hvHeader hvHeaderAw
        (hvElementAw index (by omega) (by omega)) rest

/-- Execute an arbitrary consecutive range of divisor-normalization iterations. -/
theorem shiftDivisorCyclesExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C index count kEff shift : Nat} {tail : List UInt256}
    {divisor m ret rem v quotient u numQ carry : UInt256}
    (hrange : index + count ≤ kEff)
    (hkEffWord : kEff < UInt256.size)
    (hshift : shift < 256)
    (hvalid : ValidDivisorShift aw divisor v kEff shift index count mem carry)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5394⟩
      (carry :: divisor :: UInt256.ofNat index :: m :: ret :: rem ::
        UInt256.ofNat shift :: UInt256.ofNat kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail) mem aw rdata acc k C) :
    let result := shiftDivisor aw divisor v shift index count mem carry
    RDx runtimeBytecode ee g s0 ⟨5394⟩
      (result.carry :: divisor :: UInt256.ofNat (index + count) :: m :: ret :: rem ::
        UInt256.ofNat shift :: UInt256.ofNat kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail) result.memory aw rdata acc
      (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | zero index mem carry =>
      simpa [shiftDivisor]
  | succ index count current currentCarry hdivHeader hdivHeaderAw hdivElementAw
      hvHeader hvHeaderAw hvElementAw rest ih =>
      let value := arrayWord current aw divisor index
      let nextMemory := storeShiftedWord current v index shift value currentCarry
      let nextCarry := shiftedCarry value shift
      have hi : index < kEff := by omega
      have rdCycle := divisorShiftCycleExact hi hkEffWord hshift hdivHeader
        hdivHeaderAw hdivElementAw rfl hvHeader hvHeaderAw hvElementAw hdepth h
      have rdFinal := ih (by omega) rdCycle
      have normalized := rdFinal.withIndices
        (k' := k + (shiftDivisor aw divisor v shift index (count + 1)
          current currentCarry).steps)
        (C' := C + (shiftDivisor aw divisor v shift index (count + 1)
          current currentCarry).gas)
        (by simp [shiftDivisor]; omega)
        (by simp [shiftDivisor]; omega)
      simpa [shiftDivisor, value, nextMemory, nextCarry, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using normalized

/-- Initialize, execute, and exit the complete `kEff`-limb divisor-normalization loop. -/
theorem shiftAllDivisorLimbsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff shift : Nat} {tail : List UInt256}
    {divisor m ret rem v quotient u numQ : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hshift : shift < 256)
    (hvalid : ValidDivisorShift aw divisor v kEff shift 0 kEff mem ⟨0⟩)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5391⟩
      (divisor :: m :: ret :: rem :: UInt256.ofNat shift :: UInt256.ofNat kEff :: v ::
        quotient :: u :: numQ :: ⟨1⟩ :: tail) mem aw rdata acc k C) :
    let result := shiftDivisor aw divisor v shift 0 kEff mem ⟨0⟩
    RDx runtimeBytecode ee g s0 ⟨5402⟩
      (result.carry :: divisor :: UInt256.ofNat kEff :: m :: ret :: rem ::
        UInt256.ofNat shift :: UInt256.ofNat kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail) result.memory aw rdata acc
      (k + result.steps + 9) (C + result.gas + 31) := by
  have rd5394 := evm_run h with [
    push0,
    swap1,
    dup2
  ]
  have rdFinal := shiftDivisorCyclesExact (index := 0) (count := kEff)
    (by omega) hkEffWord hshift hvalid hdepth rd5394
  have hexit : (UInt256.ofNat (0 + kEff)).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    simp
  have rd5402 := GeneratedTraces.trace_5394_notTaken
    (tail := v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
    (by simp only [List.length_cons]; omega) rdFinal
    (by native_decide) hexit
  have normalized := rd5402.withIndices
    (k' := k + (shiftDivisor aw divisor v shift 0 kEff mem ⟨0⟩).steps + 9)
    (C' := C + (shiftDivisor aw divisor v shift 0 kEff mem ⟨0⟩).gas + 31)
    (by omega) (by omega)
  simpa using normalized

/-- One in-place dividend-normalization iteration, including every bounds check. -/
theorem dividendShiftCycleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i mCount uCount shift : Nat} {tail : List UInt256}
    {ret rem v quotient u numQ carry value kEff : UInt256}
    (hi : i < mCount)
    (hmU : mCount ≤ uCount)
    (huCountWord : uCount < UInt256.size)
    (hmWord : mCount < UInt256.size)
    (hshift : shift < 256)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huElementAw : arrayAfterWord aw u i = aw)
    (hvalue : arrayWord mem aw u i = value)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5408⟩
      (UInt256.ofNat i :: UInt256.ofNat mCount :: carry :: ret :: rem ::
        UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5408⟩
      (UInt256.ofNat (i + 1) :: UInt256.ofNat mCount :: shiftedCarry value shift ::
        ret :: rem :: UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail)
      (storeShiftedWord mem u i shift value carry) aw rdata acc
      (k + 103) (C + 369) := by
  have hiWord : i < UInt256.size := lt_trans hi hmWord
  have hiSuccWord : i + 1 < UInt256.size := by
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hi) hmWord
  have hiU : i < uCount := lt_of_lt_of_le hi hmU
  have hloopNe : (UInt256.ofNat i).lt (UInt256.ofNat mCount) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt hmWord]
      exact hi
  have hguard : ((UInt256.ofNat i).lt
      (MultiLimbOddCompare.headerWord mem aw u)).isZero = ⟨0⟩ := by
    have hbound : (UInt256.ofNat i).toNat <
        (MultiLimbOddCompare.headerWord mem aw u).toNat := by
      rw [show MultiLimbOddCompare.headerWord mem aw u =
        UInt256.ofNat uCount from huHeader,
        UInt256.toNat_ofNat_of_lt hiWord,
        UInt256.toNat_ofNat_of_lt huCountWord]
      exact hiU
    rw [ult_one hbound]
    native_decide
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + u + ⟨32⟩) = value := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvalue
  have huElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        huElementAw
  have huHeaderAw' : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have hguardRaw :
      ((UInt256.ofNat i).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have rd6085 := GeneratedTraces.trace_5408_taken
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloopNe (by native_decide)
  have rd1538a := GeneratedTraces.trace_6078_body
    (by simp only [List.length_cons]; omega) rd6085
  have rd1539a := rd1538a.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539a
  have rd6099 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539a
    (by native_decide) (by native_decide)
  have rd1538b := GeneratedTraces.trace_6092_body
    (by simp only [List.length_cons]; omega) rd6099
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1538b
  rw [hvalueRaw] at rd1538b
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1538b
  rw [huElementAwRaw, huHeaderAw'] at rd1538b
  have rd1539b := rd1538b.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd6114 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b
    (by native_decide) (by native_decide)
  have rd1056 := GeneratedTraces.trace_6107_body
    (by simp only [List.length_cons]; omega) rd6114
  simp_rw [← MultiLimbOddCompare.headerWord_generated] at rd1056
  rw [hvalueRaw] at rd1056
  simp_rw [← MultiLimbOddCompare.afterHeader_generated] at rd1056
  rw [huElementAwRaw] at rd1056
  have rd6124 := checked256SubContinueExact (shift := shift) (ret := 6117)
    (Nat.le_of_lt hshift) (by native_decide)
    (by simp only [List.length_cons]; omega) rd1056
  have rd1538c := GeneratedTraces.trace_6117_body
    (by simp only [List.length_cons]; omega) rd6124
  have rd1539c := rd1538c.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539c
  have rd6136 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539c
    (by native_decide) (by native_decide)
  have rd5408 := evm_run rd6136 with [
    jumpdest,
    mstoreCanonical,
    add,
    pushCanonical 2 .PUSH2 ⟨5408⟩ (by decide),
    jump (by native_decide)
  ]
  rw [← MultiLimbOddCompare.afterHeader_generated, huElementAwRaw] at rd5408
  have hiAdd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) :=
    ofNat_add_bounded hiSuccWord
  rw [hiAdd] at rd5408
  have normalized := rd5408.withIndices
    (k' := k + 103) (C' := C + 369) (by omega) (by omega)
  simpa only [shiftedWord, shiftedCarry, storeShiftedWord, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress] using normalized

/-- Execute an arbitrary consecutive range of in-place dividend-normalization iterations. -/
theorem shiftDividendCyclesExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C index count mCount uCount shift : Nat} {tail : List UInt256}
    {ret rem v quotient u numQ carry kEff : UInt256}
    (hrange : index + count ≤ mCount)
    (hmU : mCount ≤ uCount)
    (huCountWord : uCount < UInt256.size)
    (hmWord : mCount < UInt256.size)
    (hshift : shift < 256)
    (hvalid : ValidDivisorShift aw u u uCount shift index count mem carry)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5408⟩
      (UInt256.ofNat index :: UInt256.ofNat mCount :: carry :: ret :: rem ::
        UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    let result := shiftDivisor aw u u shift index count mem carry
    RDx runtimeBytecode ee g s0 ⟨5408⟩
      (UInt256.ofNat (index + count) :: UInt256.ofNat mCount :: result.carry ::
        ret :: rem :: UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail) result.memory aw rdata acc
      (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | zero index mem carry =>
      simpa [shiftDivisor]
  | succ index count current currentCarry huHeader huHeaderAw huElementAw
      _ _ _ rest ih =>
      let value := arrayWord current aw u index
      let nextMemory := storeShiftedWord current u index shift value currentCarry
      let nextCarry := shiftedCarry value shift
      have hi : index < mCount := by omega
      have rdCycle := dividendShiftCycleExact hi hmU huCountWord hmWord hshift
        huHeader huHeaderAw huElementAw rfl hdepth h
      have rdFinal := ih (by omega) rdCycle
      have normalized := rdFinal.withIndices
        (k' := k + (shiftDivisor aw u u shift index (count + 1)
          current currentCarry).steps)
        (C' := C + (shiftDivisor aw u u shift index (count + 1)
          current currentCarry).gas)
        (by simp [shiftDivisor]; omega)
        (by simp [shiftDivisor]; omega)
      simpa [shiftDivisor, value, nextMemory, nextCarry, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using normalized

/-- Initialize, execute, and exit the complete `m`-limb dividend-normalization loop. -/
theorem shiftAllDividendLimbsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C mCount uCount shift : Nat} {tail : List UInt256}
    {divisorCarry divisor ret rem v quotient u numQ kEff : UInt256}
    (hmU : mCount ≤ uCount)
    (huCountWord : uCount < UInt256.size)
    (hmWord : mCount < UInt256.size)
    (hshift : shift < 256)
    (hvalid : ValidDivisorShift aw u u uCount shift 0 mCount mem ⟨0⟩)
    (hdepth : tail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5402⟩
      (divisorCarry :: divisor :: kEff :: UInt256.ofNat mCount :: ret :: rem ::
        UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    let result := shiftDivisor aw u u shift 0 mCount mem ⟨0⟩
    RDx runtimeBytecode ee g s0 ⟨5416⟩
      (UInt256.ofNat mCount :: UInt256.ofNat mCount :: result.carry :: ret :: rem ::
        UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
      result.memory aw rdata acc (k + result.steps + 12) (C + result.gas + 36) := by
  have rd5408 := evm_run h with [
    pop,
    pop,
    pop,
    push0,
    swap1,
    push0
  ]
  have rdFinal := shiftDividendCyclesExact (index := 0) (count := mCount)
    (by omega) hmU huCountWord hmWord hshift hvalid hdepth rd5408
  have hexit : (UInt256.ofNat (0 + mCount)).lt (UInt256.ofNat mCount) = ⟨0⟩ := by
    apply ult_zero
    simp
  have rd5416 := GeneratedTraces.trace_5408_notTaken
    (by simp only [List.length_cons]; omega) rdFinal
    (by native_decide) hexit
  have normalized := rd5416.withIndices
    (k' := k + (shiftDivisor aw u u shift 0 mCount mem ⟨0⟩).steps + 12)
    (C' := C + (shiftDivisor aw u u shift 0 mCount mem ⟨0⟩).gas + 36)
    (by omega) (by omega)
  simpa using normalized

def storeDividendTopCarry
    (mem : ByteArray) (u : UInt256) (m : Nat) (carry : UInt256) : ByteArray :=
  carry.toByteArray.write 0 mem (arrayAddress u m).toNat 32

/-- Store the final normalization carry in the allocated extra limb `u[m]`. -/
theorem storeDividendTopCarryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C mCount uCount shift : Nat} {tail : List UInt256}
    {carry ret rem kEff v quotient u numQ : UInt256}
    (hmU : mCount < uCount)
    (hmWord : mCount < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huElementAw : arrayAfterWord aw u mCount = aw)
    (hdepth : tail.length ≤ 1000)
    (h : RDx runtimeBytecode ee g s0 ⟨5416⟩
      (UInt256.ofNat mCount :: UInt256.ofNat mCount :: carry :: ret :: rem ::
        UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5428⟩
      (ret :: rem :: UInt256.ofNat shift :: kEff :: v :: quotient :: u :: numQ ::
        ⟨1⟩ :: tail)
      (storeDividendTopCarry mem u mCount carry) aw rdata acc
      (k + 24) (C + 84) := by
  have hguard : ((UInt256.ofNat mCount).lt
      (MultiLimbOddCompare.headerWord mem aw u)).isZero = ⟨0⟩ := by
    have hbound : (UInt256.ofNat mCount).toNat <
        (MultiLimbOddCompare.headerWord mem aw u).toNat := by
      rw [show MultiLimbOddCompare.headerWord mem aw u =
        UInt256.ofNat uCount from huHeader,
        UInt256.toNat_ofNat_of_lt hmWord,
        UInt256.toNat_ofNat_of_lt huCountWord]
      exact hmU
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      ((UInt256.ofNat mCount).lt
        (if u.toNat ≥ mem.size ∨ u ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding u.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have huHeaderAw' : MultiLimbOddCompare.afterHeader aw u = aw := huHeaderAw
  have huElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat mCount).shiftLeft ⟨5⟩ + u + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        huElementAw
  have rd1538 := GeneratedTraces.trace_5416_body
    (by simp only [List.length_cons]; omega) h
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, huHeaderAw'] at rd1539
  have rd5426 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539
    (by native_decide) (by native_decide)
  have rd5428 := evm_run rd5426 with [
    jumpdest,
    mstoreCanonical
  ]
  rw [← MultiLimbOddCompare.afterHeader_generated, huElementAwRaw] at rd5428
  have normalized := rd5428.withIndices
    (k' := k + 24) (C' := C + 84) (by omega) (by omega)
  simpa only [storeDividendTopCarry, arrayAddress,
    MultiLimbSchoolbookSingle.arrayAddress] using normalized

/-- Load the top normalized-divisor limb and arrange the outer division-loop frame. -/
theorem loadNormalizedTopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff : Nat} {tail : List UInt256}
    {ret rem shift v quotient u numQ vTop normalized : UInt256}
    (hkEffPos : 0 < kEff)
    (hkEffWord : kEff < UInt256.size)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvTopAw : arrayAfterWord aw v (kEff - 1) = aw)
    (hvTop : arrayWord mem aw v (kEff - 1) = vTop)
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode ee g s0 ⟨5428⟩
      (ret :: rem :: shift :: UInt256.ofNat kEff :: v :: quotient :: u :: numQ ::
        normalized :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5450⟩
      (shift :: ret :: rem :: numQ :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalized :: tail) mem aw rdata acc (k + 42) (C + 149) := by
  have hkEffPredWord : kEff - 1 < UInt256.size := by omega
  have rd1035 := GeneratedTraces.trace_5428_body
    (by simp only [List.length_cons]; omega) h
  have rd5440 := checkedSubOneContinueExact (x := kEff) (ret := 5440)
    hkEffPos hkEffWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1035
  have hguard :
      ((UInt256.ofNat (kEff - 1)).lt
        (MultiLimbOddCompare.headerWord mem aw v)).isZero = ⟨0⟩ := by
    have hbound : (UInt256.ofNat (kEff - 1)).toNat <
        (MultiLimbOddCompare.headerWord mem aw v).toNat := by
      rw [show MultiLimbOddCompare.headerWord mem aw v = UInt256.ofNat kEff from
          hvHeader,
        UInt256.toNat_ofNat_of_lt hkEffPredWord,
        UInt256.toNat_ofNat_of_lt hkEffWord]
      omega
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      ((UInt256.ofNat (kEff - 1)).lt
        (if v.toNat ≥ mem.size ∨ v ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding v.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have hvHeaderAw' : MultiLimbOddCompare.afterHeader aw v = aw := hvHeaderAw
  have hvTopRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat (kEff - 1)).shiftLeft ⟨5⟩ + v + ⟨32⟩) = vTop := by
    simpa only [arrayWord, MultiLimbSchoolbookSingle.arrayWord,
      MultiLimbSchoolbookShort.arrayWord, MultiLimbOddCompare.loadedWord,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvTop
  have hvTopAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat (kEff - 1)).shiftLeft ⟨5⟩ + v + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookSingle.arrayAfterWord,
      MultiLimbSchoolbookShort.arrayAfterWord, MultiLimbOddCompare.afterLoad,
      arrayAddress, MultiLimbSchoolbookSingle.arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using
        hvTopAw
  have rd1538 := GeneratedTraces.trace_5440_body
    (by simp only [List.length_cons]; omega) rd5440
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated, hvHeaderAw'] at rd1539
  have rd5446 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539
    (by native_decide) (by native_decide)
  have rd5450 := evm_run rd5446 with [
    jumpdest,
    mloadCanonical,
    swap8,
    swap3
  ]
  rw [← MultiLimbOddCompare.headerWord_generated, hvTopRaw,
    ← MultiLimbOddCompare.afterHeader_generated, hvTopAwRaw] at rd5450
  have normalized := rd5450.withIndices
    (k' := k + 42) (C' := C + 149) (by omega) (by omega)
  simpa using normalized

/-- The zero-shift path copies every divisor limb into `v` exactly. -/
theorem shiftZeroCopyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C divisor v kEff ret : Nat} {tail : List UInt256}
    {m rem quotient u numQ : UInt256}
    (hkBytes : 32 * kEff < UInt256.size)
    (hdivisor32 : divisor + 32 < UInt256.size)
    (hv32 : v + 32 < UInt256.size)
    (hdepth : tail.length ≤ 1006)
    (h : RDx runtimeBytecode ee g s0 ⟨6194⟩
      (UInt256.ofNat divisor :: m :: UInt256.ofNat ret :: rem :: ⟨0⟩ ::
        UInt256.ofNat kEff :: UInt256.ofNat v :: quotient :: u :: numQ :: ⟨0⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5428⟩
      (UInt256.ofNat ret :: rem :: ⟨0⟩ :: UInt256.ofNat kEff :: UInt256.ofNat v ::
        quotient :: u :: numQ :: ⟨0⟩ :: tail)
      (shiftZeroMemory mem divisor v kEff) (shiftZeroWords aw divisor v kEff)
      rdata acc (k + 15) (C + 44 + shiftZeroCopyGas aw divisor v kEff) := by
  have hshift : UInt256.shiftLeft (UInt256.ofNat kEff) ⟨5⟩ =
      UInt256.ofNat (32 * kEff) := shiftLeft5_ofNat_eq hkBytes
  have hsrc : UInt256.ofNat divisor + ⟨32⟩ = UInt256.ofNat (divisor + 32) :=
    ofNat_add_bounded hdivisor32
  have hdst : UInt256.ofNat v + ⟨32⟩ = UInt256.ofNat (v + 32) :=
    ofNat_add_bounded hv32
  have hlenNat : (UInt256.ofNat (32 * kEff)).toNat = 32 * kEff :=
    UInt256.toNat_ofNat_of_lt hkBytes
  have hsrcNat : (UInt256.ofNat (divisor + 32)).toNat = divisor + 32 :=
    UInt256.toNat_ofNat_of_lt hdivisor32
  have hdstNat : (UInt256.ofNat (v + 32)).toNat = v + 32 :=
    UInt256.toNat_ofNat_of_lt hv32
  have hcopyWords : (31 + 32 * kEff) / 32 = kEff := by omega
  have rd6216 := evm_run h with [
    jumpdest,
    swap1,
    pop,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup6,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    swap2,
    add,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup8,
    add
  ]
  rw [hshift, hsrc, hdst] at rd6216
  have rd6217 := RDx.mcopy
    (shiftZeroExpansionGas aw divisor v kEff)
    (shiftZeroMemory mem divisor v kEff)
    (shiftZeroWords aw divisor v kEff) rd6216 (by native_decide)
    (by
      intro s hsaw hstk
      simp [shiftZeroExpansionGas, shiftZeroWords, memoryExpansionCost,
        memoryExpansionCost.μᵢ', hsaw, hstk, hsrcNat, hdstNat, hlenNat])
    (by simp [shiftZeroMemory, hsrcNat, hdstNat, hlenNat])
    (by simp [shiftZeroWords, hsrcNat, hdstNat, hlenNat])
    (by simp only [List.length_cons]; omega)
  have rd5428 := evm_run rd6217 with [
    pushCanonical 2 .PUSH2 ⟨5428⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd5428.withIndices
    (k' := k + 15) (C' := C + 44 + shiftZeroCopyGas aw divisor v kEff)
    (by omega) (by
      simp [shiftZeroCopyGas, GasConstants.Gverylow, GasConstants.Gcopy, hlenNat,
        hcopyWords, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega)
  simpa using normalized

/-- Every copied payload word is exactly the corresponding divisor word. -/
theorem shiftZeroMemory_limb
    (mem : ByteArray) (divisor v kEff i : Nat)
    (hkEffPos : 0 < kEff)
    (hi : i < kEff)
    (hsource : divisor + 32 + 32 * kEff ≤ mem.size)
    (hdest : v + 32 ≤ mem.size) :
    (shiftZeroMemory mem divisor v kEff).readWithPadding (v + 32 + 32 * i) 32 =
      mem.readWithPadding (divisor + 32 + 32 * i) 32 := by
  unfold shiftZeroMemory
  rw [Modexp.MultiLimbMontgomeryCIOSSemantic.write_read_copy_window
    mem mem (divisor + 32) (v + 32) (32 * kEff) (32 * i) 32]
  · symm
    apply readWithPadding_eq_extract'
    · omega
    · norm_num
    · omega
  · omega
  · exact hsource
  · exact hdest
  · omega
  · omega
  · norm_num

end Modexp.MultiLimbSchoolbookNormalization
