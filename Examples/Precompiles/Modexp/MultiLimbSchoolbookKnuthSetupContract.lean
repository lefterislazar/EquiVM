import Examples.Precompiles.Modexp.MultiLimbSchoolbookSingleContract

/-!
# Normalized Knuth-division setup

The first setup segment computes `numQlimbs = m - kEff + 1` through the compiler's checked
arithmetic helpers before allocating the quotient.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookKnuthSetup

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def quotientMemory (mem : ByteArray) (fp numQ : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize numQ)) fp numQ

def quotientWords (aw : UInt256) (fp numQ : Nat) : UInt256 :=
  newWordArrayWords aw fp numQ

def quotientAllocationGas (aw : UInt256) (fp numQ : Nat) : Nat :=
  21 + newWordArrayGas aw fp numQ

def uMemory (mem : ByteArray) (fp m : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize (m + 1))) fp (m + 1)

def uWords (aw : UInt256) (fp m : Nat) : UInt256 :=
  newWordArrayWords aw fp (m + 1)

def uAllocationGas (aw : UInt256) (fp m : Nat) : Nat :=
  79 + newWordArrayGas aw fp (m + 1)

def copiedUMemory (mem : ByteArray) (fp dividend m : Nat) : ByteArray :=
  mem.write (dividend + 32) mem (fp + 32) (32 * m)

def copiedUWords (aw : UInt256) (fp dividend m : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.M aw.toNat (max (fp + 32) (dividend + 32)) (32 * m))

def copyUExpansionGas (aw : UInt256) (fp dividend m : Nat) : Nat :=
  Cₘ (copiedUWords aw fp dividend m) - Cₘ aw

def copyUGas (aw : UInt256) (fp dividend m : Nat) : Nat :=
  copyUExpansionGas aw fp dividend m +
    GasConstants.Gverylow + GasConstants.Gcopy * m

private theorem copyUGasSum (m expansion : Nat) :
    3 + (3 + (3 + (3 + (3 + (3 * m + (8 + (31 + (45 + expansion)))))))) =
      3 * m + (99 + expansion) := by
  omega

/-- Exact successful path through the compiler's checked `x - 1` helper. -/
theorem checkedSubOneExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x ret : Nat} {tail : List UInt256}
    (hxPos : 0 < x)
    (hx : x < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1023⟩
      (UInt256.ofNat x :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x - 1) :: tail) mem aw rdata acc (k + 12) (C + 45) := by
  have hxPred : x - 1 < UInt256.size := by omega
  have hsub : UInt256.ofNat x + (⟨0⟩ : UInt256).lnot = UInt256.ofNat (x - 1) := by
    rw [show x = (x - 1) + 1 by omega, u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat ((x - 1) + 1)) =
      UInt256.ofNat (x - 1)
    exact MultiLimbOddCompare.scanIndex_ofNat_succ (x - 1) (by omega)
  have hcondition : UInt256.gt (UInt256.ofNat (x - 1)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxPred, UInt256.toNat_ofNat_of_lt hx]
    omega
  have rd1036 := GeneratedTraces.trace_1023_notTaken
    (by omega) h (by native_decide) (by
      simpa [hsub] using hcondition)
  rw [hsub] at rd1036
  have rdret := GeneratedTraces.trace_1036_jump
    (by simp only [List.length_cons]; omega) rd1036
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 12) (C' := C + 45) (by omega) (by omega)
  simpa using normalized

/-- Exact successful path through the compiler's checked subtraction helper. -/
theorem checkedSubExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x y ret : Nat} {tail : List UInt256}
    (hyx : y ≤ x)
    (hx : x < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1103⟩
      (UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x - y) :: tail) mem aw rdata acc (k + 11) (C + 43) := by
  have hy : y < UInt256.size := by omega
  have hxy : x - y < UInt256.size := by omega
  have hsub : UInt256.sub (UInt256.ofNat x) (UInt256.ofNat y) =
      UInt256.ofNat (x - y) := by
    apply u256_inj
    rw [usub_toNat]
    · rw [UInt256.toNat_ofNat_of_lt hx, UInt256.toNat_ofNat_of_lt hy,
        UInt256.toNat_ofNat_of_lt hxy]
    · rw [UInt256.toNat_ofNat_of_lt hx, UInt256.toNat_ofNat_of_lt hy]
      exact hyx
  have hcondition : UInt256.gt (UInt256.ofNat (x - y)) (UInt256.ofNat x) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxy, UInt256.toNat_ofNat_of_lt hx]
    omega
  have rd1115 := GeneratedTraces.trace_1103_notTaken
    (by omega) h (by native_decide) (by
      simpa [hsub] using hcondition)
  rw [hsub] at rd1115
  have rdret := GeneratedTraces.trace_1115_jump
    (by simp only [List.length_cons]; omega) rd1115
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 11) (C' := C + 43) (by omega) (by omega)
  simpa using normalized

/-- Exact successful path through the compiler's checked `x + 1` helper. -/
theorem checkedAddOneExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C x ret : Nat} {tail : List UInt256}
    (hx : x + 1 < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1323⟩
      (UInt256.ofNat x :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x + 1) :: tail) mem aw rdata acc (k + 11) (C + 43) := by
  have hxWord : x < UInt256.size := by omega
  have hadd : UInt256.ofNat x + ⟨1⟩ = UInt256.ofNat (x + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hxWord,
      UInt256.toNat_ofNat_of_lt hx]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
    rw [Nat.mod_eq_of_lt hx]
  have hcondition : UInt256.gt (UInt256.ofNat x) (UInt256.ofNat (x + 1)) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hxWord, UInt256.toNat_ofNat_of_lt hx]
    omega
  have rd1336 := GeneratedTraces.trace_1323_notTaken
    (by omega) h (by native_decide) (by
      simpa [hadd] using hcondition)
  rw [hadd] at rd1336
  have rdret := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336
    (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 11) (C' := C + 43) (by omega) (by omega)
  simpa using normalized

/-- Compute the exact quotient-array length `m - kEff + 1`. -/
theorem quotientLengthExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m kEff : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hkEff : kEff ≤ m)
    (hm : m < UInt256.size)
    (hnumQ : m - kEff + 1 < UInt256.size)
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5287⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5304⟩
      (UInt256.ofNat (m - kEff + 1) :: UInt256.ofNat kEff :: UInt256.ofNat m ::
        rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc (k + 31) (C + 121) := by
  have rd1103 := evm_run h with [
    pushCanonical 2 .PUSH2 ⟨0x14b8⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨0x14b3⟩ (by decide),
    dup3,
    dup5,
    pushCanonical 2 .PUSH2 ⟨0x44f⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5299 := checkedSubExact hkEff hm (by native_decide)
    (by simp only [List.length_cons]; omega) rd1103
  have rd1323 := evm_run rd5299 with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨0x52b⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5304 := checkedAddOneExact hnumQ (by native_decide)
    (by simp only [List.length_cons]; omega) rd1323
  have normalized := rd5304.withIndices
    (k' := k + 31) (C' := C + 121) (by omega) (by omega)
  simpa using normalized

/-- Allocate the exact `numQlimbs`-word quotient array. -/
theorem quotientAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp numQ kEff m : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hnumQ : numQ ≤ 65)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize numQ < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1007)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5304⟩
      (UInt256.ofNat numQ :: UInt256.ofNat kEff :: UInt256.ofNat m :: rem ::
        dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5314⟩
      (UInt256.ofNat fp :: ret :: UInt256.ofNat kEff :: UInt256.ofNat m :: rem ::
        dividend :: UInt256.ofNat numQ :: divisor :: tail)
      (quotientMemory mem fp numQ) (quotientWords aw fp numQ) rdata acc
      (k + 84) (C + quotientAllocationGas aw fp numQ) := by
  have rd1487 := evm_run h with [
    jumpdest,
    swap5,
    pushCanonical 2 .PUSH2 ⟨0x14c2⟩ (by decide),
    dup7,
    pushCanonical 2 .PUSH2 ⟨0x5cf⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5314 := newWordArrayExact68 (by omega) hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd5314.withIndices
    (k' := k + 84) (C' := C + quotientAllocationGas aw fp numQ)
    (by omega) (by simp [quotientAllocationGas]; omega)
  simpa only [quotientMemory, quotientWords] using normalized

/-- Compute `numQlimbs` and allocate the quotient in one exact setup contract. -/
theorem throughQuotientAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m kEff : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hkEff : kEff ≤ m)
    (hm : m < UInt256.size)
    (hnumQWord : m - kEff + 1 < UInt256.size)
    (hnumQ : m - kEff + 1 ≤ 65)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (m - kEff + 1) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1007)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5287⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    let numQ := m - kEff + 1
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5314⟩
      (UInt256.ofNat fp :: ret :: UInt256.ofNat kEff :: UInt256.ofNat m :: rem ::
        dividend :: UInt256.ofNat numQ :: divisor :: tail)
      (quotientMemory mem fp numQ) (quotientWords aw fp numQ) rdata acc
      (k + 115) (C + 121 + quotientAllocationGas aw fp numQ) := by
  have rd5304 := quotientLengthExact hkEff hm hnumQWord (by omega) h
  have rd5314 := quotientAllocationExact hnumQ hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata htail rd5304
  have normalized := rd5314.withIndices
    (k' := k + 115)
    (C' := C + 121 + quotientAllocationGas aw fp (m - kEff + 1))
    (by omega) (by omega)
  simpa using normalized

/-- Compute `m + 1` and allocate the normalized-dividend workspace `u`. -/
theorem uAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m kEff numQ : Nat} {tail : List UInt256}
    {quotient rem dividend ret divisor : UInt256}
    (hmWord : m + 1 < UInt256.size)
    (hmCount : m + 1 ≤ 66)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1004)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5314⟩
      (quotient :: ret :: UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend ::
        UInt256.ofNat numQ :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5327⟩
      (UInt256.ofNat fp :: rem :: ret :: UInt256.ofNat kEff :: UInt256.ofNat m ::
        quotient :: dividend :: UInt256.ofNat numQ :: divisor :: tail)
      (uMemory mem fp m) (uWords aw fp m) rdata acc
      (k + 99) (C + uAllocationGas aw fp m) := by
  have rd1323 := evm_run h with [
    jumpdest,
    swap4,
    pushCanonical 2 .PUSH2 ⟨0x14cf⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨0x13a7⟩ (by decide),
    dup6,
    pushCanonical 2 .PUSH2 ⟨0x52b⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5031 := checkedAddOneExact hmWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1323
  have rd1487 := evm_run rd5031 with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨0x5cf⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5327 := newWordArrayExact68 (by omega) hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd5327.withIndices
    (k' := k + 99) (C' := C + uAllocationGas aw fp m)
    (by omega) (by simp [uAllocationGas]; omega)
  simpa only [uMemory, uWords] using normalized

/-- Copy all dividend limbs into `u` and compute the top-divisor index `kEff - 1`. -/
theorem copyUAndTopIndexExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp dividend m kEff numQ ret : Nat} {tail : List UInt256}
    {quotient rem divisor : UInt256}
    (hkEffPos : 0 < kEff)
    (hkEffWord : kEff < UInt256.size)
    (hmBytes : 32 * m < UInt256.size)
    (hfp32 : fp + 32 < UInt256.size)
    (hdividend32 : dividend + 32 < UInt256.size)
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5327⟩
      (UInt256.ofNat fp :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff ::
        UInt256.ofNat m :: quotient :: UInt256.ofNat dividend :: UInt256.ofNat numQ ::
        divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5356⟩
      (UInt256.ofNat (kEff - 1) :: ⟨5362⟩ :: ⟨5368⟩ :: rem :: UInt256.ofNat ret ::
        UInt256.ofNat kEff :: UInt256.ofNat m :: quotient :: UInt256.ofNat fp ::
        UInt256.ofNat numQ :: divisor :: tail)
      (copiedUMemory mem fp dividend m) (copiedUWords aw fp dividend m)
      rdata acc (k + 30) (C + 99 + copyUGas aw fp dividend m) := by
  have hshift : UInt256.shiftLeft (UInt256.ofNat m) ⟨5⟩ =
      UInt256.ofNat (32 * m) := shiftLeft5_ofNat_eq hmBytes
  have hsrc : UInt256.ofNat dividend + ⟨32⟩ = UInt256.ofNat (dividend + 32) :=
    ofNat_add_bounded hdividend32
  have hdst : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) :=
    ofNat_add_bounded hfp32
  have hlenNat : (UInt256.ofNat (32 * m)).toNat = 32 * m :=
    UInt256.toNat_ofNat_of_lt hmBytes
  have hcopyWords' : (31 + 32 * m) / 32 = m := by omega
  have hsrcNat : (UInt256.ofNat (dividend + 32)).toNat = dividend + 32 :=
    UInt256.toNat_ofNat_of_lt hdividend32
  have hdstNat : (UInt256.ofNat (fp + 32)).toNat = fp + 32 :=
    UInt256.toNat_ofNat_of_lt hfp32
  have rd5341 := evm_run h with [
    jumpdest,
    swap6,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup6,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    swap2,
    add,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup9,
    add
  ]
  rw [hshift, hsrc, hdst] at rd5341
  have rd5342 := RDx.mcopy
    (copyUExpansionGas aw fp dividend m)
    (copiedUMemory mem fp dividend m)
    (copiedUWords aw fp dividend m) rd5341 (by native_decide)
    (by
      intro s hsaw hstk
      simp [copyUExpansionGas, copiedUWords, memoryExpansionCost,
        memoryExpansionCost.μᵢ', hsaw, hstk, hsrcNat, hdstNat, hlenNat])
    (by simp [copiedUMemory, hsrcNat, hdstNat, hlenNat])
    (by simp [copiedUWords, hsrcNat, hdstNat, hlenNat])
    (by simp only [List.length_cons]; omega)
  have rd1023 := evm_run rd5342 with [
    pushCanonical 2 .PUSH2 ⟨5368⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨5362⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨5356⟩ (by decide),
    dup6,
    pushCanonical 2 .PUSH2 ⟨1023⟩ (by decide),
    jump (by native_decide)
  ]
  have rd5356 := checkedSubOneExact hkEffPos hkEffWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1023
  have normalized := rd5356.withIndices
    (k' := k + 30) (C' := C + 99 + copyUGas aw fp dividend m)
    (by omega) (by
      simp [copyUGas, GasConstants.Gverylow, GasConstants.Gcopy, hlenNat, hcopyWords',
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      exact copyUGasSum m (copyUExpansionGas aw fp dividend m))
  simpa using normalized

/-- Bounds-check `divisor[kEff - 1]` and compute its payload address. -/
theorem topDivisorAddressExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m kEff numQ ret : Nat} {tail : List UInt256}
    {quotient rem divisor : UInt256}
    (hkEffPos : 0 < kEff)
    (hkEffWord : kEff < UInt256.size)
    (hdivHeader : MultiLimbOddCompare.headerWord mem aw divisor = UInt256.ofNat kEff)
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode ee g s0 ⟨5356⟩
      (UInt256.ofNat (kEff - 1) :: ⟨5362⟩ :: ⟨5368⟩ :: rem :: UInt256.ofNat ret ::
        UInt256.ofNat kEff :: UInt256.ofNat m :: quotient :: UInt256.ofNat fp ::
        UInt256.ofNat numQ :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5362⟩
      (MultiLimbOddCompare.elementPtr divisor (UInt256.ofNat (kEff - 1)) :: ⟨5368⟩ ::
        rem :: UInt256.ofNat ret :: UInt256.ofNat kEff :: UInt256.ofNat m :: quotient ::
        UInt256.ofNat fp :: UInt256.ofNat numQ :: divisor :: tail)
      mem (MultiLimbOddCompare.afterHeader aw divisor) rdata acc
      (k + 20) (C + 73 +
        (Cₘ (MultiLimbOddCompare.afterHeader aw divisor) - Cₘ aw)) := by
  have hpredWord : kEff - 1 < UInt256.size := by omega
  have hbound : (UInt256.ofNat (kEff - 1)).toNat <
      (MultiLimbOddCompare.headerWord mem aw divisor).toNat := by
    rw [hdivHeader, UInt256.toNat_ofNat_of_lt hpredWord,
      UInt256.toNat_ofNat_of_lt hkEffWord]
    omega
  have hguard : ((UInt256.ofNat (kEff - 1)).lt
      (MultiLimbOddCompare.headerWord mem aw divisor)).isZero = ⟨0⟩ := by
    rw [ult_one hbound]
    native_decide
  have rd1538 := GeneratedTraces.trace_5356_body
    (by omega) h
  have hguardRaw :
      ((UInt256.ofNat (kEff - 1)).lt
        (if divisor.toNat ≥ mem.size ∨ divisor ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding divisor.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hguard
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd1548 := GeneratedTraces.trace_1539_body
    (by simp only [List.length_cons]; omega) rd1539
  have rd5362 := rd1548.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  rw [← MultiLimbOddCompare.afterHeader_generated] at rd5362
  have normalized := rd5362.withIndices
    (k' := k + 20)
    (C' := C + 73 +
      (Cₘ (MultiLimbOddCompare.afterHeader aw divisor) - Cₘ aw))
    (by omega) (by omega)
  simpa only [MultiLimbOddCompare.elementPtr] using normalized

end Modexp.MultiLimbSchoolbookKnuthSetup
