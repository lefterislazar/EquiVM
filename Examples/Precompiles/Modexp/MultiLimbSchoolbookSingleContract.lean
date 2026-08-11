import Examples.Precompiles.Modexp.MultiLimbDiv512Contract
import Examples.Precompiles.Modexp.LimbModel

/-!
# Single-limb `schoolbookDiv` loop

The specialized branch scans the dividend from its most-significant limb, calls the exact
`div512by256` helper, and stores one quotient limb per iteration.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookSingle

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arrayHeader (mem : ByteArray) (aw array : UInt256) : UInt256 :=
  MultiLimbSchoolbookShort.arrayHeader mem aw array

def arrayAfterHeader (aw array : UInt256) : UInt256 :=
  MultiLimbSchoolbookShort.arrayAfterHeader aw array

def arrayAddress (array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookShort.arrayAddress array index

def arrayWord (mem : ByteArray) (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookShort.arrayWord mem aw array index

def arrayAfterWord (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbSchoolbookShort.arrayAfterWord aw array index

def storeQuotient
    (mem : ByteArray) (quotient : UInt256) (index : Nat) (value : UInt256) : ByteArray :=
  value.toByteArray.write 0 mem (arrayAddress quotient index).toNat 32

def stepRemainder (remainder value d : UInt256) : UInt256 :=
  if remainder = ⟨0⟩ then UInt256.mod value d
  else MultiLimbDiv512.nonzeroRemainder remainder value d

def stepQuotient (remainder value d : UInt256) : UInt256 :=
  if remainder = ⟨0⟩ then UInt256.div value d
  else MultiLimbDiv512.nonzeroQuotient remainder value d

def cycleSteps (remainder : UInt256) : Nat :=
  if remainder = ⟨0⟩ then 102 else 179

def cycleGas (remainder : UInt256) : Nat :=
  if remainder = ⟨0⟩ then 352 else 627

def allocatedMemory (mem : ByteArray) (fp m : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize m)) fp m

def allocatedWords (aw : UInt256) (fp m : Nat) : UInt256 :=
  newWordArrayWords aw fp m

def allocationGas (aw : UInt256) (fp m : Nat) : Nat :=
  93 + newWordArrayGas aw fp m

theorem arrayAddress_zero_comm (array : UInt256) :
    (⟨32⟩ : UInt256) + array = arrayAddress array 0 := by
  unfold arrayAddress MultiLimbSchoolbookShort.arrayAddress
    MultiLimbOddCompare.elementPtr
  rw [show UInt256.ofNat 0 = ⟨0⟩ by native_decide,
    show (⟨0⟩ : UInt256).shiftLeft ⟨5⟩ = ⟨0⟩ by native_decide,
    u256_zero_add, u256_add_comm]

theorem stepRemainder_toNat (remainder value d : UInt256)
    (hd : 1 < d.toNat) :
    (stepRemainder remainder value d).toNat =
      (remainder.toNat * UInt256.size + value.toNat) % d.toNat := by
  by_cases hz : remainder = ⟨0⟩
  · subst remainder
    simp only [stepRemainder]
    simp only [ite_true]
    rw [umod_toNat (by omega : d.toNat ≠ 0)]
    simp
  · rw [stepRemainder, if_neg hz,
      MultiLimbDiv512.nonzeroRemainder_toNat remainder value d hd]
    rfl

theorem stepQuotient_toNat (remainder value d : UInt256)
    (hd : 1 < d.toNat) (hremainder : remainder.toNat < d.toNat) :
    (stepQuotient remainder value d).toNat =
      (remainder.toNat * UInt256.size + value.toNat) / d.toNat := by
  by_cases hz : remainder = ⟨0⟩
  · subst remainder
    simp only [stepQuotient]
    simp only [ite_true]
    rw [udiv_toNat]
    simp
  · rw [stepQuotient, if_neg hz,
      MultiLimbDiv512.nonzeroQuotient_toNat remainder value d hz hd hremainder]
    rfl

def divideLimbs : List UInt256 → UInt256 → List UInt256 × UInt256
  | [], _ => ([], ⟨0⟩)
  | limb :: limbs, d =>
      let high := divideLimbs limbs d
      (stepQuotient high.2 limb d :: high.1, stepRemainder high.2 limb d)

/-- The same pure division recurrence with an explicit incoming high remainder. -/
def divideLimbsFrom : List UInt256 → UInt256 → UInt256 → List UInt256 × UInt256
  | [], _, remainder => ([], remainder)
  | limb :: limbs, d, remainder =>
      let high := divideLimbsFrom limbs d remainder
      (stepQuotient high.2 limb d :: high.1, stepRemainder high.2 limb d)

/-- Low-to-high words read from the first `n` array positions. -/
def arrayWords (mem : ByteArray) (aw array : UInt256) : Nat → List UInt256
  | 0 => []
  | n + 1 => arrayWords mem aw array n ++ [arrayWord mem aw array n]

def arrayWordsFrom (values : Nat → UInt256) : Nat → List UInt256
  | 0 => []
  | n + 1 => arrayWordsFrom values n ++ [values n]

/-- Pure recurrence in the exact high-to-low order used by the bytecode loop. -/
def descendPure (values : Nat → UInt256) (d : UInt256) :
    Nat → UInt256 → List UInt256 × UInt256
  | 0, remainder => ([], remainder)
  | n + 1, remainder =>
      let value := values n
      let quotient := stepQuotient remainder value d
      let nextRemainder := stepRemainder remainder value d
      let rest := descendPure values d n nextRemainder
      (rest.1 ++ [quotient], rest.2)

theorem divideLimbsFrom_append_single
    (limbs : List UInt256) (last d remainder : UInt256) :
    divideLimbsFrom (limbs ++ [last]) d remainder =
      let topQuotient := stepQuotient remainder last d
      let topRemainder := stepRemainder remainder last d
      let rest := divideLimbsFrom limbs d topRemainder
      (rest.1 ++ [topQuotient], rest.2) := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [List.cons_append, divideLimbsFrom]
      rw [ih]

theorem descendPure_eq_divideLimbsFrom
    (values : Nat → UInt256) (d remainder : UInt256) (n : Nat) :
    descendPure values d n remainder =
      divideLimbsFrom
        (arrayWordsFrom values n) d remainder := by
  induction n generalizing remainder with
  | zero => rfl
  | succ n ih =>
      rw [show arrayWordsFrom values (n + 1) =
        arrayWordsFrom values n ++ [values n] by
          simp [arrayWordsFrom]]
      rw [divideLimbsFrom_append_single]
      simp only [descendPure]
      rw [ih]

theorem divideLimbs_eq_divideLimbsFrom (limbs : List UInt256) (d : UInt256) :
    divideLimbs limbs d = divideLimbsFrom limbs d ⟨0⟩ := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [divideLimbs, divideLimbsFrom]
      rw [ih]

theorem arrayWords_eq_arrayWordsFrom
    (mem : ByteArray) (aw array : UInt256) (n : Nat) :
    arrayWords mem aw array n = arrayWordsFrom (fun i => arrayWord mem aw array i) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arrayWords, arrayWordsFrom, ih]

theorem descendPure_zero_eq_divideLimbs
    (values : Nat → UInt256) (d : UInt256) (n : Nat) :
    descendPure values d n ⟨0⟩ = divideLimbs (arrayWordsFrom values n) d := by
  rw [descendPure_eq_divideLimbsFrom, divideLimbs_eq_divideLimbsFrom]

theorem descendPure_congr
    (left right : Nat → UInt256) (d remainder : UInt256) (n : Nat)
    (heq : ∀ i, i < n → left i = right i) :
    descendPure left d n remainder = descendPure right d n remainder := by
  induction n generalizing remainder with
  | zero => rfl
  | succ n ih =>
      simp only [descendPure]
      rw [heq n (by omega)]
      rw [ih (stepRemainder remainder (right n) d)
        (fun i hi => heq i (by omega))]

@[simp] theorem divideLimbs_length (limbs : List UInt256) (d : UInt256) :
    (divideLimbs limbs d).1.length = limbs.length := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp [divideLimbs, ih]

theorem divideLimbs_remainder_lt (limbs : List UInt256) (d : UInt256)
    (hd : 1 < d.toNat) :
    (divideLimbs limbs d).2.toNat < d.toNat := by
  induction limbs with
  | nil =>
      change 0 < d.toNat
      omega
  | cons limb limbs ih =>
      simp only [divideLimbs]
      rw [stepRemainder_toNat _ _ _ hd]
      exact Nat.mod_lt _ (by omega)

theorem divideLimbs_value (limbs : List UInt256) (d : UInt256)
    (hd : 1 < d.toNat) :
    Modexp.limbsToNatAt UInt256.size (limbs.map UInt256.toNat) =
      d.toNat * Modexp.limbsToNatAt UInt256.size
        ((divideLimbs limbs d).1.map UInt256.toNat) +
      (divideLimbs limbs d).2.toNat := by
  induction limbs with
  | nil => simp [divideLimbs, Modexp.limbsToNatAt]
  | cons limb limbs ih =>
      have hhigh : (divideLimbs limbs d).2.toNat < d.toNat :=
        divideLimbs_remainder_lt limbs d hd
      have hq := stepQuotient_toNat (divideLimbs limbs d).2 limb d hd hhigh
      have hr := stepRemainder_toNat (divideLimbs limbs d).2 limb d hd
      have hsplit := Nat.mod_add_div
        ((divideLimbs limbs d).2.toNat * UInt256.size + limb.toNat) d.toNat
      simp only [divideLimbs, List.map_cons, Modexp.limbsToNatAt]
      change limb.toNat + UInt256.size *
          Modexp.limbsToNatAt UInt256.size (limbs.map UInt256.toNat) =
        d.toNat *
            ((stepQuotient (divideLimbs limbs d).2 limb d).toNat +
              UInt256.size * Modexp.limbsToNatAt UInt256.size
                ((divideLimbs limbs d).1.map UInt256.toNat)) +
          (stepRemainder (divideLimbs limbs d).2 limb d).toNat
      rw [ih, hq, hr]
      ring_nf at hsplit ⊢
      omega

theorem divideLimbs_quotient (limbs : List UInt256) (d : UInt256)
    (hd : 1 < d.toNat) :
    Modexp.limbsToNatAt UInt256.size
        ((divideLimbs limbs d).1.map UInt256.toNat) =
      Modexp.limbsToNatAt UInt256.size (limbs.map UInt256.toNat) / d.toNat := by
  let q := Modexp.limbsToNatAt UInt256.size
    ((divideLimbs limbs d).1.map UInt256.toNat)
  let r := (divideLimbs limbs d).2.toNat
  have hvalue := divideLimbs_value limbs d hd
  have hr := divideLimbs_remainder_lt limbs d hd
  rw [hvalue, Nat.add_comm,
    Nat.add_mul_div_left _ _ (by omega : 0 < d.toNat),
    Nat.div_eq_of_lt hr, Nat.zero_add]

theorem divideLimbs_remainder (limbs : List UInt256) (d : UInt256)
    (hd : 1 < d.toNat) :
    (divideLimbs limbs d).2.toNat =
      Modexp.limbsToNatAt UInt256.size (limbs.map UInt256.toNat) % d.toNat := by
  let q := Modexp.limbsToNatAt UInt256.size
    ((divideLimbs limbs d).1.map UInt256.toNat)
  let r := (divideLimbs limbs d).2.toNat
  have hvalue := divideLimbs_value limbs d hd
  have hr := divideLimbs_remainder_lt limbs d hd
  rw [hvalue, Nat.add_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hr]

/-- Load the single divisor limb and allocate the `m`-limb quotient. -/
theorem allocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m divisorCount : Nat} {tail : List UInt256}
    {rem dividend ret divisor d : UInt256}
    (hm : 0 < m)
    (hmCount : m ≤ 32)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize m < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1008)
    (hdivisorCount : 0 < divisorCount)
    (hdivisorCountBound : divisorCount ≤ 32)
    (hdivisorHeader : arrayHeader mem aw divisor = UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : arrayAfterHeader aw divisor = aw)
    (hdivisorElementAw : arrayAfterWord aw divisor 0 = aw)
    (hdivisorWord : arrayWord mem aw divisor 0 = d)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6274⟩
      (⟨1⟩ :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6298⟩
      (UInt256.ofNat fp :: UInt256.ofNat m :: dividend :: d :: ret :: rem :: tail)
      (allocatedMemory mem fp m) (allocatedWords aw fp m) rdata acc
      (k + 104) (C + allocationGas aw fp m) := by
  have hcountSmall : divisorCount < UInt256.size := by
    exact lt_trans (by omega : divisorCount < 33) (by decide)
  have hheaderNe : UInt256.ofNat divisorCount ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    rw [UInt256.toNat_ofNat_of_lt hcountSmall] at hnat
    norm_num at hnat
    omega
  have hcondition :
      (MultiLimbOddCompare.headerWord mem aw divisor).isZero = ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw divisor =
      UInt256.ofNat divisorCount from hdivisorHeader]
    exact isZero_eq_zero_of_ne hheaderNe
  have rd1524 := GeneratedTraces.trace_6274_notTaken
    (by omega) h (by native_decide) hcondition
  have hheaderAwRaw : MultiLimbOddCompare.afterHeader aw divisor = aw :=
    hdivisorHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hheaderAwRaw] at rd1524
  have rd6294raw := GeneratedTraces.trace_1524_jump
    (by simp only [List.length_cons]; omega) rd1524
    (by native_decide) (by native_decide)
  rw [arrayAddress_zero_comm divisor] at rd6294raw
  have rd1487 := evm_run rd6294raw with [
    jumpdest,
    mloadCanonical,
    swap2,
    pushCanonical 2 .PUSH2 ⟨0x189a⟩ (by decide),
    dup2,
    pushCanonical 2 .PUSH2 ⟨0x5cf⟩ (by decide),
    jump (by native_decide)
  ]
  have hwordRaw :
      MultiLimbOddCompare.headerWord mem aw (arrayAddress divisor 0) = d := by
    simpa only [arrayWord, MultiLimbSchoolbookShort.arrayWord,
      MultiLimbOddCompare.loadedWord] using hdivisorWord
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw (arrayAddress divisor 0) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad] using hdivisorElementAw
  rw [← MultiLimbOddCompare.headerWord_generated, hwordRaw,
    ← MultiLimbOddCompare.afterHeader_generated, helementAwRaw] at rd1487
  have rd6305 := newWordArrayExact hmCount hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd6305.withIndices
    (k' := k + 104) (C' := C + allocationGas aw fp m)
    (by omega) (by simp [allocationGas]; omega)
  simpa only [allocatedMemory, allocatedWords] using normalized

/-- Initialize `remainder = 0`, `i = m`, and enter the first loop body. -/
theorem setupLoop
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m : Nat} {tail : List UInt256}
    {quotient dividend d ret rem : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (hm : 0 < m)
    (hmBound : m < UInt256.size)
    (h : RDx runtimeBytecode ee g s0 ⟨6298⟩
      (quotient :: UInt256.ofNat m :: dividend :: d :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6326⟩
      (dividend :: d :: ⟨0⟩ :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc (k + 9) (C + 29) := by
  have hmNe : UInt256.ofNat m ≠ ⟨0⟩ := by
    intro hzero
    have := congrArg UInt256.toNat hzero
    rw [UInt256.toNat_ofNat_of_lt hmBound] at this
    norm_num at this
    omega
  have rd6333 := GeneratedTraces.trace_6298_taken
    (tail := ret :: rem :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hmNe (by native_decide)
  have normalized := rd6333.withIndices
    (k' := k + 9) (C' := C + 29) (by omega) (by omega)
  simpa using normalized

/-- One loop iteration whose incoming high word is zero. -/
theorem zeroCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i m dividendCount quotientCount : Nat} {tail : List UInt256}
    {dividend d quotient ret rem value : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hi : i < m)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hd : 1 < d.toNat)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : arrayAfterWord aw dividend i = aw)
    (hvalue : arrayWord mem aw dividend i = value)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hquotElementAw : arrayAfterWord aw quotient i = aw)
    (hret : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6326⟩
      (dividend :: d :: ⟨0⟩ :: UInt256.ofNat (i + 1) :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6304⟩
      (UInt256.ofNat i :: dividend :: d :: UInt256.mod value d :: UInt256.ofNat i ::
        quotient :: ret :: rem :: tail)
      (storeQuotient mem quotient i (UInt256.div value d)) aw rdata acc
      (k + 102) (C + 352) := by
  have hwordLarge : 32 < UInt256.size := by decide
  have hcountSmall : dividendCount < UInt256.size := by omega
  have hquotientSmall : quotientCount < UInt256.size := by omega
  have hiSmall : i < UInt256.size := by omega
  have hindexSmall : i + 1 < UInt256.size := by omega
  have hdec : (UInt256.ofNat (i + 1) + (⟨0⟩ : UInt256).lnot) =
      UInt256.ofNat i := by
    rw [u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (i + 1)) = UInt256.ofNat i
    exact MultiLimbOddCompare.scanIndex_ofNat_succ i hindexSmall
  have hdivBound :
      (UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw dividend) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw dividend =
      UInt256.ofNat dividendCount from hdivHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall,
        UInt256.toNat_ofNat_of_lt hcountSmall]
      omega
  have hdivCondition :
      ((UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw dividend)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hdivBound, Bool.toUInt256]
    native_decide
  have htraceDepth : (quotient :: ret :: rem :: tail).length + 4 ≤ 1016 := by
    simpa only [List.length_cons] using
      (show tail.length + 7 ≤ 1016 by omega)
  have rd1538 := GeneratedTraces.trace_6326_body
    (tail := quotient :: ret :: rem :: tail)
    htraceDepth h
  rw [hdec] at rd1538
  have rd1539 := rd1538.jumpiNT (by native_decide) hdivCondition
    (by simp only [List.length_cons]; omega)
  have hdivHeaderAw' : MultiLimbOddCompare.afterHeader aw dividend = aw :=
    hdivHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hdivHeaderAw'] at rd1539
  have rd6355 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = value := by
    simpa only [arrayWord, MultiLimbSchoolbookShort.arrayWord,
      MultiLimbOddCompare.loadedWord, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvalue
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hdivElementAw
  have rd7905 := (evm_run rd6355 with [
    jumpdest,
    mloadCanonical,
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x1eda⟩ (by decide),
    jump (by native_decide)
  ])
  rw [← MultiLimbOddCompare.headerWord_generated, hvalueRaw,
    ← MultiLimbOddCompare.afterHeader_generated, helementAwRaw] at rd7905
  have rd6362 := MultiLimbDiv512.zeroHighExact
    (by simp only [List.length_cons]; omega) hret rd7905
  have hquotBound :
      (UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw quotient) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw quotient =
      UInt256.ofNat quotientCount from hquotHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall,
        UInt256.toNat_ofNat_of_lt hquotientSmall]
      omega
  have hquotCondition :
      ((UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw quotient)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hquotBound, Bool.toUInt256]
    native_decide
  have rd1539b := GeneratedTraces.trace_6355_notTaken
    (by simp only [List.length_cons]; omega) rd6362 (by native_decide) hquotCondition
  have hquotHeaderAw' : MultiLimbOddCompare.afterHeader aw quotient = aw :=
    hquotHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotHeaderAw'] at rd1539b
  have rd6374 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b (by native_decide) (by native_decide)
  have hquotElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + quotient + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hquotElementAw
  have rd6311 := (evm_run rd6374 with [
    jumpdest,
    mstoreCanonical,
    swap4,
    swap3,
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x18a0⟩ (by decide),
    jump (by native_decide)
  ])
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotElementAwRaw] at rd6311
  have normalized := rd6311.withIndices
    (k' := k + 102) (C' := C + 352) (by omega) (by omega)
  simpa only [storeQuotient, arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

/-- One loop iteration whose incoming high word is nonzero. -/
theorem nonzeroCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i m dividendCount quotientCount : Nat} {tail : List UInt256}
    {dividend d remainder quotient ret rem value : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hi : i < m)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hremNe : remainder ≠ ⟨0⟩)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : arrayAfterWord aw dividend i = aw)
    (hvalue : arrayWord mem aw dividend i = value)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hquotElementAw : arrayAfterWord aw quotient i = aw)
    (hret : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6326⟩
      (dividend :: d :: remainder :: UInt256.ofNat (i + 1) :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6304⟩
      (UInt256.ofNat i :: dividend :: d ::
        MultiLimbDiv512.nonzeroRemainder remainder value d :: UInt256.ofNat i ::
        quotient :: ret :: rem :: tail)
      (storeQuotient mem quotient i
        (MultiLimbDiv512.nonzeroQuotient remainder value d)) aw rdata acc
      (k + 179) (C + 627) := by
  have hwordLarge : 32 < UInt256.size := by decide
  have hcountSmall : dividendCount < UInt256.size := by omega
  have hquotientSmall : quotientCount < UInt256.size := by omega
  have hiSmall : i < UInt256.size := by omega
  have hindexSmall : i + 1 < UInt256.size := by omega
  have hdec : (UInt256.ofNat (i + 1) + (⟨0⟩ : UInt256).lnot) =
      UInt256.ofNat i := by
    rw [u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (i + 1)) = UInt256.ofNat i
    exact MultiLimbOddCompare.scanIndex_ofNat_succ i hindexSmall
  have hdivBound :
      (UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw dividend) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw dividend =
      UInt256.ofNat dividendCount from hdivHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall,
        UInt256.toNat_ofNat_of_lt hcountSmall]
      omega
  have hdivCondition :
      ((UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw dividend)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hdivBound, Bool.toUInt256]
    native_decide
  have htraceDepth : (quotient :: ret :: rem :: tail).length + 4 ≤ 1016 := by
    simpa only [List.length_cons] using
      (show tail.length + 7 ≤ 1016 by omega)
  have rd1538 := GeneratedTraces.trace_6326_body
    (tail := quotient :: ret :: rem :: tail) htraceDepth h
  rw [hdec] at rd1538
  have rd1539 := rd1538.jumpiNT (by native_decide) hdivCondition
    (by simp only [List.length_cons]; omega)
  have hdivHeaderAw' : MultiLimbOddCompare.afterHeader aw dividend = aw :=
    hdivHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hdivHeaderAw'] at rd1539
  have rd6355 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = value := by
    simpa only [arrayWord, MultiLimbSchoolbookShort.arrayWord,
      MultiLimbOddCompare.loadedWord, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hvalue
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hdivElementAw
  have rd7905 := (evm_run rd6355 with [
    jumpdest,
    mloadCanonical,
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x1eda⟩ (by decide),
    jump (by native_decide)
  ])
  rw [← MultiLimbOddCompare.headerWord_generated, hvalueRaw,
    ← MultiLimbOddCompare.afterHeader_generated, helementAwRaw] at rd7905
  have rd6362 := MultiLimbDiv512.nonzeroHighExact
    (by simp only [List.length_cons]; omega) hremNe hret rd7905
  have hquotBound :
      (UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw quotient) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw quotient =
      UInt256.ofNat quotientCount from hquotHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall,
        UInt256.toNat_ofNat_of_lt hquotientSmall]
      omega
  have hquotCondition :
      ((UInt256.ofNat i).lt
        (MultiLimbOddCompare.headerWord mem aw quotient)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hquotBound, Bool.toUInt256]
    native_decide
  have rd1539b := GeneratedTraces.trace_6355_notTaken
    (by simp only [List.length_cons]; omega) rd6362 (by native_decide) hquotCondition
  have hquotHeaderAw' : MultiLimbOddCompare.afterHeader aw quotient = aw :=
    hquotHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotHeaderAw'] at rd1539b
  have rd6374 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b (by native_decide) (by native_decide)
  have hquotElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + quotient + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbSchoolbookShort.arrayAddress, MultiLimbOddCompare.elementPtr] using hquotElementAw
  have rd6311 := (evm_run rd6374 with [
    jumpdest,
    mstoreCanonical,
    swap4,
    swap3,
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x18a0⟩ (by decide),
    jump (by native_decide)
  ])
  rw [← MultiLimbOddCompare.afterHeader_generated, hquotElementAwRaw] at rd6311
  have normalized := rd6311.withIndices
    (k' := k + 179) (C' := C + 627) (by omega) (by omega)
  simpa only [storeQuotient, arrayAddress,
    MultiLimbSchoolbookShort.arrayAddress] using normalized

/-- Path-sensitive exact cycle contract. -/
theorem cycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i m dividendCount quotientCount : Nat} {tail : List UInt256}
    {dividend d remainder quotient ret rem value : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hi : i < m)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hd : 1 < d.toNat)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : arrayAfterWord aw dividend i = aw)
    (hvalue : arrayWord mem aw dividend i = value)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hquotElementAw : arrayAfterWord aw quotient i = aw)
    (hret : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6326⟩
      (dividend :: d :: remainder :: UInt256.ofNat (i + 1) :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6304⟩
      (UInt256.ofNat i :: dividend :: d :: stepRemainder remainder value d ::
        UInt256.ofNat i :: quotient :: ret :: rem :: tail)
      (storeQuotient mem quotient i (stepQuotient remainder value d)) aw rdata acc
      (k + cycleSteps remainder) (C + cycleGas remainder) := by
  by_cases hz : remainder = ⟨0⟩
  · subst remainder
    simpa [stepRemainder, stepQuotient, cycleSteps, cycleGas] using
      zeroCycle hdepth hi hmDividend hmQuotient hdividendCount hquotientCount hd
        hdivHeader hdivHeaderAw hdivElementAw hvalue hquotHeader hquotHeaderAw
        hquotElementAw hret h
  · simpa [stepRemainder, stepQuotient, cycleSteps, cycleGas, hz] using
      nonzeroCycle hdepth hi hmDividend hmQuotient hdividendCount hquotientCount hz
        hdivHeader hdivHeaderAw hdivElementAw hvalue hquotHeader hquotHeaderAw
        hquotElementAw hret h

structure DescendingResult where
  memory : ByteArray
  remainder : UInt256
  steps : Nat
  gas : Nat

/-- Pure operational model of the descending single-limb division loop, including the
three-instruction loop-header branch after every body. -/
def descend
    (aw dividend quotient d : UInt256) : Nat → ByteArray → UInt256 → DescendingResult
  | 0, mem, remainder => ⟨mem, remainder, 0, 0⟩
  | n + 1, mem, remainder =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      let rest := descend aw dividend quotient d n nextMemory nextRemainder
      ⟨rest.memory, rest.remainder,
        cycleSteps remainder + 3 + rest.steps,
        cycleGas remainder + 14 + rest.gas⟩

/-- Array-read and active-memory facts along every evolving-memory state of `descend`. -/
inductive ValidDescending
    (aw dividend quotient d : UInt256) (dividendCount quotientCount : Nat) :
    Nat → ByteArray → UInt256 → Prop
  | zero (mem : ByteArray) (remainder : UInt256) :
      ValidDescending aw dividend quotient d dividendCount quotientCount 0 mem remainder
  | succ (n : Nat) (mem : ByteArray) (remainder : UInt256)
      (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
      (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
      (hdivElementAw : arrayAfterWord aw dividend n = aw)
      (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
      (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
      (hquotElementAw : arrayAfterWord aw quotient n = aw)
      (rest : ValidDescending aw dividend quotient d dividendCount quotientCount n
        (storeQuotient mem quotient n
          (stepQuotient remainder (arrayWord mem aw dividend n) d))
        (stepRemainder remainder (arrayWord mem aw dividend n) d)) :
      ValidDescending aw dividend quotient d dividendCount quotientCount (n + 1)
        mem remainder

/-- An in-bounds quotient-word store does not grow memory. -/
theorem storeQuotient_size_eq
    (mem : ByteArray) (quotient : UInt256) (index : Nat) (value : UInt256)
    (hwrite : (arrayAddress quotient index).toNat + 32 ≤ mem.size) :
    (storeQuotient mem quotient index value).size = mem.size := by
  unfold storeQuotient
  apply toByteArray_write32_size_of_le mem value (arrayAddress quotient index).toNat
    mem.size mem.size rfl
  · omega
  · exact max_eq_left hwrite

/-- A complete header below an in-bounds quotient store is unchanged. -/
theorem arrayHeader_storeQuotient_eq
    (mem : ByteArray) (aw quotient ptr : UInt256) (index : Nat) (value : UInt256)
    (hwrite : (arrayAddress quotient index).toNat + 32 ≤ mem.size)
    (hbelow : ptr.toNat + 32 ≤ (arrayAddress quotient index).toNat) :
    arrayHeader (storeQuotient mem quotient index value) aw ptr =
      arrayHeader mem aw ptr := by
  unfold arrayHeader
  unfold MultiLimbSchoolbookShort.arrayHeader
  unfold MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [storeQuotient_size_eq mem quotient index value hwrite]
  unfold storeQuotient
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size]) (by omega) hbelow]

theorem arrayWord_storeQuotient_eq
    (mem : ByteArray) (aw dividend quotient : UInt256) (sourceIndex storeIndex : Nat)
    (value : UInt256)
    (hwrite : (arrayAddress quotient storeIndex).toNat + 32 ≤ mem.size)
    (hbelow : (arrayAddress dividend sourceIndex).toNat + 32 ≤
      (arrayAddress quotient storeIndex).toNat) :
    arrayWord (storeQuotient mem quotient storeIndex value) aw dividend sourceIndex =
      arrayWord mem aw dividend sourceIndex := by
  unfold arrayWord
  unfold MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
  exact arrayHeader_storeQuotient_eq mem aw quotient (arrayAddress dividend sourceIndex)
    storeIndex value hwrite hbelow

theorem arrayHeader_storeQuotient_eq_above
    (mem : ByteArray) (aw quotient ptr : UInt256) (index : Nat) (value : UInt256)
    (hwrite : (arrayAddress quotient index).toNat + 32 ≤ mem.size)
    (habove : (arrayAddress quotient index).toNat + 32 ≤ ptr.toNat) :
    arrayHeader (storeQuotient mem quotient index value) aw ptr =
      arrayHeader mem aw ptr := by
  unfold arrayHeader
  unfold MultiLimbSchoolbookShort.arrayHeader
  unfold MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [storeQuotient_size_eq mem quotient index value hwrite]
  unfold storeQuotient
  rw [write32_read_above_padded _ _ _ _ (by rw [toByteArray_size]) hwrite habove]

theorem arrayWord_storeQuotient_self
    (mem : ByteArray) (aw quotient value : UInt256) (index : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : (arrayAddress quotient index).toNat + 32 ≤ mem.size)
    (hactive : (arrayAddress quotient index).toNat + 32 ≤ 32 * aw.toNat) :
    arrayWord (storeQuotient mem quotient index value) aw quotient index = value := by
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hnotActive : ¬ arrayAddress quotient index ≥ aw * ⟨32⟩ := by
    intro hge
    have hgeNat : (aw * (⟨32⟩ : UInt256)).toNat ≤
        (arrayAddress quotient index).toNat := hge
    rw [hmul] at hgeNat
    omega
  have hsize := storeQuotient_size_eq mem quotient index value hwrite
  unfold arrayWord
  change MultiLimbOddCompare.loadedWord (storeQuotient mem quotient index value) aw
    (arrayAddress quotient index) = value
  unfold MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [hsize]; omega, hnotActive⟩)]
  unfold storeQuotient
  rw [toByteArray_write32_read_back mem value (arrayAddress quotient index).toNat
    (by omega), fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- Ordinary separated-array layout facts construct the invariant required by every descending
loop state. -/
theorem validDescendingOfLayout
    (aw dividend quotient d : UInt256) (dividendCount quotientCount n : Nat)
    (mem : ByteArray) (remainder : UInt256)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hdivElementAw : ∀ i, i < n → arrayAfterWord aw dividend i = aw)
    (hquotElementAw : ∀ i, i < n → arrayAfterWord aw quotient i = aw)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hdividendBelow : ∀ i, i < n →
      dividend.toNat + 32 ≤ (arrayAddress quotient i).toNat)
    (hquotientBelow : ∀ i, i < n →
      quotient.toNat + 32 ≤ (arrayAddress quotient i).toNat) :
    ValidDescending aw dividend quotient d dividendCount quotientCount n mem remainder := by
  induction n generalizing mem remainder with
  | zero => exact ValidDescending.zero mem remainder
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n
        (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      have hwriteLast := hwrite n (by omega)
      have hnextSize : nextMemory.size = mem.size := by
        exact storeQuotient_size_eq mem quotient n
          (stepQuotient remainder value d) hwriteLast
      apply ValidDescending.succ n mem remainder hdivHeader hdivHeaderAw
        (hdivElementAw n (by omega)) hquotHeader hquotHeaderAw
        (hquotElementAw n (by omega))
      apply ih
      · rw [arrayHeader_storeQuotient_eq mem aw quotient dividend n
          (stepQuotient remainder value d) hwriteLast
          (hdividendBelow n (by omega))]
        exact hdivHeader
      · rw [arrayHeader_storeQuotient_eq mem aw quotient quotient n
          (stepQuotient remainder value d) hwriteLast
          (hquotientBelow n (by omega))]
        exact hquotHeader
      · exact fun i hi => hdivElementAw i (by omega)
      · exact fun i hi => hquotElementAw i (by omega)
      · intro i hi
        rw [hnextSize]
        exact hwrite i (by omega)
      · exact fun i hi => hdividendBelow i (by omega)
      · exact fun i hi => hquotientBelow i (by omega)

/-- In-bounds stores preserve memory size across the complete descending model. -/
theorem descend_size_eq
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (remainder : UInt256)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size) :
    (descend aw dividend quotient d n mem remainder).memory.size = mem.size := by
  induction n generalizing mem remainder with
  | zero => rfl
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n
        (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      have hnextSize : nextMemory.size = mem.size :=
        storeQuotient_size_eq mem quotient n (stepQuotient remainder value d)
          (hwrite n (by omega))
      have hrest := ih nextMemory nextRemainder (fun i hi => by
        rw [hnextSize]
        exact hwrite i (by omega))
      simpa [descend, value, nextMemory, nextRemainder] using hrest.trans hnextSize

/-- A complete word below every quotient destination remains unchanged by the descending model. -/
theorem descend_arrayHeader_eq
    (aw dividend quotient d ptr : UInt256) (n : Nat) (mem : ByteArray)
    (remainder : UInt256)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hbelow : ∀ i, i < n → ptr.toNat + 32 ≤ (arrayAddress quotient i).toNat) :
    arrayHeader (descend aw dividend quotient d n mem remainder).memory aw ptr =
      arrayHeader mem aw ptr := by
  induction n generalizing mem remainder with
  | zero => rfl
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n
        (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      have hnextSize : nextMemory.size = mem.size :=
        storeQuotient_size_eq mem quotient n (stepQuotient remainder value d)
          (hwrite n (by omega))
      have hrest := ih nextMemory nextRemainder
        (fun i hi => by rw [hnextSize]; exact hwrite i (by omega))
        (fun i hi => hbelow i (by omega))
      have hone := arrayHeader_storeQuotient_eq mem aw quotient ptr n
        (stepQuotient remainder value d) (hwrite n (by omega))
        (hbelow n (by omega))
      simpa [descend, value, nextMemory, nextRemainder] using hrest.trans hone

theorem descend_arrayHeader_eq_above
    (aw dividend quotient d ptr : UInt256) (n : Nat) (mem : ByteArray)
    (remainder : UInt256)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (habove : ∀ i, i < n →
      (arrayAddress quotient i).toNat + 32 ≤ ptr.toNat) :
    arrayHeader (descend aw dividend quotient d n mem remainder).memory aw ptr =
      arrayHeader mem aw ptr := by
  induction n generalizing mem remainder with
  | zero => rfl
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n
        (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      have hnextSize : nextMemory.size = mem.size :=
        storeQuotient_size_eq mem quotient n (stepQuotient remainder value d)
          (hwrite n (by omega))
      have hrest := ih nextMemory nextRemainder
        (fun i hi => by rw [hnextSize]; exact hwrite i (by omega))
        (fun i hi => habove i (by omega))
      have hone := arrayHeader_storeQuotient_eq_above mem aw quotient ptr n
        (stepQuotient remainder value d) (hwrite n (by omega))
        (habove n (by omega))
      simpa [descend, value, nextMemory, nextRemainder] using hrest.trans hone

/-- The operational model's remainder is the pure high-to-low recurrence over the initial
dividend words. -/
theorem descend_remainder_eq_pure
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (remainder : UInt256)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat) :
    (descend aw dividend quotient d n mem remainder).remainder =
      (descendPure (fun i => arrayWord mem aw dividend i) d n remainder).2 := by
  induction n generalizing mem remainder with
  | zero => rfl
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let nextMemory := storeQuotient mem quotient n
        (stepQuotient remainder value d)
      let nextRemainder := stepRemainder remainder value d
      have hwriteLast := hwrite n (by omega)
      have hnextSize : nextMemory.size = mem.size :=
        storeQuotient_size_eq mem quotient n (stepQuotient remainder value d)
          hwriteLast
      have hrest := ih nextMemory nextRemainder
        (fun i hi => by rw [hnextSize]; exact hwrite i (by omega))
        (fun i hi j hj => hsourceBelow i (by omega) j (by omega))
      have hvalues := descendPure_congr
        (fun i => arrayWord nextMemory aw dividend i)
        (fun i => arrayWord mem aw dividend i) d nextRemainder n
        (fun i hi => arrayWord_storeQuotient_eq mem aw dividend quotient i n
          (stepQuotient remainder value d) hwriteLast
          (hsourceBelow i (by omega) n (by omega)))
      simp only [descend, descendPure]
      exact hrest.trans (congrArg Prod.snd hvalues)

theorem descend_remainder_eq_divideLimbs
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat) :
    (descend aw dividend quotient d n mem ⟨0⟩).remainder =
      (divideLimbs (arrayWords mem aw dividend n) d).2 := by
  rw [descend_remainder_eq_pure aw dividend quotient d n mem ⟨0⟩ hwrite
    hsourceBelow, descendPure_zero_eq_divideLimbs,
    arrayWords_eq_arrayWordsFrom]

/-- Every final quotient word is the corresponding output of the pure recurrence. -/
theorem descend_arrayWords_eq_pure
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (remainder : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hactive : ∀ i, i < n →
      (arrayAddress quotient i).toNat + 32 ≤ 32 * aw.toNat)
    (horder : ∀ i, i < n → ∀ j, j < n → i < j →
      (arrayAddress quotient i).toNat + 32 ≤ (arrayAddress quotient j).toNat)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat) :
    arrayWords (descend aw dividend quotient d n mem remainder).memory aw quotient n =
      (descendPure (fun i => arrayWord mem aw dividend i) d n remainder).1 := by
  induction n generalizing mem remainder with
  | zero => rfl
  | succ n ih =>
      let value := arrayWord mem aw dividend n
      let topQuotient := stepQuotient remainder value d
      let nextMemory := storeQuotient mem quotient n topQuotient
      let nextRemainder := stepRemainder remainder value d
      have hwriteLast := hwrite n (by omega)
      have hnextSize : nextMemory.size = mem.size :=
        storeQuotient_size_eq mem quotient n topQuotient hwriteLast
      have hlower := ih nextMemory nextRemainder
        (fun i hi => by rw [hnextSize]; exact hwrite i (by omega))
        (fun i hi => hactive i (by omega))
        (fun i hi j hj hij => horder i (by omega) j (by omega) hij)
        (fun i hi j hj => hsourceBelow i (by omega) j (by omega))
      have hvalues := descendPure_congr
        (fun i => arrayWord nextMemory aw dividend i)
        (fun i => arrayWord mem aw dividend i) d nextRemainder n
        (fun i hi => arrayWord_storeQuotient_eq mem aw dividend quotient i n
          topQuotient hwriteLast (hsourceBelow i (by omega) n (by omega)))
      have hlower' := hlower.trans (congrArg Prod.fst hvalues)
      have htopPreserved := descend_arrayHeader_eq_above aw dividend quotient d
        (arrayAddress quotient n) n nextMemory nextRemainder
        (fun i hi => by rw [hnextSize]; exact hwrite i (by omega))
        (fun i hi => horder i (by omega) n (by omega) (by omega))
      have htopStored := arrayWord_storeQuotient_self mem aw quotient topQuotient n
        hawFit hwriteLast (hactive n (by omega))
      have htop :
          arrayWord (descend aw dividend quotient d n nextMemory nextRemainder).memory
              aw quotient n = topQuotient := by
        simpa only [arrayWord, MultiLimbSchoolbookShort.arrayWord,
          MultiLimbOddCompare.loadedWord] using htopPreserved.trans htopStored
      simp only [descend, arrayWords, descendPure]
      rw [hlower', htop]

theorem descend_arrayWords_eq_divideLimbs
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hactive : ∀ i, i < n →
      (arrayAddress quotient i).toNat + 32 ≤ 32 * aw.toNat)
    (horder : ∀ i, i < n → ∀ j, j < n → i < j →
      (arrayAddress quotient i).toNat + 32 ≤ (arrayAddress quotient j).toNat)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat) :
    arrayWords (descend aw dividend quotient d n mem ⟨0⟩).memory aw quotient n =
      (divideLimbs (arrayWords mem aw dividend n) d).1 := by
  rw [descend_arrayWords_eq_pure aw dividend quotient d n mem ⟨0⟩ hawFit
    hwrite hactive horder hsourceBelow,
    descendPure_zero_eq_divideLimbs, arrayWords_eq_arrayWordsFrom]

/-- Exact arithmetic semantics of the complete specialized division loop. -/
theorem descend_exact_div_mod
    (aw dividend quotient d : UInt256) (n : Nat) (mem : ByteArray)
    (hd : 1 < d.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < n → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hactive : ∀ i, i < n →
      (arrayAddress quotient i).toNat + 32 ≤ 32 * aw.toNat)
    (horder : ∀ i, i < n → ∀ j, j < n → i < j →
      (arrayAddress quotient i).toNat + 32 ≤ (arrayAddress quotient j).toNat)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat) :
    let result := descend aw dividend quotient d n mem ⟨0⟩
    Modexp.limbsToNatAt UInt256.size
        ((arrayWords result.memory aw quotient n).map UInt256.toNat) =
        Modexp.limbsToNatAt UInt256.size
          ((arrayWords mem aw dividend n).map UInt256.toNat) / d.toNat ∧
      result.remainder.toNat =
        Modexp.limbsToNatAt UInt256.size
          ((arrayWords mem aw dividend n).map UInt256.toNat) % d.toNat := by
  constructor
  · rw [descend_arrayWords_eq_divideLimbs aw dividend quotient d n mem hawFit
      hwrite hactive horder hsourceBelow]
    exact divideLimbs_quotient (arrayWords mem aw dividend n) d hd
  · rw [descend_remainder_eq_divideLimbs aw dividend quotient d n mem hwrite
      hsourceBelow]
    exact divideLimbs_remainder (arrayWords mem aw dividend n) d hd

/-- Execute every remaining descending iteration and take the final loop-header exit.  The
result and cost are the projections of the same recursive operational model. -/
theorem descendThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n m dividendCount quotientCount : Nat} {tail : List UInt256}
    {dividend d remainder quotient ret rem : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hn : 0 < n)
    (hnm : n ≤ m)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hd : 1 < d.toNat)
    (hvalid : ValidDescending aw dividend quotient d dividendCount quotientCount
      n mem remainder)
    (hret : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6326⟩
      (dividend :: d :: remainder :: UInt256.ofNat n :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    let result := descend aw dividend quotient d n mem remainder
    RDx runtimeBytecode ee g s0 ⟨6309⟩
      (dividend :: d :: result.remainder :: ⟨0⟩ :: quotient :: ret :: rem :: tail)
      result.memory aw rdata acc (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | zero => omega
  | succ i current currentRemainder hdivHeader hdivHeaderAw hdivElementAw
      hquotHeader hquotHeaderAw hquotElementAw rest ih =>
      let value := arrayWord current aw dividend i
      let nextMemory := storeQuotient current quotient i
        (stepQuotient currentRemainder value d)
      let nextRemainder := stepRemainder currentRemainder value d
      have hi : i < m := by omega
      have rdCycle := cycle hdepth hi hmDividend hmQuotient hdividendCount
        hquotientCount hd hdivHeader hdivHeaderAw hdivElementAw rfl hquotHeader
        hquotHeaderAw hquotElementAw hret h
      by_cases hiz : i = 0
      · subst i
        have rdExit := GeneratedTraces.trace_6304_notTaken
          (by simp only [List.length_cons]; omega) rdCycle
          (by native_decide) (by native_decide)
        have normalized := rdExit.withIndices
          (k' := k + (descend aw dividend quotient d 1 current currentRemainder).steps)
          (C' := C + (descend aw dividend quotient d 1 current currentRemainder).gas)
          (by simp [descend]; omega) (by simp [descend]; omega)
        simpa [descend, value, nextMemory, nextRemainder] using normalized
      · have hiSmall : i < UInt256.size := by
          exact lt_trans (by omega : i < 33) (by decide)
        have hiWord : UInt256.ofNat i ≠ ⟨0⟩ := by
          intro hzero
          have hnat := congrArg UInt256.toNat hzero
          rw [UInt256.toNat_ofNat_of_lt hiSmall] at hnat
          norm_num at hnat
          omega
        have rdNext := GeneratedTraces.trace_6304_taken
          (by simp only [List.length_cons]; omega) rdCycle
          (by native_decide) hiWord (by native_decide)
        have rdFinal := ih (by omega) (by omega) rdNext
        have normalized := rdFinal.withIndices
          (k' := k + (descend aw dividend quotient d (i + 1)
            current currentRemainder).steps)
          (C' := C + (descend aw dividend quotient d (i + 1)
            current currentRemainder).gas)
          (by simp [descend, value, nextMemory, nextRemainder]; omega)
          (by simp [descend, value, nextMemory, nextRemainder]; omega)
        simpa [descend, value, nextMemory, nextRemainder] using normalized

/-- Store the final remainder in `rem[0]`, remove the loop locals, and return
`(rem, quotient)` to the caller. -/
theorem storeRemainderAndReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C remCount : Nat} {tail : List UInt256}
    {dividend d remainder quotient ret rem : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hremCount : 0 < remCount)
    (hremCountBound : remCount ≤ 32)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : arrayAfterWord aw rem 0 = aw)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6309⟩
      (dividend :: d :: remainder :: ⟨0⟩ :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (rem :: quotient :: tail)
      (storeQuotient mem rem 0 remainder) aw rdata acc (k + 23) (C + 84) := by
  have hcountSmall : remCount < UInt256.size := by
    exact lt_trans (by omega : remCount < 33) (by decide)
  have hheaderNe : UInt256.ofNat remCount ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    rw [UInt256.toNat_ofNat_of_lt hcountSmall] at hnat
    norm_num at hnat
    omega
  have hcondition :
      (MultiLimbOddCompare.headerWord mem aw rem).isZero = ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw rem = UInt256.ofNat remCount
      from hremHeader]
    exact isZero_eq_zero_of_ne hheaderNe
  have rd1524 := GeneratedTraces.trace_6309_notTaken
    (by omega) h (by native_decide) hcondition
  have hremHeaderAw' : MultiLimbOddCompare.afterHeader aw rem = aw := hremHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hremHeaderAw'] at rd1524
  have rd6328 := GeneratedTraces.trace_1524_jump
    (by simp only [List.length_cons]; omega) rd1524
    (by native_decide) (by native_decide)
  have rdret := GeneratedTraces.trace_6321_jump
    (by omega) rd6328
    (by native_decide) hret
  have hptr : (⟨32⟩ : UInt256) + rem = arrayAddress rem 0 := by
    unfold arrayAddress MultiLimbSchoolbookShort.arrayAddress
      MultiLimbOddCompare.elementPtr
    rw [show UInt256.ofNat 0 = ⟨0⟩ by native_decide,
      show (⟨0⟩ : UInt256).shiftLeft ⟨5⟩ = ⟨0⟩ by native_decide,
      u256_zero_add, u256_add_comm]
  rw [hptr] at rdret
  have hremElementAw' :
      MultiLimbOddCompare.afterHeader aw (arrayAddress rem 0) = aw := by
    simpa only [arrayAfterWord, MultiLimbSchoolbookShort.arrayAfterWord,
      MultiLimbOddCompare.afterLoad] using hremElementAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hremElementAw'] at rdret
  have normalized := rdret.withIndices
    (k' := k + 23) (C' := C + 84) (by omega) (by omega)
  simpa only [storeQuotient] using normalized

/-- Complete the specialized single-limb loop from its setup PC through the internal return. -/
theorem loopThroughReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m dividendCount quotientCount remCount : Nat} {tail : List UInt256}
    {dividend d quotient ret rem : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hm : 0 < m)
    (hmBound : m < UInt256.size)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hd : 1 < d.toNat)
    (hvalid : ValidDescending aw dividend quotient d dividendCount quotientCount
      m mem ⟨0⟩)
    (hremCount : 0 < remCount)
    (hremCountBound : remCount ≤ 32)
    (hremHeader : arrayHeader (descend aw dividend quotient d m mem ⟨0⟩).memory
      aw rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : arrayAfterWord aw rem 0 = aw)
    (hhelperRet : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6298⟩
      (quotient :: UInt256.ofNat m :: dividend :: d :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    let result := descend aw dividend quotient d m mem ⟨0⟩
    RDx runtimeBytecode ee g s0 ret (rem :: quotient :: tail)
      (storeQuotient result.memory rem 0 result.remainder) aw rdata acc
      (k + result.steps + 32) (C + result.gas + 113) := by
  have rd6333 := setupLoop (by omega) hm hmBound h
  have rd6316 := descendThroughExit hdepth hm (by omega : m ≤ m) hmDividend
    hmQuotient hdividendCount hquotientCount hd hvalid hhelperRet rd6333
  have rdret := storeRemainderAndReturn hdepth hremCount hremCountBound hremHeader
    hremHeaderAw hremElementAw hret rd6316
  have normalized := rdret.withIndices
    (k' := k + (descend aw dividend quotient d m mem ⟨0⟩).steps + 32)
    (C' := C + (descend aw dividend quotient d m mem ⟨0⟩).gas + 113)
    (by omega) (by omega)
  simpa using normalized

/-- Complete trace and arithmetic semantics under ordinary separated-array layout facts. -/
theorem loopThroughReturnOfLayout
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m dividendCount quotientCount remCount : Nat} {tail : List UInt256}
    {dividend d quotient ret rem : UInt256}
    (hdepth : tail.length + 8 ≤ 1014)
    (hm : 0 < m)
    (hmBound : m < UInt256.size)
    (hmDividend : m ≤ dividendCount)
    (hmQuotient : m ≤ quotientCount)
    (hdividendCount : dividendCount ≤ 32)
    (hquotientCount : quotientCount ≤ 32)
    (hd : 1 < d.toNat)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat remCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : arrayAfterWord aw rem 0 = aw)
    (hdivElementAw : ∀ i, i < m → arrayAfterWord aw dividend i = aw)
    (hquotElementAw : ∀ i, i < m → arrayAfterWord aw quotient i = aw)
    (hwrite : ∀ i, i < m → (arrayAddress quotient i).toNat + 32 ≤ mem.size)
    (hdividendHeaderBelow : ∀ i, i < m →
      dividend.toNat + 32 ≤ (arrayAddress quotient i).toNat)
    (hquotientHeaderBelow : ∀ i, i < m →
      quotient.toNat + 32 ≤ (arrayAddress quotient i).toNat)
    (hremainderHeaderBelow : ∀ i, i < m →
      rem.toNat + 32 ≤ (arrayAddress quotient i).toNat)
    (hremCount : 0 < remCount)
    (hremCountBound : remCount ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hactive : ∀ i, i < m →
      (arrayAddress quotient i).toNat + 32 ≤ 32 * aw.toNat)
    (horder : ∀ i, i < m → ∀ j, j < m → i < j →
      (arrayAddress quotient i).toNat + 32 ≤ (arrayAddress quotient j).toNat)
    (hsourceBelow : ∀ i, i < m → ∀ j, j < m →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress quotient j).toNat)
    (hhelperRet : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6298⟩
      (quotient :: UInt256.ofNat m :: dividend :: d :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    let result := descend aw dividend quotient d m mem ⟨0⟩
    RDx runtimeBytecode ee g s0 ret (rem :: quotient :: tail)
        (storeQuotient result.memory rem 0 result.remainder) aw rdata acc
        (k + result.steps + 32) (C + result.gas + 113) ∧
      Modexp.limbsToNatAt UInt256.size
          ((arrayWords result.memory aw quotient m).map UInt256.toNat) =
          Modexp.limbsToNatAt UInt256.size
            ((arrayWords mem aw dividend m).map UInt256.toNat) / d.toNat ∧
        result.remainder.toNat =
          Modexp.limbsToNatAt UInt256.size
            ((arrayWords mem aw dividend m).map UInt256.toNat) % d.toNat := by
  have hvalid := validDescendingOfLayout aw dividend quotient d dividendCount
    quotientCount m mem ⟨0⟩ hdivHeader hquotHeader hdivHeaderAw hquotHeaderAw
    hdivElementAw hquotElementAw hwrite hdividendHeaderBelow hquotientHeaderBelow
  have hremFinal :
      arrayHeader (descend aw dividend quotient d m mem ⟨0⟩).memory aw rem =
        UInt256.ofNat remCount := by
    rw [descend_arrayHeader_eq aw dividend quotient d rem m mem ⟨0⟩ hwrite
      hremainderHeaderBelow]
    exact hremHeader
  have rd := loopThroughReturn hdepth hm hmBound hmDividend hmQuotient hdividendCount
    hquotientCount hd hvalid hremCount hremCountBound hremFinal hremHeaderAw
    hremElementAw hhelperRet hret h
  exact ⟨rd, descend_exact_div_mod aw dividend quotient d m mem hd hawFit hwrite
    hactive horder hsourceBelow⟩

/-- Complete the single-limb-divisor branch from dispatch through allocation, every quotient
iteration, the final remainder store, and the internal return. -/
theorem executeThroughReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m dividendCount divisorCount remCount : Nat} {tail : List UInt256}
    {rem dividend ret divisor d : UInt256}
    (hm : 0 < m)
    (hmCount : m ≤ 32)
    (hmDividend : m ≤ dividendCount)
    (hdividendCount : dividendCount ≤ 32)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize m < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1006)
    (hdivisorCount : 0 < divisorCount)
    (hdivisorCountBound : divisorCount ≤ 32)
    (hdivisorHeader : arrayHeader mem aw divisor = UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : arrayAfterHeader aw divisor = aw)
    (hdivisorElementAw : arrayAfterWord aw divisor 0 = aw)
    (hdivisorWord : arrayWord mem aw divisor 0 = d)
    (hd : 1 < d.toNat)
    (hvalid : ValidDescending (allocatedWords aw fp m) dividend (UInt256.ofNat fp) d
      dividendCount m m (allocatedMemory mem fp m) ⟨0⟩)
    (hremCount : 0 < remCount)
    (hremCountBound : remCount ≤ 32)
    (hremHeader :
      arrayHeader
        (descend (allocatedWords aw fp m) dividend (UInt256.ofNat fp) d m
          (allocatedMemory mem fp m) ⟨0⟩).memory
        (allocatedWords aw fp m) rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader (allocatedWords aw fp m) rem =
      allocatedWords aw fp m)
    (hremElementAw : arrayAfterWord (allocatedWords aw fp m) rem 0 =
      allocatedWords aw fp m)
    (hhelperRet : (D_J runtimeBytecode 0).contains ⟨6355⟩ = true)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6274⟩
      (⟨1⟩ :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    let result := descend (allocatedWords aw fp m) dividend (UInt256.ofNat fp) d m
      (allocatedMemory mem fp m) ⟨0⟩
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (rem :: UInt256.ofNat fp :: tail)
      (storeQuotient result.memory rem 0 result.remainder)
      (allocatedWords aw fp m) rdata acc
      (k + result.steps + 136)
      (C + allocationGas aw fp m + result.gas + 113) := by
  have rd6305 := allocationExact hm hmCount hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by omega) hdivisorCount hdivisorCountBound
    hdivisorHeader hdivisorHeaderAw hdivisorElementAw hdivisorWord h
  have hmBound : m < UInt256.size :=
    lt_trans (by omega : m < 33) (by decide)
  have rdret := loopThroughReturn (by omega) hm hmBound hmDividend (by omega : m ≤ m)
    hdividendCount hmCount hd hvalid hremCount hremCountBound hremHeader
    hremHeaderAw hremElementAw hhelperRet hret rd6305
  have normalized := rdret.withIndices
    (k' := k +
      (descend (allocatedWords aw fp m) dividend (UInt256.ofNat fp) d m
        (allocatedMemory mem fp m) ⟨0⟩).steps + 136)
    (C' := C + allocationGas aw fp m +
      (descend (allocatedWords aw fp m) dividend (UInt256.ofNat fp) d m
        (allocatedMemory mem fp m) ⟨0⟩).gas + 113)
    (by omega) (by omega)
  simpa using normalized

end Modexp.MultiLimbSchoolbookSingle
