import Examples.Precompiles.Modexp.MultiLimbExponentTrace
import Examples.Precompiles.Modexp.MultiLimbBackendModel
import Examples.Precompiles.Modexp.WideWordExponentBridge
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSSemantic

/-! # Multi-limb exponent-loop model bridge -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbExponentModel

open Modexp.MultiLimbExponentTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

/-- The unchecked decrement used by the deployed bit loop is ordinary subtraction on every
nonzero loop counter. -/
theorem previousBit_toNat {bit : UInt256} (hbit : bit ≠ ⟨0⟩) :
    (UInt256.lnot ⟨0⟩ + bit).toNat = bit.toNat - 1 := by
  rw [lnotZero_eq_max, uadd_toNat]
  rw [UInt256.toNat_ofNat_of_lt
    (by native_decide : UInt256.size - 1 < UInt256.size)]
  have hpos : 0 < bit.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hbit
    apply u256_inj
    simpa using hz
  have hlt : bit.toNat < UInt256.size := bit.val.isLt
  rw [show UInt256.size - 1 + bit.toNat =
    UInt256.size + (bit.toNat - 1) by omega]
  rw [Nat.add_mod, Nat.mod_self, zero_add]
  have hsub : bit.toNat - 1 < UInt256.size := by omega
  rw [Nat.mod_eq_of_lt hsub, Nat.mod_eq_of_lt hsub]

/-- Set/unset decisions made by a selected deployed bit loop, in execution order. -/
def exponentBitLoopDecisions : ExponentBitLoopSelection → List Bool
  | .done _ _ => []
  | .unset _ rest => false :: exponentBitLoopDecisions rest
  | .set _ _ rest => true :: exponentBitLoopDecisions rest

/-- The mathematical bit selected at a zero-based index. -/
def exponentBitDecision (byte : UInt256) (index : Nat) : Bool :=
  decide (((byte.shiftRight (UInt256.ofNat index)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩)

/-- Descending decisions for bit indices `count - 1, ..., 0`. -/
def exponentBitDecisions (byte : UInt256) : Nat → List Bool
  | 0 => []
  | count + 1 => exponentBitDecision byte count :: exponentBitDecisions byte count

/-- The deployed shift/mask/equality sequence denotes the mathematical bit at `index`. -/
theorem exponentBitDecision_eq_wordBit (byte : UInt256) (index : Nat)
    (hindex : index < 256) :
    exponentBitDecision byte index =
      decide (wordBitNat byte.toNat (index + 1) = 1) := by
  unfold exponentBitDecision
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  calc
    (((byte.shiftRight (UInt256.ofNat index)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩) ↔
      wideBitSet byte index := by
      constructor
      · intro heq hzero
        rw [hzero] at heq
        exact heq (by native_decide)
      · intro hwide
        let x := (byte.shiftRight (UInt256.ofNat index)).land ⟨1⟩
        have hxLt : x.toNat < 2 := by
          unfold x
          rw [uInt256_land_one_toNat]
          exact Nat.mod_lt _ (by decide)
        have hxNe : x.toNat ≠ 0 := by
          intro hz
          apply hwide
          exact uint256_toNat_eq_zero hz
        have hx : x = ⟨1⟩ := by
          apply u256_inj
          simp only [show (⟨1⟩ : UInt256).toNat = 1 by decide]
          omega
        unfold x at hx
        rw [hx, uInt256_eq_self]
        decide
    _ ↔ wordBitNat byte.toNat (index + 1) = 1 :=
      wideBitSet_iff_wordBitNat byte index hindex

theorem exponentBitDecision_toNat (byte : UInt256) (index : Nat)
    (hindex : index < 256) :
    (if exponentBitDecision byte index then 1 else 0) =
      wordBitNat byte.toNat (index + 1) := by
  rw [exponentBitDecision_eq_wordBit byte index hindex]
  by_cases hbit : wordBitNat byte.toNat (index + 1) = 1
  · simp [hbit]
  · have hlt : wordBitNat byte.toNat (index + 1) < 2 := by
      unfold wordBitNat
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      exact Nat.mod_lt _ (by decide)
    have hz : wordBitNat byte.toNat (index + 1) = 0 := by omega
    simp [hz]

/-- Folding the selected descending bits appends exactly those bits to a numeric prefix. -/
theorem exponentBitDecisions_fold (byte : UInt256) (count pfx : Nat)
    (hcount : count ≤ 256) :
    (exponentBitDecisions byte count).foldl
        (fun acc bit => 2 * acc + if bit then 1 else 0) pfx =
      appendWordBits byte.toNat count pfx := by
  induction count generalizing pfx with
  | zero => rfl
  | succ count ih =>
      rw [exponentBitDecisions, List.foldl_cons, appendWordBits,
        exponentBitDecision_toNat byte count (by omega)]
      exact ih _ (by omega)

theorem exponentBitDecisions_toNat (byte : UInt256) (count : Nat)
    (hcount : count ≤ 256) :
    bitsToNatMSB (exponentBitDecisions byte count) =
      appendWordBits byte.toNat count 0 := by
  exact exponentBitDecisions_fold byte count 0 hcount

/-- A valid executable selection contains exactly one decision per remaining loop counter. -/
theorem ExponentBitLoopValid.decisions_length
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte : UInt256} {mem : ByteArray} {aw bit : UInt256}
    {selected : ExponentBitLoopSelection}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected) :
    (exponentBitLoopDecisions selected).length = bit.toNat := by
  induction valid with
  | done => rfl
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      simp only [exponentBitLoopDecisions, List.length_cons]
      rw [ih, previousBit_toNat bitNonzero]
      have hpos : 0 < bit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply bitNonzero
        apply u256_inj
        simpa using hz
      omega
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      simp only [exponentBitLoopDecisions, List.length_cons]
      rw [ih, previousBit_toNat bitNonzero]
      have hpos : 0 < bit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply bitNonzero
        apply u256_inj
        simpa using hz
      omega

/-- The selected set/unset branches are exactly the descending shift-and-mask decisions of the
loaded exponent byte. -/
theorem ExponentBitLoopValid.decisions_eq
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte : UInt256} {mem : ByteArray} {aw bit : UInt256}
    {selected : ExponentBitLoopSelection}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected) :
    exponentBitLoopDecisions selected = exponentBitDecisions byte bit.toNat := by
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
      have hunset :
          ¬ (((byte.shiftRight (UInt256.ofNat previous)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩) := by
        rw [hword]
        exact fun hne => hne bitUnset
      simp only [exponentBitLoopDecisions, hbit, exponentBitDecisions,
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
      have hset :
          ((byte.shiftRight (UInt256.ofNat previous)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩ := by
        rw [hword]
        exact bitSet
      simp only [exponentBitLoopDecisions, hbit, exponentBitDecisions,
        exponentBitDecision, List.cons.injEq]
      constructor
      · simp [hset]
      · simpa [hprevious] using ih

/-- Numeric value stored in the fixed Montgomery result array used by the exponent loop. -/
def exponentMontgomeryValue (wordCount : Nat) (rM : UInt256) (mem : ByteArray) : Nat :=
  Modexp.wordLimbsToNat
    (memoryWordsFrom mem (rM + ⟨32⟩).toNat wordCount)

/-- Once each selected square and multiply satisfies its arithmetic contract, the complete
selected bit loop is exactly the backend-independent MSB-first power scan. -/
theorem ExponentBitLoopValid.value_eq_msbPowScan
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte : UInt256} {mem : ByteArray} {aw bit : UInt256}
    {selected : ExponentBitLoopSelection}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected)
    (mul : Nat → Nat → Nat) (base : Nat) (pfx : Nat)
    (hsquare : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.unset square rest) →
      exponentMontgomeryValue wordCount rM square.memory =
        mul (exponentMontgomeryValue wordCount rM mem')
          (exponentMontgomeryValue wordCount rM mem'))
    (hsquareSet : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {multiply : ExponentMultiplySelection}
      {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.set square multiply rest) →
      exponentMontgomeryValue wordCount rM square.memory =
        mul (exponentMontgomeryValue wordCount rM mem')
          (exponentMontgomeryValue wordCount rM mem'))
    (hmultiply : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {multiply : ExponentMultiplySelection}
      {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.set square multiply rest) →
      exponentMontgomeryValue wordCount rM multiply.memory =
        mul (exponentMontgomeryValue wordCount rM square.memory) base) :
    exponentMontgomeryValue wordCount rM selected.memory =
      (Modexp.msbPowScan mul base
        { value := exponentMontgomeryValue wordCount rM mem, exponent := pfx }
        (exponentBitLoopDecisions selected)).value := by
  induction valid generalizing pfx with
  | done => rfl
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      simp only [ExponentBitLoopSelection.memory, exponentBitLoopDecisions, Modexp.msbPowScan]
      rw [← hsquare (.unset bitNonzero squareValid bitUnset restValid)]
      exact ih (2 * pfx)
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      simp only [ExponentBitLoopSelection.memory, exponentBitLoopDecisions, Modexp.msbPowScan]
      rw [← hsquareSet (.set bitNonzero squareValid multiplyValid bitSet restValid)]
      rw [← hmultiply (.set bitNonzero squareValid multiplyValid bitSet restValid)]
      simp only [if_true]
      exact ih (2 * pfx + 1)

/-- The natural operation computed by one Montgomery multiplication call. -/
def exponentMontgomeryMul (modulus rInv x y : Nat) : Nat :=
  (x * y * rInv) % modulus

/-- Decode a Montgomery-domain natural using the same inverse factor. -/
def exponentMontgomeryDecode (modulus rInv x : Nat) : Nat :=
  (x * rInv) % modulus

theorem exponentMontgomeryDecode_mul (modulus rInv x y : Nat) :
    exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryMul modulus rInv x y) =
      (exponentMontgomeryDecode modulus rInv x *
        exponentMontgomeryDecode modulus rInv y) % modulus := by
  have hleft : (x * y * rInv) % modulus * rInv ≡
      x * y * rInv * rInv [MOD modulus] :=
    (Nat.mod_modEq (x * y * rInv) modulus).mul (Nat.ModEq.refl rInv)
  have hright : (x * rInv) % modulus * ((y * rInv) % modulus) ≡
      (x * rInv) * (y * rInv) [MOD modulus] :=
    (Nat.mod_modEq (x * rInv) modulus).mul
      (Nat.mod_modEq (y * rInv) modulus)
  have halgebra : x * y * rInv * rInv = (x * rInv) * (y * rInv) := by ring
  rw [halgebra] at hleft
  have h := hleft.trans hright.symm
  simpa only [exponentMontgomeryDecode, exponentMontgomeryMul, Nat.ModEq,
    Nat.mod_mod] using h

/-- The selected bit loop therefore computes the ordinary modular power of its decoded base. -/
theorem ExponentBitLoopValid.decoded_value_eq_pow
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte : UInt256} {mem : ByteArray} {aw bit : UInt256}
    {selected : ExponentBitLoopSelection}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected)
    (modulus rInv base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM mem) =
      exponentMontgomeryDecode modulus rInv base ^ pfx % modulus)
    (hsquare : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.unset square rest) →
      exponentMontgomeryValue wordCount rM square.memory =
        exponentMontgomeryMul modulus rInv
          (exponentMontgomeryValue wordCount rM mem')
          (exponentMontgomeryValue wordCount rM mem'))
    (hsquareSet : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {multiply : ExponentMultiplySelection}
      {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.set square multiply rest) →
      exponentMontgomeryValue wordCount rM square.memory =
        exponentMontgomeryMul modulus rInv
          (exponentMontgomeryValue wordCount rM mem')
          (exponentMontgomeryValue wordCount rM mem'))
    (hmultiply : ∀ {mem' : ByteArray} {aw' bit' : UInt256}
      {square : ExponentSquareSelection} {multiply : ExponentMultiplySelection}
      {rest : ExponentBitLoopSelection},
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte mem' aw' bit'
        (.set square multiply rest) →
      exponentMontgomeryValue wordCount rM multiply.memory =
        exponentMontgomeryMul modulus rInv
          (exponentMontgomeryValue wordCount rM square.memory) base) :
    exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM selected.memory) =
      exponentMontgomeryDecode modulus rInv base ^
          ((exponentBitLoopDecisions selected).foldl
            (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  have hvalue :=
    Modexp.MultiLimbExponentModel.ExponentBitLoopValid.value_eq_msbPowScan valid
    (exponentMontgomeryMul modulus rInv) base pfx hsquare hsquareSet hmultiply
  rw [hvalue]
  have hcorrect := Modexp.msbPowScan_correct
    (exponentMontgomeryDecode modulus rInv)
    (exponentMontgomeryMul modulus rInv) base modulus hmodulus
    (exponentMontgomeryDecode_mul modulus rInv)
    { value := exponentMontgomeryValue wordCount rM mem, exponent := pfx }
    (exponentBitLoopDecisions selected) hinitial
  rw [Modexp.msbPowScan_exponent] at hcorrect
  exact hcorrect

/-- A selected byte contributes its descending bits from `topBit` through zero. -/
theorem ExponentByteValid.decisions_eq
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : ExponentByteSelection}
    (valid : ExponentByteValid I fuel wordCount fp rM aM n n0inv
      mem aw byteIdx exponent topBit expLen selected)
    (htop : topBit.toNat < 8) :
    exponentBitLoopDecisions selected.bits =
      exponentBitDecisions selected.byte (topBit.toNat + 1) := by
  have hfit : topBit.toNat + 1 < UInt256.size :=
    lt_of_lt_of_le (by omega : topBit.toNat + 1 < 10) (by native_decide)
  have hadd : (topBit + ⟨1⟩).toNat = topBit.toNat + 1 := by
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt hfit]
  rw [← hadd]
  exact ExponentBitLoopValid.decisions_eq valid.bitsValid

/-- Bit decisions made by all selected exponent bytes, in deployed execution order. -/
def exponentByteLoopDecisions : ExponentByteLoopSelection → List Bool
  | .done _ _ _ _ => []
  | .next byte rest =>
      exponentBitLoopDecisions byte.bits ++ exponentByteLoopDecisions rest

def expectedExponentByteLoopDecisions : Nat → ExponentByteLoopSelection → List Bool
  | _, .done _ _ _ _ => []
  | topBit, .next byte rest =>
      exponentBitDecisions byte.byte (topBit + 1) ++
        expectedExponentByteLoopDecisions 7 rest

/-- Numeric prefix obtained from the bytes recorded by the executable selection. -/
def selectedExponentByteLoopValue : Nat → ExponentByteLoopSelection → Nat → Nat
  | _, .done _ _ _ _, pfx => pfx
  | topBit, .next byte rest, pfx =>
      selectedExponentByteLoopValue 7 rest
        (appendWordBits byte.byte.toNat (topBit + 1) pfx)

theorem expectedExponentByteLoopDecisions_fold
    (topBit : Nat) (selected : ExponentByteLoopSelection) (pfx : Nat)
    (htop : topBit < 256) :
    (expectedExponentByteLoopDecisions topBit selected).foldl
        (fun acc bit => 2 * acc + if bit then 1 else 0) pfx =
      selectedExponentByteLoopValue topBit selected pfx := by
  induction selected generalizing topBit pfx with
  | done => rfl
  | next byte rest ih =>
      rw [expectedExponentByteLoopDecisions, List.foldl_append,
        exponentBitDecisions_fold byte.byte (topBit + 1) pfx (by omega)]
      exact ih 7 _ (by omega)

theorem expectedExponentByteLoopDecisions_toNat
    (topBit : Nat) (selected : ExponentByteLoopSelection) (htop : topBit < 256) :
    bitsToNatMSB (expectedExponentByteLoopDecisions topBit selected) =
      selectedExponentByteLoopValue topBit selected 0 := by
  exact expectedExponentByteLoopDecisions_fold topBit selected 0 htop

/-- A selected suffix records the same bytes as the trusted padded exponent field.  This
predicate deliberately isolates memory framing from the numeric exponent proof. -/
inductive ExponentByteLoopMatches (I : ExecutionEnv) (baseSize exponentSize : Nat) :
    Nat → ExponentByteLoopSelection → Prop where
  | done (mem : ByteArray) (aw byteIdx topBit : UInt256) :
      ExponentByteLoopMatches I baseSize exponentSize exponentSize
        (.done mem aw byteIdx topBit)
  | next {start : Nat} {byte : ExponentByteSelection}
      {rest : ExponentByteLoopSelection}
      (hstart : start < exponentSize)
      (byteEq : byte.byte.toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
      (restMatches : ExponentByteLoopMatches I baseSize exponentSize (start + 1) rest) :
      ExponentByteLoopMatches I baseSize exponentSize start (.next byte rest)

/-- Processing a matching suffix with ordinary eight-bit iterations appends exactly the trusted
big-endian exponent suffix to the existing numeric prefix. -/
theorem ExponentByteLoopMatches.fullBytesValue
    {I : ExecutionEnv} {baseSize exponentSize start : Nat}
    {selected : ExponentByteLoopSelection}
    (matching : ExponentByteLoopMatches I baseSize exponentSize start selected)
    (pfx : Nat) :
    selectedExponentByteLoopValue 7 selected pfx =
      pfx * 256 ^ (exponentSize - start) +
        Model.bytesToNatPadded I.calldata (96 + baseSize + start)
          (exponentSize - start) := by
  induction matching generalizing pfx with
  | done =>
      simp [selectedExponentByteLoopValue, model_bytesToNatPadded_zero_width]
  | @next start byte rest hstart byteEq restMatches ih =>
      have hbyteLt : byte.byte.toNat < 256 := by
        rw [byteEq]
        have h := model_bytesToNatPadded_lt_pow I.calldata
          (96 + baseSize + start) 1
        simpa using h
      have hsplit := model_bytesToNatPadded_split I.calldata
        (96 + baseSize + start) 1 (exponentSize - (start + 1))
      have hwidth : exponentSize - start =
          1 + (exponentSize - (start + 1)) := by omega
      simp only [selectedExponentByteLoopValue]
      rw [appendWordBits_eight byte.byte.toNat pfx hbyteLt, ih]
      rw [hwidth, hsplit, ← byteEq]
      simp only [pow_add, pow_one]
      ring

/-- Processing all bits down from a valid byte top position reconstructs the byte exactly. -/
theorem appendWordBits_zero_eq_of_lt_pow (byte count : Nat)
    (hcount : count ≤ 8) (hbyte : byte < 2 ^ count) :
    appendWordBits byte count 0 = byte := by
  interval_cases count <;>
    simp [appendWordBits, wordBitNat] at hbyte ⊢ <;>
    omega

/-- The first significant byte may start below bit seven.  Once its selected bit count rebuilds
that byte, the remaining full-byte loop denotes the complete trusted exponent suffix. -/
theorem ExponentByteLoopMatches.significantValue
    {I : ExecutionEnv} {baseSize exponentSize start topBit : Nat}
    {byte : ExponentByteSelection} {rest : ExponentByteLoopSelection}
    (hstart : start < exponentSize)
    (byteEq : byte.byte.toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : ExponentByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hfirst : appendWordBits byte.byte.toNat (topBit + 1) 0 = byte.byte.toNat) :
    selectedExponentByteLoopValue topBit (.next byte rest) 0 =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  have htail := restMatches.fullBytesValue byte.byte.toNat
  have hsplit := model_bytesToNatPadded_split I.calldata
    (96 + baseSize + start) 1 (exponentSize - (start + 1))
  have hwidth : exponentSize - start =
      1 + (exponentSize - (start + 1)) := by omega
  simp only [selectedExponentByteLoopValue, hfirst]
  rw [htail, hwidth, hsplit, ← byteEq]
  ring

theorem ExponentByteLoopMatches.significantValue_of_lt_pow
    {I : ExecutionEnv} {baseSize exponentSize start topBit : Nat}
    {byte : ExponentByteSelection} {rest : ExponentByteLoopSelection}
    (hstart : start < exponentSize)
    (byteEq : byte.byte.toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : ExponentByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (htop : topBit < 8) (hbyte : byte.byte.toNat < 2 ^ (topBit + 1)) :
    selectedExponentByteLoopValue topBit (.next byte rest) 0 =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  exact significantValue hstart byteEq restMatches
    (appendWordBits_zero_eq_of_lt_pow byte.byte.toNat (topBit + 1) (by omega) hbyte)

/-- Every valid selected byte loop is the concatenation of the first byte's selected suffix and
all eight bits of each later byte. -/
theorem ExponentByteLoopValid.decisions_eq
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected)
    (htop : topBit.toNat < 8) :
    exponentByteLoopDecisions selected =
      expectedExponentByteLoopDecisions topBit.toNat selected := by
  induction valid with
  | done => rfl
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      simp only [exponentByteLoopDecisions, expectedExponentByteLoopDecisions]
      rw [ExponentByteValid.decisions_eq byteValid htop, ih (by decide)]
      simp only [show (⟨7⟩ : UInt256).toNat = 7 by decide]

/-- The branch stream consumed by a valid complete byte loop denotes exactly the value assembled
from the selected exponent bytes. -/
theorem ExponentByteLoopValid.decisions_toNat
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected)
    (htop : topBit.toNat < 8) :
    bitsToNatMSB (exponentByteLoopDecisions selected) =
      selectedExponentByteLoopValue topBit.toNat selected 0 := by
  rw [ExponentByteLoopValid.decisions_eq valid htop]
  exact expectedExponentByteLoopDecisions_toNat topBit.toNat selected (by omega)

/-- Combined trace-to-model exponent theorem.  The two remaining premises are exactly the
entry/top-bit fact and the stable exponent-memory window fact. -/
theorem ExponentByteLoopValid.decisions_to_model
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {byte : ExponentByteSelection} {rest : ExponentByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit (.next byte rest))
    (htop : topBit.toNat < 8)
    (hstart : start < exponentSize)
    (byteEq : byte.byte.toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : ExponentByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : byte.byte.toNat < 2 ^ (topBit.toNat + 1)) :
    bitsToNatMSB (exponentByteLoopDecisions (.next byte rest)) =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) := by
  rw [ExponentByteLoopValid.decisions_toNat valid htop]
  exact ExponentByteLoopMatches.significantValue_of_lt_pow hstart byteEq restMatches
    htop hbyte

end Modexp.MultiLimbExponentModel
