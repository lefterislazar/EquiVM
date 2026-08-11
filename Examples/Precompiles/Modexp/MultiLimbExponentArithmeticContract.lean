import Examples.Precompiles.Modexp.MultiLimbExponentModel
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFunctionContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFunctionContract

/-! # Arithmetic contracts for selected multi-limb exponent iterations -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbExponentArithmetic

open Modexp.MultiLimbExponentTrace
open Modexp.MultiLimbExponentModel
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbMontgomerySOSCall
open Modexp.MultiLimbMontgomerySOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The semantic and copy geometry needed to interpret one selected exponent-loop square. -/
structure ExponentSquareSemanticGeometry
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM n n0inv : UInt256) (selected : ExponentSquareSelection)
    (modulus rInv : Nat) : Prop where
  function : SOSFunctionSemanticGeometry
    (exponentResetMemory mem (UInt256.ofNat fp)) (exponentResetAw aw) wordCount fp
    n n0inv rM selected.square modulus rInv
    (exponentMontgomeryValue wordCount rM mem)
  copySource : (sosFunctionResultPtr fp).toNat + 32 * wordCount ≤
    selected.square.setup.initialized.arithmetic.suffix.copy.memory.size
  copyResult : (rM + ⟨32⟩).toNat ≤
    selected.square.setup.initialized.arithmetic.suffix.copy.memory.size

/-- A selected exponent-loop square updates the persistent accumulator with exactly one pure
Montgomery square. The exposed `_montSqr` selector supplies the computation; the continuation's
`MCOPY` supplies only the relocation into the persistent array. -/
theorem selectedExponentSquare_value
    {zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat}
    {mem : ByteArray} {aw : UInt256} {wordCount fp : Nat}
    {rM n n0inv : UInt256} {selected : ExponentSquareSelection}
    (modulus rInv : Nat)
    (geometry : ExponentSquareSemanticGeometry mem aw wordCount fp rM n n0inv selected
      modulus rInv)
    (hwords : wordCount ≤ 32)
    (hselect : selectExponentSquare zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw wordCount fp rM n n0inv =
        some selected) :
    exponentMontgomeryValue wordCount rM selected.memory =
      exponentMontgomeryMul modulus rInv
        (exponentMontgomeryValue wordCount rM mem)
        (exponentMontgomeryValue wordCount rM mem) := by
  unfold selectExponentSquare at hselect
  dsimp only at hselect
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  cases hs : selectSOSFunction zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel resetMemory resetAw wordCount fp
      n n0inv ⟨3406⟩ rM with
  | none =>
      rw [hs] at hselect
      contradiction
  | some square =>
      rw [hs] at hselect
      let squareMemory := square.setup.initialized.arithmetic.suffix.copy.memory
      let squareAw := square.setup.initialized.arithmetic.suffix.copy.activeWords
      have hselected : selected = {
          square := square
          memory := exponentCopyMemory squareMemory (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          activeWords := exponentCopyAw squareAw (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          steps := 19 + square.steps + 16
          gas := exponentResetGas aw + square.gas +
            exponentCopyGas squareAw (UInt256.ofNat fp) rM (UInt256.ofNat wordCount) } := by
        exact Option.some.inj hselect.symm
      subst selected
      have hsquare := selectedSOSFunction_value modulus rInv
        (exponentMontgomeryValue wordCount rM mem) geometry.function
        (by simpa [resetMemory, resetAw] using hs)
      have hbytes :
          (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩).toNat = 32 * wordCount :=
        ushl5_ofNat_toNat wordCount (by omega)
      have hcopy := finalCopyMemory_words_eq_source wordCount squareMemory
        (sosFunctionResultPtr fp) (rM + ⟨32⟩)
        (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩)
        geometry.function.wordsPos hbytes geometry.copySource geometry.copyResult
      unfold exponentMontgomeryValue exponentMontgomeryMul
      rw [show exponentCopyMemory squareMemory (UInt256.ofNat fp) rM
          (UInt256.ofNat wordCount) =
          finalCopyMemory squareMemory (sosFunctionResultPtr fp) (rM + ⟨32⟩)
            (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩) by
        rfl]
      rw [hcopy]
      exact hsquare

/-- The semantic and copy geometry needed to interpret one selected exponent-loop multiply. -/
structure ExponentMultiplySemanticGeometry
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM aM n n0inv : UInt256) (selected : ExponentMultiplySelection)
    (modulus rInv base : Nat) : Prop where
  function : CIOSFunctionSemanticGeometry wordCount fp rM aM n n0inv selected.multiply
    modulus rInv (exponentMontgomeryValue wordCount rM mem) base
  resultPtr : selected.multiply.head.setup.resultPtr = UInt256.ofNat fp + ⟨32⟩
  copySource : (UInt256.ofNat fp + ⟨32⟩).toNat + 32 * wordCount ≤
    selected.multiply.finalize.memory.size
  copyResult : (rM + ⟨32⟩).toNat ≤ selected.multiply.finalize.memory.size

/-- A selected set-bit multiplication updates the persistent accumulator with exactly one pure
Montgomery product by the fixed Montgomery base. -/
theorem selectedExponentMultiply_value
    {zeroFuel outerFuel compareFuel subFuel : Nat}
    {mem : ByteArray} {aw : UInt256} {wordCount fp : Nat}
    {rM aM n n0inv : UInt256} {selected : ExponentMultiplySelection}
    (modulus rInv base : Nat)
    (geometry : ExponentMultiplySemanticGeometry mem aw wordCount fp rM aM n n0inv
      selected modulus rInv base)
    (hwords : wordCount ≤ 32)
    (hselect : selectExponentMultiply zeroFuel outerFuel compareFuel subFuel mem aw
      wordCount fp rM aM n n0inv = some selected) :
    exponentMontgomeryValue wordCount rM selected.memory =
      exponentMontgomeryMul modulus rInv
        (exponentMontgomeryValue wordCount rM mem) base := by
  unfold selectExponentMultiply at hselect
  dsimp only at hselect
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  cases hm : selectCIOSFunction zeroFuel outerFuel compareFuel subFuel resetMemory resetAw
      wordCount fp rM aM n n0inv ⟨3406⟩ with
  | none =>
      rw [hm] at hselect
      contradiction
  | some multiply =>
      rw [hm] at hselect
      have hselected : selected = {
          multiply := multiply
          memory := exponentCopyMemory multiply.finalize.memory (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          activeWords := exponentCopyAw multiply.finalize.activeWords (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          steps := 12 + multiply.steps + 16
          gas := exponentMultiplyResetGas aw + multiply.gas +
            exponentCopyGas multiply.finalize.activeWords (UInt256.ofNat fp) rM
              (UInt256.ofNat wordCount) } := by
        exact Option.some.inj hselect.symm
      subst selected
      have hmultiply := selectedCIOSFunction_value modulus rInv
        (exponentMontgomeryValue wordCount rM mem) base geometry.function
        (by simpa [resetMemory, resetAw] using hm)
      rw [geometry.resultPtr] at hmultiply
      have hbytes :
          (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩).toNat = 32 * wordCount :=
        ushl5_ofNat_toNat wordCount (by omega)
      have hcopy := finalCopyMemory_words_eq_source wordCount multiply.finalize.memory
        (UInt256.ofNat fp + ⟨32⟩) (rM + ⟨32⟩)
        (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩)
        (Nat.zero_lt_of_lt geometry.function.layout.columnsGtOne) hbytes
        geometry.copySource geometry.copyResult
      unfold exponentMontgomeryValue exponentMontgomeryMul
      rw [show exponentCopyMemory multiply.finalize.memory (UInt256.ofNat fp) rM
          (UInt256.ofNat wordCount) =
          finalCopyMemory multiply.finalize.memory (UInt256.ofNat fp + ⟨32⟩)
            (rM + ⟨32⟩) (UInt256.shiftLeft (UInt256.ofNat wordCount) ⟨5⟩) by
        rfl]
      rw [hcopy]
      exact hmultiply

/-- Package the square selector contract in the validity record used by the recursive bit loop. -/
theorem ExponentSquareValid.value
    {I : ExecutionEnv} {fuel : ExponentLoopFuel}
    {mem : ByteArray} {aw : UInt256} {wordCount fp : Nat}
    {rM n n0inv : UInt256} {square : ExponentSquareSelection}
    {modulus rInv : Nat}
    (valid : ExponentSquareValid I fuel mem aw wordCount fp rM n n0inv square)
    (geometry : ExponentSquareSemanticGeometry mem aw wordCount fp rM n n0inv square
      modulus rInv) :
    exponentMontgomeryValue wordCount rM square.memory =
      exponentMontgomeryMul modulus rInv
        (exponentMontgomeryValue wordCount rM mem)
        (exponentMontgomeryValue wordCount rM mem) :=
  selectedExponentSquare_value modulus rInv geometry valid.words valid.selected

/-- Package the multiply selector contract in the validity record used by the recursive bit loop. -/
theorem ExponentMultiplyValid.value
    {I : ExecutionEnv} {fuel : ExponentLoopFuel}
    {mem : ByteArray} {aw : UInt256} {wordCount fp : Nat}
    {rM aM n n0inv : UInt256} {multiply : ExponentMultiplySelection}
    {modulus rInv base : Nat}
    (valid : ExponentMultiplyValid I fuel mem aw wordCount fp rM aM n n0inv multiply)
    (geometry : ExponentMultiplySemanticGeometry mem aw wordCount fp rM aM n n0inv
      multiply modulus rInv base) :
    exponentMontgomeryValue wordCount rM multiply.memory =
      exponentMontgomeryMul modulus rInv
        (exponentMontgomeryValue wordCount rM mem) base :=
  selectedExponentMultiply_value modulus rInv base geometry valid.words valid.selected

/-- Supplying the concrete selector geometry at each recursive node discharges all arithmetic
callbacks of the backend-independent bit-loop model. -/
theorem ExponentBitLoopValid.decoded_value_eq_pow_of_geometry
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte : UInt256} {mem : ByteArray} {aw bit : UInt256}
    {selected : ExponentBitLoopSelection}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected)
    (modulus rInv base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM mem) =
      exponentMontgomeryDecode modulus rInv base ^ pfx % modulus)
    (hsquare : ∀ {mem' : ByteArray} {aw' : UInt256}
      {square : ExponentSquareSelection},
      (squareValid : ExponentSquareValid I fuel mem' aw' wordCount fp rM n n0inv square) →
      ExponentSquareSemanticGeometry mem' aw' wordCount fp rM n n0inv square
        modulus rInv)
    (hmultiply : ∀ {mem' : ByteArray} {aw' : UInt256}
      {multiply : ExponentMultiplySelection},
      (multiplyValid : ExponentMultiplyValid I fuel mem' aw' wordCount fp rM aM n n0inv
        multiply) →
      ExponentMultiplySemanticGeometry mem' aw' wordCount fp rM aM n n0inv multiply
        modulus rInv base) :
    exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM selected.memory) =
      exponentMontgomeryDecode modulus rInv base ^
          ((exponentBitLoopDecisions selected).foldl
            (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  apply Modexp.MultiLimbExponentModel.ExponentBitLoopValid.decoded_value_eq_pow valid
    modulus rInv base pfx hmodulus hinitial
  · intro mem' aw' bit' square rest step
    cases step with
    | unset bitNonzero squareValid bitUnset restValid =>
        exact Modexp.MultiLimbExponentArithmetic.ExponentSquareValid.value squareValid
          (hsquare squareValid)
  · intro mem' aw' bit' square multiply rest step
    cases step with
    | set bitNonzero squareValid multiplyValid bitSet restValid =>
        exact Modexp.MultiLimbExponentArithmetic.ExponentSquareValid.value squareValid
          (hsquare squareValid)
  · intro mem' aw' bit' square multiply rest step
    cases step with
    | set bitNonzero squareValid multiplyValid bitSet restValid =>
        exact Modexp.MultiLimbExponentArithmetic.ExponentMultiplyValid.value multiplyValid
          (hmultiply multiplyValid)

/-- The arithmetic invariant threads through every selected exponent byte. -/
theorem ExponentByteLoopValid.decoded_value_eq_pow_of_geometry
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected)
    (modulus rInv base pfx : Nat) (hmodulus : 0 < modulus)
    (hinitial : exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM mem) =
      exponentMontgomeryDecode modulus rInv base ^ pfx % modulus)
    (hsquare : ∀ {mem' : ByteArray} {aw' : UInt256}
      {square : ExponentSquareSelection},
      (squareValid : ExponentSquareValid I fuel mem' aw' wordCount fp rM n n0inv square) →
      ExponentSquareSemanticGeometry mem' aw' wordCount fp rM n n0inv square
        modulus rInv)
    (hmultiply : ∀ {mem' : ByteArray} {aw' : UInt256}
      {multiply : ExponentMultiplySelection},
      (multiplyValid : ExponentMultiplyValid I fuel mem' aw' wordCount fp rM aM n n0inv
        multiply) →
      ExponentMultiplySemanticGeometry mem' aw' wordCount fp rM aM n n0inv multiply
        modulus rInv base) :
    exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM selected.memory) =
      exponentMontgomeryDecode modulus rInv base ^
          ((exponentByteLoopDecisions selected).foldl
            (fun acc decision => 2 * acc + if decision then 1 else 0) pfx) % modulus := by
  induction valid generalizing pfx with
  | done mem aw byteIdx topBit guardZero =>
      simpa [ExponentByteLoopSelection.memory, exponentByteLoopDecisions] using hinitial
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      have hbyte :=
        Modexp.MultiLimbExponentArithmetic.ExponentBitLoopValid.decoded_value_eq_pow_of_geometry
          byteValid.bitsValid modulus rInv base pfx hmodulus hinitial hsquare hmultiply
      have hrest := ih
        ((exponentBitLoopDecisions byte.bits).foldl
          (fun acc decision => 2 * acc + if decision then 1 else 0) pfx)
        (by simpa [byteValid.memoryEq] using hbyte)
      simpa [ExponentByteLoopSelection.memory, exponentByteLoopDecisions,
        List.foldl_append] using hrest

/-- Combining byte-loop arithmetic with the trusted exponent-memory model yields the pure modular
power for the complete selected exponent suffix. -/
theorem ExponentByteLoopValid.decoded_value_eq_calldata_pow
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {byte : ExponentByteSelection} {rest : ExponentByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit (.next byte rest))
    (modulus rInv base : Nat) (hmodulus : 0 < modulus)
    (hinitial : exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM mem) = 1 % modulus)
    (hsquare : ∀ {mem' : ByteArray} {aw' : UInt256}
      {square : ExponentSquareSelection},
      (squareValid : ExponentSquareValid I fuel mem' aw' wordCount fp rM n n0inv square) →
      ExponentSquareSemanticGeometry mem' aw' wordCount fp rM n n0inv square
        modulus rInv)
    (hmultiply : ∀ {mem' : ByteArray} {aw' : UInt256}
      {multiply : ExponentMultiplySelection},
      (multiplyValid : ExponentMultiplyValid I fuel mem' aw' wordCount fp rM aM n n0inv
        multiply) →
      ExponentMultiplySemanticGeometry mem' aw' wordCount fp rM aM n n0inv multiply
        modulus rInv base)
    (htop : topBit.toNat < 8)
    (hstart : start < exponentSize)
    (byteEq : byte.byte.toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : ExponentByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : byte.byte.toNat < 2 ^ (topBit.toNat + 1)) :
    exponentMontgomeryDecode modulus rInv
        (exponentMontgomeryValue wordCount rM
          (ExponentByteLoopSelection.next byte rest).memory) =
      exponentMontgomeryDecode modulus rInv base ^
          Model.bytesToNatPadded I.calldata (96 + baseSize + start)
            (exponentSize - start) % modulus := by
  have harithmetic :=
    Modexp.MultiLimbExponentArithmetic.ExponentByteLoopValid.decoded_value_eq_pow_of_geometry
      valid modulus rInv base 0 hmodulus (by simpa using hinitial) hsquare hmultiply
  have hexponent := Modexp.MultiLimbExponentModel.ExponentByteLoopValid.decisions_to_model
    valid htop hstart byteEq restMatches hbyte
  rw [bitsToNatMSB] at hexponent
  rw [hexponent] at harithmetic
  exact harithmetic

end Modexp.MultiLimbExponentArithmetic
