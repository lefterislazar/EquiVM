import Examples.Precompiles.Modexp.MultiLimbBarrettResultContract
import Examples.Precompiles.Modexp.MultiLimbBarrettExponentSetup
import Examples.Precompiles.Modexp.MultiLimbLimbsToBytesSemantic
import Examples.Precompiles.Modexp.ReturnSuffix

/-!
# Barrett exponent/result semantics

This module lifts the selected Barrett byte-loop arithmetic through the leading-byte and top-bit
setup selectors, then connects the selected accumulator value to result serialization.
-/

open Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Modexp.MultiLimbBarrettResultSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbBarrettExponentLoop
open Modexp.MultiLimbBarrettExponentSemantic
open Modexp.MultiLimbBarrettExponentSetup
open Modexp.MultiLimbBarrettExponentTrace
open Modexp.MultiLimbBarrettAccumulator
open Modexp.MultiLimbExponentTrace
open Modexp.MultiLimbLimbsToBytes
open Modexp.MultiLimbLimbsToBytesSemantic
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The leading-zero scanner only reads exponent memory; active words may grow, but bytes do not
change. -/
theorem BarrettLeadingScanValid.memory_eq
    {exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected) :
    selected.memory = mem := by
  induction valid with
  | exhausted => rfl
  | found => rfl
  | skipZero _ _ _ _ _ restValid ih =>
      simpa [BarrettLeadingScanSelection.memory] using ih

/-- An exhausted selected scan ends at a cleared loop guard. -/
theorem BarrettLeadingScanValid.finalGuardZero
    {exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (hexhausted : selected.isExhausted = true) :
    selected.startByte.lt expLen = ⟨0⟩ := by
  induction valid with
  | exhausted guardZero => exact guardZero
  | found => simp [BarrettLeadingScanSelection.isExhausted] at hexhausted
  | skipZero _ _ _ _ _ restValid ih => exact ih hexhausted

/-- An exhausted setup scan leaves the initialized accumulator unchanged. -/
theorem BarrettLoopSetupValid.allZero_value
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {value : Nat}
    (valid : BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.allZero scan))
    (hinitial : barrettAccumulatorValue kWords r mem = value) :
    barrettAccumulatorValue kWords r (BarrettLoopSetupSelection.allZero scan).memory = value := by
  cases valid with
  | allZero scanValid exhausted =>
      rw [BarrettLoopSetupSelection.memory,
        Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.memory_eq scanValid]
      exact hinitial

/-- An exhausted fresh setup scan leaves the concretely initialized accumulator unchanged. -/
theorem FreshBarrettLoopSetupValid.allZero_value
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {value : Nat}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.allZero scan))
    (hinitial : barrettAccumulatorValue kWords r mem = value) :
    barrettAccumulatorValue kWords r
        (FreshBarrettLoopSetupSelection.allZero scan).memory = value := by
  cases valid with
  | allZero scanValid exhausted =>
      rw [FreshBarrettLoopSetupSelection.memory,
        Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.memory_eq scanValid]
      exact hinitial

/-- The fresh nonzero setup path computes the trusted exponent suffix from its selected first
square/multiply byte and all remaining reused-scratch bytes. -/
theorem BarrettLeadingScanValid.fresh_nonzero_value_eq_model_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {first : FreshBarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (scanValid : BarrettLeadingScanValid exponent expLen mem
      (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
    (hnonexhausted : scan.isExhausted = false)
    (topValid : BarrettTopBitValid
      (barrettExponentByteValue scan.memory
        (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
        exponent scan.startByte) ⟨7⟩ top)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory
      (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
      kWords fp scan.startByte exponent top.topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r
        (FreshBarrettLoopSetupSelection.nonzero scan top first rest).memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
  have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant hexponentFit
    (fun idx hguard =>
      (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
  have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩) (by native_decide)
  have hguard := scanValid.finalGuardSet hnonexhausted
  let aw0 := readWords1 scan.activeWords ⟨64⟩
  let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
  rcases haccess scan.memory aw0 scan.startByte hguard with
    ⟨topIndex, topExponentFit, topByteFit⟩
  have topLoadInvariant := freeInvariant.afterExponentByteLoad topExponentFit topByteFit
  rcases haccess scan.memory aw2 scan.startByte hguard with
    ⟨firstIndex, firstExponentFit, firstByteFit⟩
  have htopBound : top.topBit.toNat ≤ 7 := by simpa using topValid.topBit_le
  have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by
        have hs : 8 < UInt256.size := by decide
        omega)]
    omega
  have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by
        have hs : 8 < UInt256.size := by decide
        omega)] at hzNat
    simp at hzNat
  have hvalue := selectFreshBarrettByteAndLoop_value_eq_model_powInvariant
    topLoadInvariant hguard firstIndex htopGuard hcounter (by omega)
    firstExponentFit firstByteFit haccess hinitial
    (by simpa only [aw0, aw2] using hfirst) hrest startLt byteEq restMatches hbyte
  simpa [FreshBarrettLoopSetupSelection.memory] using hvalue

/-- Framed counterpart of `fresh_nonzero_value_eq_model_powInvariant`. -/
theorem BarrettLeadingScanValid.fresh_nonzero_value_eq_model_powInvariantFramed
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {first : FreshBarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (scanValid : BarrettLeadingScanValid exponent expLen mem
      (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
    (hnonexhausted : scan.isExhausted = false)
    (topValid : BarrettTopBitValid
      (barrettExponentByteValue scan.memory
        (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
        exponent scan.startByte) ⟨7⟩ top)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory
      (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
      kWords fp scan.startByte exponent top.topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r
        (FreshBarrettLoopSetupSelection.nonzero scan top first rest).memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  have scanStartInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
  have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
    access.exponentFit access.byteFit
  have scanAccess : BarrettExponentAccessFrame scan.memory exponent expLen r := by
    simpa only [Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.memory_eq
      scanValid] using access
  have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩) (by native_decide)
  have hguard := scanValid.finalGuardSet hnonexhausted
  let aw0 := readWords1 scan.activeWords ⟨64⟩
  let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
  have topLoadInvariant := freeInvariant.afterExponentByteLoad scanAccess.exponentFit
    (scanAccess.byteFit scan.startByte hguard)
  have hlength : exponentArrayLength scan.memory aw2 exponent = expLen :=
    exponentArrayLength_eq_of_header topLoadInvariant.covered topLoadInvariant.activeWordsFit
      scanAccess.headerConcrete scanAccess.header
  have firstIndex :
      (scan.startByte.lt (exponentArrayLength scan.memory aw2 exponent)).isZero = ⟨0⟩ := by
    rw [hlength]
    exact isZero_eq_zero_of_ne hguard
  have htopBound : top.topBit.toNat <= 7 := by simpa using topValid.topBit_le
  have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by
        have hs : 8 < UInt256.size := by decide
        omega)]
    omega
  have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by
        have hs : 8 < UInt256.size := by decide
        omega)] at hzNat
    simp at hzNat
  have hvalue := selectFreshBarrettByteAndLoop_value_eq_model_powInvariantFramed
    topLoadInvariant hguard firstIndex htopGuard hcounter (by omega) scanAccess hinitial
    (by simpa only [aw0, aw2] using hfirst) hrest startLt byteEq restMatches hbyte
  simpa [FreshBarrettLoopSetupSelection.memory] using hvalue

/-- The concrete nonzero setup path computes the trusted exponent suffix from one persistent
Barrett invariant. All square and multiply geometry is derived internally; the access provider is
limited to Solidity's checked dynamic-array reads and representable MLOAD addresses. -/
theorem BarrettLeadingScanValid.nonzero_value_eq_model_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (scanValid : BarrettLeadingScanValid exponent expLen mem
      (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
    (hnonexhausted : scan.isExhausted = false)
    (topValid : BarrettTopBitValid
      (barrettExponentByteValue scan.memory
        (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
        exponent scan.startByte) ⟨7⟩ top)
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hloop : selectBarrettByteLoop byteFuel bitFuel callFuel scan.memory
      (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
      kWords fp scan.startByte exponent top.topBit expLen r a n mu =
        some (.next byte rest))
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r
        (BarrettLoopSetupSelection.nonzero scan top (.next byte rest)).memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % nValue := by
  have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
  have scanInvariant := scanValid.preserveInvariant scanStartInvariant hexponentFit
    (fun idx hguard =>
      (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
  have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
    (by native_decide)
  have hguard := scanValid.finalGuardSet hnonexhausted
  rcases haccess scan.memory (readWords1 scan.activeWords ⟨64⟩) scan.startByte hguard with
    ⟨indexValid, exponentFit, byteFit⟩
  have byteStartInvariant := freeInvariant.afterExponentByteLoad exponentFit byteFit
  have htopBound : top.topBit.toNat ≤ 7 := by
    simpa using topValid.topBit_le
  have hvalue := selectBarrettByteLoop_value_eq_model_powInvariant byteStartInvariant
    htopBound haccess hinitial hloop startLt byteEq restMatches hbyte
  simpa [BarrettLoopSetupSelection.memory] using hvalue

/-- A nonzero setup selection computes the pure modular power of the trusted significant exponent
suffix. Every square and multiply still uses the concrete Barrett geometry provider. -/
theorem BarrettLoopSetupValid.nonzero_value_eq_model_pow
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start modulus base : Nat}
    (valid : BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.nonzero scan top (.next byte rest)))
    (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ 0 % modulus)
    (hsquare : BarrettSquareGeometryProvider I callFuel kWords fp r n mu modulus)
    (hmultiply : BarrettMultiplyGeometryProvider I callFuel kWords fp r a n mu base modulus)
    (htop : top.topBit.toNat < 8)
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1)) :
    barrettAccumulatorValue kWords r
        (BarrettLoopSetupSelection.nonzero scan top (.next byte rest)).memory =
      base ^ Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start) % modulus := by
  cases valid with
  | nonzero scanValid nonexhausted indexValid freePointer topValid bytesValid =>
      have hscanMemory :=
        Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.memory_eq scanValid
      have hinitial' : barrettAccumulatorValue kWords r scan.memory =
          base ^ 0 % modulus := by
        rw [hscanMemory]
        exact hinitial
      have hvalue := bytesValid.value_eq_model_pow_of_geometry hmodulus hinitial'
        hsquare hmultiply htop startLt byteEq restMatches hbyte
      simpa [BarrettLoopSetupSelection.memory] using hvalue

/-- The exhausted leading scan computes the pure zero-exponent result once its scanned calldata
window is identified with zero. -/
theorem BarrettLoopSetupValid.allZero_value_eq_model_pow
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {baseSize exponentSize modulus base : Nat}
    (valid : BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.allZero scan))
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ 0 % modulus)
    (hexponent : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize = 0) :
    barrettAccumulatorValue kWords r
        (BarrettLoopSetupSelection.allZero scan).memory =
      base ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % modulus := by
  rw [Modexp.MultiLimbBarrettResultSemantic.BarrettLoopSetupValid.allZero_value
    valid hinitial, hexponent]

/-- Fresh-scratch counterpart of the exhausted leading-scan model theorem. -/
theorem FreshBarrettLoopSetupValid.allZero_value_eq_model_pow
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {baseSize exponentSize modulus base : Nat}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.allZero scan))
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ 0 % modulus)
    (hexponent : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize = 0) :
    barrettAccumulatorValue kWords r
        (FreshBarrettLoopSetupSelection.allZero scan).memory =
      base ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % modulus := by
  rw [Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.allZero_value
    valid hinitial, hexponent]

/-- A fresh nonzero selection computes the pure power for the entire exponent once the leading
zero scan is connected to the significant calldata suffix. -/
theorem FreshBarrettLoopSetupValid.nonzero_value_eq_full_model_powInvariant
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {first : FreshBarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.nonzero scan top first rest))
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue)
    (hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory
      (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
      kWords fp scan.startByte exponent top.topBit r a n mu = some first)
    (hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
      first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩ expLen
      r a n mu = some rest)
    (startLt : start < exponentSize)
    (byteEq : (first.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (first.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1))
    (hsuffix : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start)) :
    barrettAccumulatorValue kWords r
        (FreshBarrettLoopSetupSelection.nonzero scan top first rest).memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % nValue := by
  cases valid with
  | nonzero scanValid nonexhausted indexValid freePointer topValid firstValid restValid =>
      have hscanNonexhausted : scan.isExhausted = false := by
        cases hscan : scan.isExhausted with
        | false => rfl
        | true =>
            exact False.elim (firstValid.guardTaken
              (Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.finalGuardZero
                scanValid (by simpa using hscan)))
      rw [hsuffix]
      exact Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.fresh_nonzero_value_eq_model_powInvariant
        scanValid
        hscanNonexhausted topValid invariant hexponentFit haccess hinitial
        hfirst hrest startLt byteEq restMatches hbyte

/-- The Barrett byte helper is the high byte of its checked 32-byte load. -/
theorem barrettExponentByteValue_toNat
    (mem : ByteArray) (aw exponent idx : UInt256) :
    (barrettExponentByteValue mem aw exponent idx).toNat =
      (exponentByteWord mem aw (exponentByteAddress exponent idx)).toNat / 2 ^ 248 := by
  let word := exponentByteWord mem aw (exponentByteAddress exponent idx)
  have hmask :
      (⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩ :
        UInt256) = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248) := by
    native_decide
  unfold barrettExponentByteValue
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    show (⟨248⟩ : UInt256).toNat = 248 by decide, hmask,
    Reasoning.Theory.u256_land_high_mask_toNat word 248 (by omega),
    Nat.mul_comm (word.toNat / 2 ^ 248) (2 ^ 248),
    Nat.mul_div_right _ (by positivity : 0 < (2 : Nat) ^ 248)]

/-- The leading scanner's masked word is zero exactly when the extracted Barrett byte is zero. -/
theorem barrettScanMaskedWord_eq_zero_iff
    (mem : ByteArray) (aw exponent idx : UInt256) :
    barrettScanMaskedWord mem aw exponent idx = ⟨0⟩ ↔
      barrettExponentByteValue mem aw exponent idx = ⟨0⟩ := by
  let word := exponentByteWord mem aw (exponentByteAddress exponent idx)
  let mask : UInt256 :=
    ⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩
  have hmask : mask = UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248) := by
    native_decide
  have hscanNat : (barrettScanMaskedWord mem aw exponent idx).toNat =
      (word.toNat / 2 ^ 248) * 2 ^ 248 := by
    simp only [barrettScanMaskedWord]
    change ((mask.land word).land mask).toNat = _
    have hcomm :
        ((UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248)).land word).land
            (UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248)) =
          (UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248)).land
            ((UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248)).land word) := by
      exact Reasoning.Theory.u256_land_comm _ _
    rw [hmask, hcomm,
      Reasoning.Theory.u256_land_high_mask_toNat
        ((UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 248)).land word) 248 (by omega),
      Reasoning.Theory.u256_land_high_mask_toNat word 248 (by omega),
      Nat.mul_comm (word.toNat / 2 ^ 248) (2 ^ 248),
      Nat.mul_div_right _ (by positivity : 0 < (2 : Nat) ^ 248)]
    exact Nat.mul_comm _ _
  have hbyteNat : (barrettExponentByteValue mem aw exponent idx).toNat =
      word.toNat / 2 ^ 248 := by
    simpa only [word] using barrettExponentByteValue_toNat mem aw exponent idx
  constructor
  · intro hzero
    apply u256_inj
    rw [hbyteNat, show (⟨0⟩ : UInt256).toNat = 0 by decide]
    have hnat := congrArg UInt256.toNat hzero
    rw [hscanNat, show (⟨0⟩ : UInt256).toNat = 0 by decide] at hnat
    omega
  · intro hzero
    apply u256_inj
    rw [hscanNat, show (⟨0⟩ : UInt256).toNat = 0 by decide]
    have hnat := congrArg UInt256.toNat hzero
    rw [hbyteNat, show (⟨0⟩ : UInt256).toNat = 0 by decide] at hnat
    rw [hnat, Nat.zero_mul]

/-- A Barrett exponent-byte load that is framed back to a concrete source byte denotes exactly
the corresponding trusted padded calldata byte. -/
theorem barrettExponentByteValue_toNat_eq_model_of_frame
    (I : ExecutionEnv) (mem source : ByteArray) (aw exponent idx : UInt256)
    (address calldataOffset : Nat)
    (haddress : (exponentByteAddress exponent idx).toNat = address)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : address + 32 ≤ mem.size)
    (haddress64 : address < 2 ^ 64)
    (hcalldataOffset64 : calldataOffset < 2 ^ 64)
    (hframe : mem.readWithPadding address 32 = source.readWithPadding address 32)
    (hsource : source.readWithPadding address 1 =
      I.calldata.readWithPadding calldataOffset 1) :
    (barrettExponentByteValue mem aw exponent idx).toNat =
      Model.bytesToNatPadded I.calldata calldataOffset 1 := by
  let ptr := exponentByteAddress exponent idx
  have hptrWord : ptr.toNat + 32 ≤ mem.size := by
    simpa only [ptr, haddress] using hword
  have hactive : ¬ ptr ≥ aw * ⟨32⟩ :=
    wordBelowActive_of_covered mem aw ptr hcovered hawFit hptrWord
  have hdecoded : exponentByteWord mem aw ptr =
      uInt256OfByteArray (mem.readWithPadding address 32) := by
    unfold exponentByteWord
    rw [if_neg (not_or.mpr ⟨by omega, hactive⟩)]
    rw [haddress]
    exact (uInt256OfByteArray_eq _).symm
  have hreadBytes : mem.readBytes address 32 = mem.readWithPadding address 32 := by
    rw [readBytes_eq_model_readPadded mem address 32 haddress64 (by decide),
      readWithPadding_eq_model_readPadded mem address 32 haddress64 (by decide)]
  have hbyteMem :
      (UInt256.byteAt ⟨0⟩ (uInt256OfByteArray
        (mem.readWithPadding address 32))).toNat =
        Model.bytesToNatPadded mem address 1 := by
    rw [← hreadBytes]
    exact calldataByte0_toNat_eq_model mem address haddress64
  have hframeOne : mem.readWithPadding address 1 =
      source.readWithPadding address 1 := by
    calc
      mem.readWithPadding address 1 =
          (mem.readWithPadding address 32).extract 0 1 := by
            symm
            exact readWithPadding_window mem address 32 0 1 haddress64 (by decide)
              (by simpa using haddress64) (by decide) (by omega)
      _ = (source.readWithPadding address 32).extract 0 1 := by
            exact congrArg (fun bs : ByteArray => bs.extract 0 1) hframe
      _ = source.readWithPadding address 1 := by
            exact readWithPadding_window source address 32 0 1 haddress64 (by decide)
              (by simpa using haddress64) (by decide) (by omega)
  have hmodel : Model.bytesToNatPadded mem address 1 =
      Model.bytesToNatPadded I.calldata calldataOffset 1 :=
    model_bytesToNatPadded_eq_of_readWithPadding haddress64 hcalldataOffset64
      (by decide) (hframeOne.trans hsource)
  rw [barrettExponentByteValue_toNat, show exponentByteAddress exponent idx = ptr by rfl,
    hdecoded]
  have hbyteAt := byteAt_zero_toNat
    (uInt256OfByteArray (mem.readWithPadding address 32))
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    show (UInt256.ofNat 248).toNat = 248 by decide] at hbyteAt
  exact hbyteAt.symm.trans (hbyteMem.trans hmodel)

/-- The executable remaining-byte selector matches the trusted calldata suffix whenever its
persistent exponent window is framed back to a concrete source. -/
theorem selectBarrettByteLoop_matches_of_frame
    {I : ExecutionEnv}
    {byteFuel bitFuel callFuel kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem source : ByteArray}
    {aw byteIdx topBit : UInt256} {selected : BarrettByteLoopSelection}
    {baseSize exponentSize start : Nat}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hexpLen : expLen = UInt256.ofNat exponentSize)
    (hexponentSize : exponentSize < UInt256.size)
    (hstartLe : start ≤ exponentSize)
    (hidx : byteIdx.toNat = start)
    (htopBound : topBit.toNat ≤ 7)
    (haddress : ∀ s, s < exponentSize →
      (exponentByteAddress exponent (UInt256.ofNat s)).toNat =
        exponent.toNat + 32 + s)
    (hpayloadBelow : exponent.toNat + 32 + exponentSize + 31 ≤ r.toNat)
    (hcalldataBound : 96 + baseSize + exponentSize < 2 ^ 64)
    (hsource : ∀ s, s < exponentSize →
      source.readWithPadding (exponent.toNat + 32 + s) 1 =
        I.calldata.readWithPadding (96 + baseSize + s) 1)
    (hframe : ∀ s, s < exponentSize →
      mem.readWithPadding (exponent.toNat + 32 + s) 32 =
        source.readWithPadding (exponent.toNat + 32 + s) 32)
    (hselect : selectBarrettByteLoop byteFuel bitFuel callFuel mem aw kWords fp
      byteIdx exponent topBit expLen r a n mu = some selected) :
    BarrettByteLoopMatches I baseSize exponentSize start selected := by
  induction byteFuel generalizing mem aw byteIdx topBit selected rValue start with
  | zero =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        have hge : expLen.toNat ≤ byteIdx.toNat := by
          by_contra hnot
          have hone := ult_one (a := byteIdx) (b := expLen) (by omega)
          exact (by native_decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hone.symm.trans hguard)
        have hlenNat : expLen.toNat = exponentSize := by
          rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
        have hstartEq : start = exponentSize := by omega
        rw [hstartEq]
        exact .done mem aw byteIdx topBit
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectBarrettByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        have hge : expLen.toNat ≤ byteIdx.toNat := by
          by_contra hnot
          have hone := ult_one (a := byteIdx) (b := expLen) (by omega)
          exact (by native_decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hone.symm.trans hguard)
        have hlenNat : expLen.toNat = exponentSize := by
          rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
        have hstartEq : start = exponentSize := by omega
        rw [hstartEq]
        exact .done mem aw byteIdx topBit
      · simp only [hguard, if_false] at hselect
        have hidxLt : byteIdx.toNat < expLen.toNat := by
          by_contra hnot
          exact hguard (ult_zero (by omega))
        have hlenNat : expLen.toNat = exponentSize := by
          rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
        have hstartLt : start < exponentSize := by omega
        have hidxWord : byteIdx = UInt256.ofNat start := by
          apply u256_inj
          rw [hidx, UInt256.toNat_ofNat_of_lt (lt_trans hstartLt hexponentSize)]
        have haddr := haddress start hstartLt
        rw [← hidxWord] at haddr
        let read := exponent.toNat + 32 + start
        have hread96 : 96 ≤ read := by
          dsimp only [read]
          exact le_trans access.exponentBase (by omega)
        have hbelow : read + 32 ≤ r.toNat := by
          dsimp only [read]
          omega
        have hrMem : r.toNat ≤ mem.size := by
          apply le_trans (b := fp)
          · have hr := invariant.rBeforeScratch
            omega
          · apply le_trans (b :=
                Modexp.MultiLimbBarrettReusedCall.scratchEnd fp kWords)
            · unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
                Modexp.MultiLimbBarrettReusedCall.callResultFp
                wordArrayAllocationSize wordArrayPayloadSize
              omega
            · exact invariant.scratchConcrete
        have hword : read + 32 ≤ mem.size := hbelow.trans hrMem
        have hr64 : r.toNat < 2 ^ 64 := by
          apply lt_of_le_of_lt (b := fp)
          · have hr := invariant.rBeforeScratch
            omega
          · apply lt_of_le_of_lt
              (b := Modexp.MultiLimbBarrettReusedCall.scratchEnd fp kWords)
            · unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
                Modexp.MultiLimbBarrettReusedCall.callResultFp
                wordArrayAllocationSize wordArrayPayloadSize
              omega
            · exact invariant.scratchBound
        have htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩ := by
          apply ugt_zero
          rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
            Nat.mod_eq_of_lt (by
              have hs : 8 < UInt256.size := by decide
              omega)]
          omega
        have hlength : exponentArrayLength mem aw exponent = expLen :=
          exponentArrayLength_eq_of_header invariant.covered invariant.activeWordsFit
            access.headerConcrete access.header
        have hindex :
            (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩ := by
          rw [hlength]
          exact isZero_eq_zero_of_ne hguard
        cases hbyte : selectBarrettByte bitFuel callFuel mem aw kWords fp byteIdx exponent
            topBit r a n mu with
        | none => simp [hbyte] at hselect
        | some byte =>
            cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel byte.memory
                byte.activeWords kWords fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                r a n mu with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                rcases selectBarrettByte_validInvariantReadBelow invariant hguard hindex htop
                    access.exponentFit (access.byteFit byteIdx hguard)
                    access.exponentBase access.exponentBelowAccumulator hbyte with
                  ⟨nextValue, byteValid, nextInvariant, headerFrame⟩
                have nextAccess : BarrettExponentAccessFrame byte.memory exponent expLen r := {
                  access with
                  headerConcrete := nextInvariant.exponentHeaderConcrete
                    access.exponentBelowAccumulator
                  header := headerFrame.trans access.header }
                have lengthInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
                have hdecoded := barrettExponentByteValue_toNat_eq_model_of_frame I mem source
                  (exponentArrayLengthAw aw exponent) exponent byteIdx read
                  (96 + baseSize + start) (by simpa only [read] using haddr)
                  lengthInvariant.covered lengthInvariant.activeWordsFit hword
                  (by
                    dsimp only [read]
                    exact lt_trans (by omega : exponent.toNat + 32 + start < r.toNat)
                      hr64)
                  (by omega)
                  (hframe start hstartLt) (hsource start hstartLt)
                have hbyteNat : byte.byte.toNat =
                    Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
                  rw [byteValid.byteEq]
                  exact hdecoded
                have hbyteLt : byte.byte.toNat < 256 := by
                  rw [hbyteNat]
                  have h := model_bytesToNatPadded_lt_pow I.calldata
                    (96 + baseSize + start) 1
                  simpa using h
                have hbyteEq : (byte.byte.land ⟨255⟩).toNat =
                    Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
                  rw [Reasoning.Theory.uland_toNat,
                    show (⟨255⟩ : UInt256).toNat = 255 by decide]
                  change Nat.land byte.byte.toNat (2 ^ 8 - 1) = _
                  rw [Reasoning.Theory.nat_land_mask_eq_mod,
                    show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hbyteLt, hbyteNat]
                have hnextIdx : (byteIdx + ⟨1⟩).toNat = start + 1 := by
                  rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide, hidx,
                    Nat.mod_eq_of_lt (by omega)]
                have hnextFrame : ∀ s, s < exponentSize →
                    byte.memory.readWithPadding (exponent.toNat + 32 + s) 32 =
                      source.readWithPadding (exponent.toNat + 32 + s) 32 := by
                  intro s hs
                  have hsAddr := haddress s hs
                  let read' := exponent.toNat + 32 + s
                  have hs96 : 96 ≤ read' := by
                    dsimp only [read']
                    exact le_trans access.exponentBase (by omega)
                  have hsBelow : read' + 32 ≤ r.toNat := by dsimp only [read']; omega
                  rcases selectBarrettByte_validInvariantReadBelow invariant hguard hindex htop
                      access.exponentFit (access.byteFit byteIdx hguard) hs96 hsBelow hbyte with
                    ⟨_, _, _, selectedFrame⟩
                  exact selectedFrame.trans (hframe s hs)
                have restMatches := ih nextInvariant nextAccess (by omega) hnextIdx
                  (by decide) hnextFrame hrest
                exact .next hstartLt hbyteEq restMatches

/-- A zero result from the deployed top-bit test removes the current highest possible bit. -/
theorem barrettTopBitTest_zero_lt_pow
    (byte topBit : UInt256)
    (htop : topBit.toNat < 8)
    (hbound : (byte.land ⟨255⟩).toNat < 2 ^ (topBit.toNat + 1))
    (hzero : barrettTopBitTest byte topBit = ⟨0⟩) :
    (byte.land ⟨255⟩).toNat < 2 ^ topBit.toNat := by
  let masked := byte.land ⟨255⟩
  have hcomm : (⟨1⟩ : UInt256).land (masked.shiftRight topBit) =
      (masked.shiftRight topBit).land ⟨1⟩ :=
    Reasoning.Theory.u256_land_comm _ _
  have hzeroNat := congrArg UInt256.toNat hzero
  rw [barrettTopBitTest, show byte.land ⟨255⟩ = masked by rfl, hcomm,
    uInt256_land_one_toNat,
    shiftRight_toNat_of_lt256 masked topBit (by omega),
    show (⟨0⟩ : UInt256).toNat = 0 by decide] at hzeroNat
  have hquotLt : masked.toNat / 2 ^ topBit.toNat < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ, Nat.mul_comm] using hbound
  have hquotZero : masked.toNat / 2 ^ topBit.toNat = 0 := by
    rw [Nat.mod_eq_of_lt hquotLt] at hzeroNat
    exact hzeroNat
  have hdiv := (Nat.div_eq_zero_iff).mp hquotZero
  rcases hdiv with hpow | hmasked
  · exact False.elim ((pow_ne_zero topBit.toNat (by decide : (2 : Nat) ≠ 0)) hpow)
  · exact hmasked

/-- A valid top-bit scan returns a cursor large enough to represent the complete masked byte. -/
theorem BarrettTopBitValid.byte_lt_selected_pow
    {byte startBit : UInt256} {selected : BarrettTopBitSelection}
    (valid : BarrettTopBitValid byte startBit selected)
    (hstart : startBit.toNat < 8)
    (hbound : (byte.land ⟨255⟩).toNat < 2 ^ (startBit.toNat + 1)) :
    (byte.land ⟨255⟩).toNat < 2 ^ (selected.topBit.toNat + 1) := by
  induction valid with
  | zeroCursor => simpa [BarrettTopBitSelection.topBit] using hbound
  | setBit positive bitSet => simpa [BarrettTopBitSelection.topBit] using hbound
  | @skipZero topBit rest positive bitZero restValid ih =>
      have htopPos : 0 < topBit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply positive
        apply u256_inj
        simpa using hz
      have hprevious : (topBit - ⟨1⟩).toNat = topBit.toNat - 1 := by
        change (UInt256.sub topBit ⟨1⟩).toNat = topBit.toNat - 1
        have hone : (⟨1⟩ : UInt256).toNat = 1 := by decide
        rw [usub_toNat (by rw [hone]; omega), hone]
      have hnextBound := barrettTopBitTest_zero_lt_pow byte topBit hstart hbound bitZero
      have hnextStart : (topBit - ⟨1⟩).toNat < 8 := by rw [hprevious]; omega
      have hnextBound' : (byte.land ⟨255⟩).toNat <
          2 ^ ((topBit - ⟨1⟩).toNat + 1) := by
        rw [hprevious, show topBit.toNat - 1 + 1 = topBit.toNat by omega]
        exact hnextBound
      exact ih hnextStart hnextBound'

/-- The read-only leading scan stops at the first nonzero trusted exponent byte, or proves that
all remaining bytes are zero. -/
theorem BarrettLeadingScanValid.modelAlignment
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    {baseSize exponentSize initialStart : Nat}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hexpLen : expLen = UInt256.ofNat exponentSize)
    (hexponentSize : exponentSize < UInt256.size)
    (hstartLe : initialStart ≤ exponentSize)
    (hstartNat : startByte.toNat = initialStart)
    (haddress : ∀ s, s < exponentSize →
      (exponentByteAddress exponent (UInt256.ofNat s)).toNat =
        exponent.toNat + 32 + s)
    (hpayloadConcrete : exponent.toNat + 32 + exponentSize + 31 ≤ mem.size)
    (haddress64 : exponent.toNat + 32 + exponentSize < 2 ^ 64)
    (hcalldataBound : 96 + baseSize + exponentSize < 2 ^ 64)
    (hsource : ∀ s, s < exponentSize →
      mem.readWithPadding (exponent.toNat + 32 + s) 1 =
        I.calldata.readWithPadding (96 + baseSize + s) 1) :
    (selected.isExhausted = true ∧ selected.startByte.toNat = exponentSize ∧
        ∀ s, initialStart ≤ s → s < exponentSize →
          Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1 = 0) ∨
      (selected.isExhausted = false ∧ selected.startByte.toNat < exponentSize ∧
        (∀ s, initialStart ≤ s → s < selected.startByte.toNat →
          Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1 = 0) ∧
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + selected.startByte.toNat) 1 ≠ 0) := by
  induction valid generalizing rValue initialStart with
  | @exhausted aw current guardZero =>
      left
      have hge : expLen.toNat ≤ current.toNat := by
        by_contra hnot
        have hone := ult_one (a := current) (b := expLen) (by omega)
        exact (by native_decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
          (hone.symm.trans guardZero)
      have hlenNat : expLen.toNat = exponentSize := by
        rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
      have hend : current.toNat = exponentSize := by omega
      refine ⟨rfl, hend, ?_⟩
      intro s hsStart hsEnd
      omega
  | @found aw current scanWord guardSet indexValid wordEq wordNonzero =>
      right
      have hcurrentLt : current.toNat < expLen.toNat := by
        by_contra hnot
        exact guardSet (ult_zero (by omega))
      have hlenNat : expLen.toNat = exponentSize := by
        rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
      have hstartLt : initialStart < exponentSize := by omega
      have hcurrentWord : current = UInt256.ofNat initialStart := by
        apply u256_inj
        rw [hstartNat, UInt256.toNat_ofNat_of_lt (lt_trans hstartLt hexponentSize)]
      have haddr := haddress initialStart hstartLt
      rw [← hcurrentWord] at haddr
      let read := exponent.toNat + 32 + initialStart
      have hword : read + 32 ≤ mem.size := by
        dsimp only [read]
        omega
      have hlengthInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
      have hdecoded := barrettExponentByteValue_toNat_eq_model_of_frame I mem mem
        (exponentArrayLengthAw aw exponent) exponent current read
        (96 + baseSize + initialStart) (by simpa only [read] using haddr)
        hlengthInvariant.covered hlengthInvariant.activeWordsFit hword
        (by dsimp only [read]; omega)
        (by omega) rfl (hsource initialStart hstartLt)
      have hcurrentNonzero : Model.bytesToNatPadded I.calldata
          (96 + baseSize + initialStart) 1 ≠ 0 := by
        intro hmodelZero
        have hbyteZero : barrettExponentByteValue mem
            (exponentArrayLengthAw aw exponent) exponent current = ⟨0⟩ := by
          apply u256_inj
          rw [hdecoded, hmodelZero]
          decide
        have hscanZero := (barrettScanMaskedWord_eq_zero_iff mem
          (exponentArrayLengthAw aw exponent) exponent current).2 hbyteZero
        exact wordNonzero (wordEq.trans hscanZero)
      refine ⟨rfl, ?_, ?_, ?_⟩
      · change current.toNat < exponentSize
        omega
      · intro s hsStart hsEnd
        simp only [BarrettLeadingScanSelection.startByte] at hsEnd
        omega
      · simpa [BarrettLeadingScanSelection.startByte, hstartNat] using hcurrentNonzero
  | @skipZero aw current scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have hcurrentLt : current.toNat < expLen.toNat := by
        by_contra hnot
        exact guardSet (ult_zero (by omega))
      have hlenNat : expLen.toNat = exponentSize := by
        rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
      have hstartLt : initialStart < exponentSize := by omega
      have hcurrentWord : current = UInt256.ofNat initialStart := by
        apply u256_inj
        rw [hstartNat, UInt256.toNat_ofNat_of_lt (lt_trans hstartLt hexponentSize)]
      have haddr := haddress initialStart hstartLt
      rw [← hcurrentWord] at haddr
      let read := exponent.toNat + 32 + initialStart
      have hword : read + 32 ≤ mem.size := by
        dsimp only [read]
        omega
      have hlengthInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
      have hdecoded := barrettExponentByteValue_toNat_eq_model_of_frame I mem mem
        (exponentArrayLengthAw aw exponent) exponent current read
        (96 + baseSize + initialStart) (by simpa only [read] using haddr)
        hlengthInvariant.covered hlengthInvariant.activeWordsFit hword
        (by dsimp only [read]; omega)
        (by omega) rfl (hsource initialStart hstartLt)
      have hscanZero : barrettScanMaskedWord mem (exponentArrayLengthAw aw exponent)
          exponent current = ⟨0⟩ := wordEq.symm.trans wordZero
      have hbyteZero := (barrettScanMaskedWord_eq_zero_iff mem
        (exponentArrayLengthAw aw exponent) exponent current).1 hscanZero
      have hmodelZero : Model.bytesToNatPadded I.calldata
          (96 + baseSize + initialStart) 1 = 0 := by
        have hnat := congrArg UInt256.toNat hbyteZero
        rw [hdecoded] at hnat
        simpa using hnat
      have hnextNat : (current + ⟨1⟩).toNat = initialStart + 1 := by
        rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide, hstartNat,
          Nat.mod_eq_of_lt (by omega)]
      have loaded := invariant.afterExponentByteLoad access.exponentFit
        (access.byteFit current guardSet)
      rcases ih loaded (by omega) hnextNat with hexhausted | hfound
      · left
        refine ⟨hexhausted.1, hexhausted.2.1, ?_⟩
        intro s hsStart hsEnd
        by_cases hs : s = initialStart
        · simpa [hs] using hmodelZero
        · exact hexhausted.2.2 s (by omega) hsEnd
      · right
        refine ⟨hfound.1, hfound.2.1, ?_, hfound.2.2.2⟩
        intro s hsStart hsEnd
        by_cases hs : s = initialStart
        · simpa [hs] using hmodelZero
        · exact hfound.2.2.1 s (by omega) hsEnd

/-- Removing a model prefix whose individual bytes are zero preserves the full field value. -/
theorem model_bytesToNatPadded_eq_suffix_of_zero_prefix
    (bs : ByteArray) (start width prefixLen : Nat)
    (hprefix : prefixLen ≤ width)
    (hzero : ∀ i, i < prefixLen →
      Model.bytesToNatPadded bs (start + i) 1 = 0) :
    Model.bytesToNatPadded bs start width =
      Model.bytesToNatPadded bs (start + prefixLen) (width - prefixLen) := by
  have hprefixZero := model_bytesToNatPadded_eq_zero_of_bytes bs start prefixLen hzero
  have hsplit := model_bytesToNatPadded_split bs start prefixLen (width - prefixLen)
  have hwidth : prefixLen + (width - prefixLen) = width := by omega
  rw [hwidth] at hsplit
  rw [hsplit, hprefixZero]
  simp

/-- The byte recorded by a valid fresh first-byte selection is its concrete exponent load. -/
theorem FreshBarrettByteValid.byte_eq
    {I : ExecutionEnv} {callFuel kWords fp : Nat} {r a n mu : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : FreshBarrettByteSelection}
    (valid : FreshBarrettByteValid I callFuel kWords fp r a n mu mem aw byteIdx
      exponent topBit expLen selected) :
    selected.byte =
      barrettExponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx := by
  cases valid with
  | unset guardTaken indexValid topBitValid bitCounterNonzero byteEq bitUnset
      squareValid restValid =>
      simpa [FreshBarrettByteSelection.byte] using byteEq
  | set valid =>
      simpa [FreshBarrettByteSelection.byte] using valid.byteEq

/-- Masking an already byte-sized EVM word by `0xff` leaves its natural value unchanged. -/
theorem u256_land_255_toNat_of_lt (word : UInt256) (hword : word.toNat < 256) :
    (word.land ⟨255⟩).toNat = word.toNat := by
  rw [Reasoning.Theory.uland_toNat, show (⟨255⟩ : UInt256).toNat = 255 by decide]
  change Nat.land word.toNat (2 ^ 8 - 1) = word.toNat
  rw [Reasoning.Theory.nat_land_mask_eq_mod, show 2 ^ 8 = 256 by decide,
    Nat.mod_eq_of_lt hword]

/-- The only calldata-side alignment contract needed to identify a fresh selected exponent path
with the trusted padded exponent field. It contains no modular-arithmetic result assumption. -/
inductive FreshBarrettModelAlignment (I : ExecutionEnv) (baseSize exponentSize : Nat)
    (byteFuel bitFuel callFuel kWords fp : Nat)
    (r a n mu exponent expLen : UInt256) (mem : ByteArray) (aw : UInt256) :
    FreshBarrettLoopSetupSelection → Prop where
  | allZero {scan : BarrettLeadingScanSelection}
      (exponentZero : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize = 0) :
      FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel callFuel kWords fp
        r a n mu exponent expLen mem aw (.allZero scan)
  | nonzero {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
      {first : FreshBarrettByteSelection} {rest : BarrettByteLoopSelection} {start : Nat}
      (firstSelected : selectFreshBarrettByte bitFuel callFuel scan.memory
        (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
        kWords fp scan.startByte exponent top.topBit r a n mu = some first)
      (restSelected : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
        first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩ expLen
        r a n mu = some rest)
      (startLt : start < exponentSize)
      (byteEq : (first.byte.land ⟨255⟩).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
      (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
      (byteBound : (first.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1))
      (suffixEq : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize =
        Model.bytesToNatPadded I.calldata (96 + baseSize + start)
          (exponentSize - start)) :
      FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel callFuel kWords fp
        r a n mu exponent expLen mem aw (.nonzero scan top first rest)

/-- Construct the complete model alignment from the selected fresh setup trace and one concrete
prepared exponent frame. -/
theorem selectFreshBarrettLoopSetup_modelAlignmentFramed
    {I : ExecutionEnv}
    {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    {baseSize exponentSize : Nat}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hexpLen : expLen = UInt256.ofNat exponentSize)
    (hexponentSize : exponentSize < UInt256.size)
    (haddress : ∀ s, s < exponentSize →
      (exponentByteAddress exponent (UInt256.ofNat s)).toNat =
        exponent.toNat + 32 + s)
    (hpayloadConcrete : exponent.toNat + 32 + exponentSize + 31 ≤ mem.size)
    (hpayloadBelow : exponent.toNat + 32 + exponentSize + 31 ≤ r.toNat)
    (haddress64 : exponent.toNat + 32 + exponentSize < 2 ^ 64)
    (hcalldataBound : 96 + baseSize + exponentSize < 2 ^ 64)
    (hsource : ∀ s, s < exponentSize →
      mem.readWithPadding (exponent.toNat + 32 + s) 1 =
        I.calldata.readWithPadding (96 + baseSize + s) 1)
    (hselect : selectFreshBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel
      kWords fp mem aw exponent r a n mu expLen = some selected) :
    FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel callFuel kWords fp
      r a n mu exponent expLen mem aw selected := by
  unfold selectFreshBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem
      (exponentArrayLengthAw aw exponent) exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have hinc : ∀ startByte, startByte.lt expLen ≠ ⟨0⟩ →
          startByte ≠ UInt256.lnot ⟨0⟩ := by
        intro startByte hguard hmax
        have hlt : startByte.toNat < expLen.toNat := by
          by_contra hnot
          exact hguard (ult_zero (by omega))
        have hlenNat : expLen.toNat = exponentSize := by
          rw [hexpLen, UInt256.toNat_ofNat_of_lt hexponentSize]
        have hmaxNat : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
          native_decide
        rw [hmax, hmaxNat] at hlt
        omega
      have scanStartInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
      rcases selectBarrettLeadingScan_validInvariantFramed scanStartInvariant access hinc
          hscan with ⟨scanValid, scanInvariant⟩
      have scanAccess : BarrettExponentAccessFrame scan.memory exponent expLen r := by
        simpa only [scanValid.memoryEq] using access
      have scanSource : ∀ s, s < exponentSize →
          scan.memory.readWithPadding (exponent.toNat + 32 + s) 1 =
            I.calldata.readWithPadding (96 + baseSize + s) 1 := by
        intro s hs
        rw [scanValid.memoryEq]
        exact hsource s hs
      have scanConcrete : exponent.toNat + 32 + exponentSize + 31 ≤
          scan.memory.size := by simpa only [scanValid.memoryEq] using hpayloadConcrete
      have scanModel :=
        Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.modelAlignment
          (initialStart := 0) scanValid scanStartInvariant access hexpLen hexponentSize
          (by omega) (by decide) haddress hpayloadConcrete haddress64 hcalldataBound hsource
      simp only [hscan] at hselect
      by_cases hexhausted : scan.isExhausted = true
      · simp only [hexhausted, if_true, Option.some.injEq] at hselect
        subst selected
        rcases scanModel with hall | hfound
        · apply FreshBarrettModelAlignment.allZero
          apply model_bytesToNatPadded_eq_zero_of_bytes
          intro i hi
          have hz := hall.2.2 i (by omega) hi
          simpa [Nat.add_assoc] using hz
        · simp [hexhausted] at hfound
      · have hnotExhausted : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hnotExhausted, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
        let topByte := barrettExponentByteValue scan.memory
          (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel topByte ⟨7⟩ with
        | none => simp [aw0, topByte, htop] at hselect
        | some top =>
            cases hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory aw2
                kWords fp scan.startByte exponent top.topBit r a n mu with
            | none => simp [aw0, aw2, topByte, htop, hfirst] at hselect
            | some first =>
                cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
                    first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩
                    expLen r a n mu with
                | none => simp [aw0, aw2, topByte, htop, hfirst, hrest] at hselect
                | some rest =>
                    simp [aw0, aw2, topByte, htop, hfirst, hrest] at hselect
                    subst selected
                    rcases scanModel with hall | hfound
                    · simp [hnotExhausted] at hall
                    · have topValid := selectBarrettTopBit_valid htop
                      have htopLe : top.topBit.toNat ≤ 7 := by
                        simpa using topValid.topBit_le
                      have hguard := scanValid.finalGuardSet hnotExhausted
                      have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
                        (by native_decide)
                      have topLoadInvariant := freeInvariant.afterExponentByteLoad
                        scanAccess.exponentFit (scanAccess.byteFit scan.startByte hguard)
                      have hlength : exponentArrayLength scan.memory aw2 exponent = expLen :=
                        exponentArrayLength_eq_of_header topLoadInvariant.covered
                          topLoadInvariant.activeWordsFit scanAccess.headerConcrete
                          scanAccess.header
                      have hindex :
                          (scan.startByte.lt
                            (exponentArrayLength scan.memory aw2 exponent)).isZero = ⟨0⟩ := by
                        rw [hlength]
                        exact isZero_eq_zero_of_ne hguard
                      have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
                        apply ugt_zero
                        rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                          Nat.mod_eq_of_lt (by
                            have hs : 8 < UInt256.size := by decide
                            omega)]
                        omega
                      have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
                        intro hz
                        have hzNat := congrArg UInt256.toNat hz
                        rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                          Nat.mod_eq_of_lt (by
                            have hs : 8 < UInt256.size := by decide
                            omega)] at hzNat
                        simp at hzNat
                      rcases selectFreshBarrettByte_validInvariantReadBelow topLoadInvariant
                          hguard hindex htopGuard hcounter scanAccess.exponentFit
                          (scanAccess.byteFit scan.startByte hguard) scanAccess.exponentBase
                          scanAccess.exponentBelowAccumulator
                          (by simpa only [aw2] using hfirst) with
                        ⟨firstValue, firstValid, firstInvariant, headerFrame⟩
                      have firstAccess : BarrettExponentAccessFrame first.memory exponent
                          expLen r := {
                        scanAccess with
                        headerConcrete := firstInvariant.exponentHeaderConcrete
                          scanAccess.exponentBelowAccumulator
                        header := headerFrame.trans scanAccess.header }
                      let start := scan.startByte.toNat
                      have hstartLt : start < exponentSize := by
                        dsimp only [start]
                        exact hfound.2.1
                      have hstartWord : scan.startByte = UInt256.ofNat start := by
                        apply u256_inj
                        rw [UInt256.toNat_ofNat_of_lt (lt_trans hstartLt hexponentSize)]
                      have haddr := haddress start hstartLt
                      rw [← hstartWord] at haddr
                      let read := exponent.toNat + 32 + start
                      have hword : read + 32 ≤ scan.memory.size := by
                        dsimp only [read]
                        omega
                      have firstLengthInvariant :=
                        topLoadInvariant.afterExponentArrayLengthLoad scanAccess.exponentFit
                      have hfirstDecoded :=
                        barrettExponentByteValue_toNat_eq_model_of_frame I scan.memory mem
                          (exponentArrayLengthAw aw2 exponent) exponent scan.startByte read
                          (96 + baseSize + start) (by simpa only [read] using haddr)
                          firstLengthInvariant.covered firstLengthInvariant.activeWordsFit hword
                          (by dsimp only [read]; omega) (by omega)
                          (by rw [scanValid.memoryEq]) (hsource start hstartLt)
                      have hfirstNat : first.byte.toNat =
                          Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1 := by
                        rw [Modexp.MultiLimbBarrettResultSemantic.FreshBarrettByteValid.byte_eq
                          firstValid]
                        exact hfirstDecoded
                      have hfirstLt : first.byte.toNat < 256 := by
                        rw [hfirstNat]
                        have h := model_bytesToNatPadded_lt_pow I.calldata
                          (96 + baseSize + start) 1
                        simpa using h
                      have hfirstByte : (first.byte.land ⟨255⟩).toNat =
                          Model.bytesToNatPadded I.calldata
                            (96 + baseSize + start) 1 := by
                        rw [u256_land_255_toNat_of_lt first.byte hfirstLt, hfirstNat]
                      have topLengthInvariant :=
                        freeInvariant.afterExponentArrayLengthLoad scanAccess.exponentFit
                      have htopDecoded :=
                        barrettExponentByteValue_toNat_eq_model_of_frame I scan.memory mem
                          (exponentArrayLengthAw aw0 exponent) exponent scan.startByte read
                          (96 + baseSize + start) (by simpa only [read] using haddr)
                          topLengthInvariant.covered topLengthInvariant.activeWordsFit hword
                          (by dsimp only [read]; omega) (by omega)
                          (by rw [scanValid.memoryEq]) (hsource start hstartLt)
                      have htopLt : topByte.toNat < 256 := by
                        rw [htopDecoded]
                        have h := model_bytesToNatPadded_lt_pow I.calldata
                          (96 + baseSize + start) 1
                        simpa using h
                      have htopMask : (topByte.land ⟨255⟩).toNat =
                          Model.bytesToNatPadded I.calldata
                            (96 + baseSize + start) 1 := by
                        rw [u256_land_255_toNat_of_lt topByte htopLt, htopDecoded]
                      have htopBound :=
                        Modexp.MultiLimbBarrettResultSemantic.BarrettTopBitValid.byte_lt_selected_pow
                          topValid (by decide) (by
                            rw [htopMask]
                            have hm := model_bytesToNatPadded_lt_pow I.calldata
                              (96 + baseSize + start) 1
                            simpa using hm)
                      have hbyteBound : (first.byte.land ⟨255⟩).toNat <
                          2 ^ (top.topBit.toNat + 1) := by
                        rw [hfirstByte]
                        rw [htopMask] at htopBound
                        exact htopBound
                      have hnextIdx : (scan.startByte + ⟨1⟩).toNat = start + 1 := by
                        rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                          Nat.mod_eq_of_lt (by omega)]
                      have hnextFrame : ∀ s, s < exponentSize →
                          first.memory.readWithPadding (exponent.toNat + 32 + s) 32 =
                            mem.readWithPadding (exponent.toNat + 32 + s) 32 := by
                        intro s hs
                        let read' := exponent.toNat + 32 + s
                        have hs96 : 96 ≤ read' := by
                          dsimp only [read']
                          exact le_trans scanAccess.exponentBase (by omega)
                        have hsBelow : read' + 32 ≤ r.toNat := by
                          dsimp only [read']
                          omega
                        rcases selectFreshBarrettByte_validInvariantReadBelow topLoadInvariant
                            hguard hindex htopGuard hcounter scanAccess.exponentFit
                            (scanAccess.byteFit scan.startByte hguard) hs96 hsBelow
                            (by simpa only [aw2] using hfirst) with
                          ⟨_, _, _, selectedFrame⟩
                        exact selectedFrame.trans (by rw [scanValid.memoryEq])
                      have restMatches := selectBarrettByteLoop_matches_of_frame firstInvariant
                        firstAccess hexpLen hexponentSize (by omega) hnextIdx (by decide)
                        haddress hpayloadBelow hcalldataBound hsource hnextFrame hrest
                      have hsuffix := model_bytesToNatPadded_eq_suffix_of_zero_prefix
                        I.calldata (96 + baseSize) exponentSize start (by omega) (by
                          intro i hi
                          have hz := hfound.2.2.1 i (by omega) (by simpa only [start] using hi)
                          simpa [Nat.add_assoc] using hz)
                      exact .nonzero (by simpa only [aw2] using hfirst) hrest hstartLt
                        hfirstByte restMatches hbyteBound hsuffix

/-- A concrete exponent frame and allocator header make the complete fresh selector valid.
The guard callbacks required by the executable selector are derived from the selected leading
scan itself, rather than supplied as arbitrary path assumptions. -/
theorem selectFreshBarrettLoopSetup_validInvariantFramedAllocated
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hfreeRead : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hselect : selectFreshBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel
      kWords fp mem aw exponent r a n mu expLen = some selected) :
    FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected /\
      (match selected with
      | .allZero _ => True
      | .nonzero _ _ _ _ => exists finalValue,
          BarrettExponentInvariant I selected.memory selected.activeWords kWords fp
            r a n mu finalValue baseValue nValue) := by
  have hinc : ∀ startByte, startByte.lt expLen ≠ ⟨0⟩ →
      startByte ≠ UInt256.lnot ⟨0⟩ := by
    intro startByte hguard hmax
    have hlt : startByte.toNat < expLen.toNat := by
      by_contra hnot
      exact hguard (ult_zero (by omega))
    have hmaxNat : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
      native_decide
    have hlenFit : expLen.toNat < UInt256.size := by
      simpa [UInt256.toNat] using expLen.val.isLt
    rw [hmax, hmaxNat] at hlt
    omega
  have scanStartInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
  have hexhausted : ∀ scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent)
        ⟨0⟩ scan →
      scan.isExhausted = true → scan.startByte.eq expLen ≠ ⟨0⟩ := by
    intro scan scanValid hexhausted
    have hword := (scanValid.exhaustionStart (by simp)).1 hexhausted
    rw [hword, uInt256_eq_self]
    decide
  have hnonexhausted : ∀ scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent)
        ⟨0⟩ scan →
      scan.isExhausted = false → scan.startByte.eq expLen = ⟨0⟩ := by
    intro scan scanValid hnonexhausted
    have hne := (scanValid.exhaustionStart (by simp)).2 hnonexhausted
    apply uInt256_eq_zero_of_ne
    intro hone
    exact hne (uInt256_eq_one_eq hone)
  have hfree : ∀ scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent)
        ⟨0⟩ scan →
      scan.isExhausted = false →
      readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp := by
    intro scan scanValid _
    have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
      access.exponentFit access.byteFit
    have hword : (⟨64⟩ : UInt256).toNat + 32 ≤ scan.memory.size := by
      simpa using scanInvariant.memorySize
    have hbelow := wordBelowActive_of_covered scan.memory scan.activeWords ⟨64⟩
      scanInvariant.covered scanInvariant.activeWordsFit hword
    have hfreeRead' : mem.readWithPadding (⟨64⟩ : UInt256).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat fp) := by
      simpa using hfreeRead
    unfold readWord
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩), scanValid.memoryEq, hfreeRead',
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  have result := selectFreshBarrettLoopSetup_validInvariantFramed invariant access hinc
    hexhausted hnonexhausted hfree hselect
  constructor
  · exact result.1
  · cases selected <;> simpa using result.2

/-- A complete selected fresh exponent trace preserves every fixed word below the accumulator.
The leading scan is read-only; every square and multiply writes only in the reused scratch frame. -/
theorem selectFreshBarrettLoopSetup_readBelowFramed
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue read : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hread : 96 ≤ read) (hbelow : read + 32 ≤ r.toNat)
    (hselect : selectFreshBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel
      kWords fp mem aw exponent r a n mu expLen = some selected) :
    selected.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hinc : ∀ startByte, startByte.lt expLen ≠ ⟨0⟩ →
      startByte ≠ UInt256.lnot ⟨0⟩ := by
    intro startByte hguard hmax
    have hlt : startByte.toNat < expLen.toNat := by
      by_contra hnot
      exact hguard (ult_zero (by omega))
    have hmaxNat : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
      native_decide
    have hlenFit : expLen.toNat < UInt256.size := by
      simpa [UInt256.toNat] using expLen.val.isLt
    rw [hmax, hmaxNat] at hlt
    omega
  unfold selectFreshBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem
      (exponentArrayLengthAw aw exponent) exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have scanStartInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
      rcases selectBarrettLeadingScan_validInvariantFramed scanStartInvariant access hinc
          hscan with ⟨scanValid, scanInvariant⟩
      have scanAccess : BarrettExponentAccessFrame scan.memory exponent expLen r := by
        simpa only [scanValid.memoryEq] using access
      simp only [hscan] at hselect
      by_cases hexhausted : scan.isExhausted = true
      · simp only [hexhausted, if_true, Option.some.injEq] at hselect
        subst selected
        simpa [FreshBarrettLoopSetupSelection.memory] using
          congrArg (fun memory : ByteArray => memory.readWithPadding read 32)
            scanValid.memoryEq
      · have hnonexhausted : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hnonexhausted, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
        let byte := barrettExponentByteValue scan.memory
          (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel byte ⟨7⟩ with
        | none => simp [aw0, byte, htop] at hselect
        | some top =>
            have topValid := selectBarrettTopBit_valid htop
            have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  have htopLe : top.topBit.toNat ≤ 7 := by simpa using topValid.topBit_le
                  omega)]
              have htopLe : top.topBit.toNat ≤ 7 := by simpa using topValid.topBit_le
              omega
            have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
              intro hz
              have hzNat := congrArg UInt256.toNat hz
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  have htopLe : top.topBit.toNat ≤ 7 := by simpa using topValid.topBit_le
                  omega)] at hzNat
              simp at hzNat
            have hguard := scanValid.finalGuardSet hnonexhausted
            have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
              (by native_decide)
            have topLoadInvariant := freeInvariant.afterExponentByteLoad
              scanAccess.exponentFit (scanAccess.byteFit scan.startByte hguard)
            have hlength : exponentArrayLength scan.memory aw2 exponent = expLen :=
              exponentArrayLength_eq_of_header topLoadInvariant.covered
                topLoadInvariant.activeWordsFit scanAccess.headerConcrete scanAccess.header
            have hindex :
                (scan.startByte.lt (exponentArrayLength scan.memory aw2 exponent)).isZero =
                  ⟨0⟩ := by
              rw [hlength]
              exact isZero_eq_zero_of_ne hguard
            cases hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory aw2
                kWords fp scan.startByte exponent top.topBit r a n mu with
            | none => simp [aw0, aw2, byte, htop, hfirst] at hselect
            | some first =>
                cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
                    first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩
                    expLen r a n mu with
                | none => simp [aw0, aw2, byte, htop, hfirst, hrest] at hselect
                | some rest =>
                    simp only [aw0, aw2, byte, htop, hfirst, hrest,
                      Option.some.injEq] at hselect
                    subst selected
                    rcases selectFreshBarrettByteAndLoop_validInvariantFramedReadBelow
                        topLoadInvariant hguard hindex htopGuard hcounter scanAccess hread hbelow
                        (by simpa only [aw2] using hfirst) hrest with
                      ⟨_, _, _, _, _, _, frame⟩
                    exact frame.trans (by rw [scanValid.memoryEq])

/-- Every aligned fresh selector computes the full trusted modular exponent from the concrete
initial Barrett invariant. -/
theorem FreshBarrettLoopSetupValid.value_eq_full_model_powInvariant
    {I : ExecutionEnv}
    {baseSize exponentSize byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen
      mem aw selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (alignment : FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel
      callFuel kWords fp r a n mu exponent expLen mem aw selected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hinitial : rValue = baseValue ^ 0 % nValue) :
    barrettAccumulatorValue kWords r selected.memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % nValue := by
  cases alignment with
  | allZero exponentZero =>
      exact FreshBarrettLoopSetupValid.allZero_value_eq_model_pow valid
        (by rw [invariant.rValueEq, hinitial]) exponentZero
  | nonzero firstSelected restSelected startLt byteEq restMatches byteBound suffixEq =>
      exact FreshBarrettLoopSetupValid.nonzero_value_eq_full_model_powInvariant valid
        invariant hexponentFit haccess hinitial firstSelected restSelected startLt byteEq
        restMatches byteBound suffixEq

/-- Full model value theorem using the concrete exponent access frame. -/
theorem FreshBarrettLoopSetupValid.value_eq_full_model_powInvariantFramed
    {I : ExecutionEnv}
    {baseSize exponentSize byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen
      mem aw selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (alignment : FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel
      callFuel kWords fp r a n mu exponent expLen mem aw selected)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hinitial : rValue = baseValue ^ 0 % nValue) :
    barrettAccumulatorValue kWords r selected.memory =
      baseValue ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % nValue := by
  cases alignment with
  | allZero exponentZero =>
      exact FreshBarrettLoopSetupValid.allZero_value_eq_model_pow valid
        (by rw [invariant.rValueEq, hinitial]) exponentZero
  | @nonzero scan top first rest start firstSelected restSelected startLt byteEq restMatches
      byteBound suffixEq =>
      cases valid with
      | nonzero scanValid nonexhausted indexValid freePointer topValid firstValid restValid =>
          have hscanNonexhausted : scan.isExhausted = false := by
            cases hscan : scan.isExhausted with
            | false => rfl
            | true =>
                exact False.elim (firstValid.guardTaken
                  (BarrettLeadingScanValid.finalGuardZero scanValid (by simpa using hscan)))
          have hsuffix :=
            BarrettLeadingScanValid.fresh_nonzero_value_eq_model_powInvariantFramed
              scanValid hscanNonexhausted topValid invariant access hinitial firstSelected
              restSelected startLt byteEq restMatches byteBound
          rw [suffixEq]
          exact hsuffix

/-- The fresh selector's final memory geometry comes from the same concrete invariant as its
arithmetic value. This removes coverage, active-word fit, and accumulator-header assumptions from
the serializer boundary; only the separately preallocated result object's frame remains external. -/
theorem FreshBarrettLoopSetupValid.finalGeometry
    {I : ExecutionEnv}
    {baseSize exponentSize byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen
      mem aw selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (alignment : FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel
      callFuel kWords fp r a n mu exponent expLen mem aw selected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.readWithPadding r.toNat 32 =
        UInt256.toByteArray (UInt256.ofNat kWords) := by
  cases selected with
  | allZero scan =>
      cases valid with
      | allZero scanValid exhausted =>
        cases alignment with
        | allZero exponentZero =>
          have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
          have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
            hexponentFit (fun idx hguard =>
              (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
          refine ⟨?_, ?_, ?_⟩
          · simpa [FreshBarrettLoopSetupSelection.memory,
              FreshBarrettLoopSetupSelection.activeWords] using scanInvariant.covered
          · simpa [FreshBarrettLoopSetupSelection.activeWords] using
              scanInvariant.activeWordsFit
          · simpa [FreshBarrettLoopSetupSelection.memory] using scanInvariant.rHeader
  | nonzero scan top first rest =>
      cases valid with
      | nonzero scanValid nonexhausted indexValid freePointer topValid firstValid restValid =>
        cases alignment with
        | nonzero firstSelected restSelected startLt byteEq restMatches byteBound suffixEq =>
          have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
          have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
            hexponentFit (fun idx hguard =>
              (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
          have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩) (by native_decide)
          have hscanNonexhausted : scan.isExhausted = false := by
            cases hscan : scan.isExhausted with
            | false => rfl
            | true =>
                exact False.elim (firstValid.guardTaken
                  (BarrettLeadingScanValid.finalGuardZero scanValid (by simpa using hscan)))
          have hguard := scanValid.finalGuardSet hscanNonexhausted
          let aw0 := readWords1 scan.activeWords ⟨64⟩
          let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
          rcases haccess scan.memory aw0 scan.startByte hguard with
            ⟨topIndex, topExponentFit, topByteFit⟩
          have topLoadInvariant := freeInvariant.afterExponentByteLoad topExponentFit topByteFit
          rcases haccess scan.memory aw2 scan.startByte hguard with
            ⟨firstIndex, firstExponentFit, firstByteFit⟩
          have htopBound : top.topBit.toNat ≤ 7 := by
            simpa using topValid.topBit_le
          have htopGuard :
              top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
            apply ugt_zero
            rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
              Nat.mod_eq_of_lt (by
                have hs : 8 < UInt256.size := by decide
                omega)]
            omega
          have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
            intro hz
            have hzNat := congrArg UInt256.toNat hz
            rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
              Nat.mod_eq_of_lt (by
                have hs : 8 < UInt256.size := by decide
                omega)] at hzNat
            simp at hzNat
          rcases selectFreshBarrettByte_validInvariant topLoadInvariant hguard firstIndex
              htopGuard hcounter firstExponentFit firstByteFit
              (by simpa only [aw0, aw2] using firstSelected) with
            ⟨firstValue, selectedFirstValid, firstInvariant⟩
          rcases selectBarrettByteLoop_validInvariant firstInvariant (by decide) haccess
              restSelected with
            ⟨finalValue, selectedRestValid, finalInvariant⟩
          simpa [FreshBarrettLoopSetupSelection.memory,
            FreshBarrettLoopSetupSelection.activeWords] using
            ⟨finalInvariant.covered, finalInvariant.activeWordsFit, finalInvariant.rHeader⟩

/-- Final serializer geometry using the same concrete exponent access frame as execution. -/
theorem FreshBarrettLoopSetupValid.finalGeometryFramed
    {I : ExecutionEnv}
    {baseSize exponentSize byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen
      mem aw selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (alignment : FreshBarrettModelAlignment I baseSize exponentSize byteFuel bitFuel
      callFuel kWords fp r a n mu exponent expLen mem aw selected)
    (access : BarrettExponentAccessFrame mem exponent expLen r) :
    MemoryCovered selected.memory selected.activeWords /\
      selected.activeWords.toNat * 32 < UInt256.size /\
      selected.memory.readWithPadding r.toNat 32 =
        UInt256.toByteArray (UInt256.ofNat kWords) := by
  cases selected with
  | allZero scan =>
      cases valid with
      | allZero scanValid exhausted =>
        cases alignment with
        | allZero exponentZero =>
          have scanStartInvariant := invariant.afterExponentArrayLengthLoad
            access.exponentFit
          have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
            access.exponentFit access.byteFit
          refine ⟨?_, ?_, ?_⟩
          · simpa [FreshBarrettLoopSetupSelection.memory,
              FreshBarrettLoopSetupSelection.activeWords] using scanInvariant.covered
          · simpa [FreshBarrettLoopSetupSelection.activeWords] using
              scanInvariant.activeWordsFit
          · simpa [FreshBarrettLoopSetupSelection.memory] using scanInvariant.rHeader
  | nonzero scan top first rest =>
      cases valid with
      | nonzero scanValid nonexhausted indexValid freePointer topValid firstValid restValid =>
        cases alignment with
        | nonzero firstSelected restSelected startLt byteEq restMatches byteBound suffixEq =>
          have scanStartInvariant := invariant.afterExponentArrayLengthLoad
            access.exponentFit
          have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
            access.exponentFit access.byteFit
          have scanAccess : BarrettExponentAccessFrame scan.memory exponent expLen r := by
            simpa only [Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.memory_eq
              scanValid] using access
          have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
            (by native_decide)
          have hscanNonexhausted : scan.isExhausted = false := by
            cases hscan : scan.isExhausted with
            | false => rfl
            | true =>
                exact False.elim (firstValid.guardTaken
                  (BarrettLeadingScanValid.finalGuardZero scanValid (by simpa using hscan)))
          have hguard := scanValid.finalGuardSet hscanNonexhausted
          let aw0 := readWords1 scan.activeWords ⟨64⟩
          let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
          have topLoadInvariant := freeInvariant.afterExponentByteLoad
            scanAccess.exponentFit (scanAccess.byteFit scan.startByte hguard)
          have hlength : exponentArrayLength scan.memory aw2 exponent = expLen :=
            exponentArrayLength_eq_of_header topLoadInvariant.covered
              topLoadInvariant.activeWordsFit scanAccess.headerConcrete scanAccess.header
          have firstIndex :
              (scan.startByte.lt (exponentArrayLength scan.memory aw2 exponent)).isZero =
                ⟨0⟩ := by
            rw [hlength]
            exact isZero_eq_zero_of_ne hguard
          have htopBound : top.topBit.toNat <= 7 := by simpa using topValid.topBit_le
          have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
            apply ugt_zero
            rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
              Nat.mod_eq_of_lt (by
                have hs : 8 < UInt256.size := by decide
                omega)]
            omega
          have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
            intro hz
            have hzNat := congrArg UInt256.toNat hz
            rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
              Nat.mod_eq_of_lt (by
                have hs : 8 < UInt256.size := by decide
                omega)] at hzNat
            simp at hzNat
          rcases selectFreshBarrettByteAndLoop_validInvariantFramed topLoadInvariant hguard
              firstIndex htopGuard hcounter scanAccess
              (by simpa only [aw0, aw2] using firstSelected) restSelected with
            ⟨_, _, _, _, finalInvariant, _⟩
          simpa [FreshBarrettLoopSetupSelection.memory,
            FreshBarrettLoopSetupSelection.activeWords] using
            ⟨finalInvariant.covered, finalInvariant.activeWordsFit, finalInvariant.rHeader⟩

/-- One representable EVM word read cannot decrease the active-memory word count. -/
theorem readWords1_active_mono
    (aw ptr : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hptrFit : ptr.toNat + 32 + 31 < UInt256.size) :
    aw.toNat ≤ (readWords1 aw ptr).toNat := by
  have hmul := machineM_mul32_lt_size hawFit hptrFit
  have hmachine : MachineState.M aw.toNat ptr.toNat 32 < UInt256.size := by
    omega
  unfold readWords1
  rw [UInt256.toNat_ofNat_of_lt hmachine]
  simp [MachineState.M]

/-- The read-only leading exponent scan preserves or expands the initial active-memory extent. -/
theorem BarrettLeadingScanValid.initialActive_le
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent expLen startByte r a n mu : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r) :
    aw.toNat ≤ selected.activeWords.toNat := by
  induction valid with
  | exhausted => simp [BarrettLeadingScanSelection.activeWords]
  | @found aw startByte scanWord guardSet indexValid wordEq wordNonzero =>
      have hfirst := readWords1_active_mono aw exponent invariant.activeWordsFit
        access.exponentFit
      have hfirstCoverage := readWords1_coverage mem aw exponent invariant.covered
        invariant.activeWordsFit access.exponentFit
      have hsecond := readWords1_active_mono (exponentArrayLengthAw aw exponent)
        (exponentByteAddress exponent startByte)
        (by simpa only [exponentArrayLengthAw] using hfirstCoverage.2)
        (access.byteFit startByte guardSet)
      simpa only [BarrettLeadingScanSelection.activeWords, exponentByteLoadAw,
        exponentArrayLengthAw] using hfirst.trans hsecond
  | @skipZero aw startByte scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have hfirst := readWords1_active_mono aw exponent invariant.activeWordsFit
        access.exponentFit
      have hfirstCoverage := readWords1_coverage mem aw exponent invariant.covered
        invariant.activeWordsFit access.exponentFit
      have hsecond := readWords1_active_mono (exponentArrayLengthAw aw exponent)
        (exponentByteAddress exponent startByte)
        (by simpa only [exponentArrayLengthAw] using hfirstCoverage.2)
        (access.byteFit startByte guardSet)
      have hload : aw.toNat ≤ (exponentByteLoadAw aw exponent startByte).toNat := by
        simpa only [exponentByteLoadAw, exponentArrayLengthAw] using hfirst.trans hsecond
      have loadedInvariant := invariant.afterExponentByteLoad access.exponentFit
        (access.byteFit startByte guardSet)
      exact hload.trans (ih loadedInvariant)

/-- Convert a preserved raw array header into the guarded value consumed by `limbsToBytes`. -/
theorem headerValue_eq_of_rawHeader
    (mem : ByteArray) (aw limbs : UInt256) (kWords : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hraw : mem.readWithPadding limbs.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat kWords)) :
    headerValue mem aw limbs = UInt256.ofNat kWords := by
  apply u256_inj
  unfold headerValue
  rw [show readWord mem aw limbs =
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem limbs.toNat) by
    simpa only using
      (Modexp.MultiLimbSchoolbookMulTrace.readWord_eq_memoryWordOf_covered_padded
        mem aw limbs hcovered hawFit)]
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem limbs.toNat)]
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [hraw, fromByteArrayBigEndian_toByteArray]

/-- The nonzero selector computes the pure power for the entire exponent once the leading-zero
scan is connected to the significant calldata suffix. -/
theorem BarrettLoopSetupValid.nonzero_value_eq_full_model_pow
    {I : ExecutionEnv} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
    {byte : BarrettByteSelection} {rest : BarrettByteLoopSelection}
    {baseSize exponentSize start modulus base : Nat}
    (valid : BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
      (.nonzero scan top (.next byte rest)))
    (hmodulus : 0 < modulus)
    (hinitial : barrettAccumulatorValue kWords r mem = base ^ 0 % modulus)
    (hsquare : BarrettSquareGeometryProvider I callFuel kWords fp r n mu modulus)
    (hmultiply : BarrettMultiplyGeometryProvider I callFuel kWords fp r a n mu base modulus)
    (htop : top.topBit.toNat < 8)
    (startLt : start < exponentSize)
    (byteEq : (byte.byte.land ⟨255⟩).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start) 1)
    (restMatches : BarrettByteLoopMatches I baseSize exponentSize (start + 1) rest)
    (hbyte : (byte.byte.land ⟨255⟩).toNat < 2 ^ (top.topBit.toNat + 1))
    (hsuffix : Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize =
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
        (exponentSize - start)) :
    barrettAccumulatorValue kWords r
        (BarrettLoopSetupSelection.nonzero scan top (.next byte rest)).memory =
      base ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize % modulus := by
  rw [hsuffix]
  exact Modexp.MultiLimbBarrettResultSemantic.BarrettLoopSetupValid.nonzero_value_eq_model_pow
    valid hmodulus hinitial hsquare hmultiply htop startLt byteEq restMatches hbyte

/-- If every concrete source load has the expected value, the recursive full-word serializer
source list is exactly the corresponding memory limb list. -/
theorem fullSourceWords_eq_memoryWordsFrom_of_values
    (mem : ByteArray) (ptr : Nat) (aw limbs dataLen out : UInt256)
    (count : Nat) (state : FullState)
    (hsource : ∀ q, q < count →
      sourceValue (iterate aw limbs dataLen out q state).memory aw
          (iterate aw limbs dataLen out q state).index limbs =
        UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat mem (ptr + 32 * q))) :
    fullSourceWords aw limbs dataLen out count state = memoryWordsFrom mem ptr count := by
  induction count generalizing state ptr with
  | zero => rfl
  | succ count ih =>
      rw [fullSourceWords, memoryWordsFrom]
      have hhead := hsource 0 (by omega)
      simp only [iterate, Nat.mul_zero, Nat.add_zero] at hhead
      rw [hhead]
      congr 1
      apply ih
      intro q hq
      have htail := hsource (q + 1) (by omega)
      rw [show iterate aw limbs dataLen out (q + 1) state =
        iterate aw limbs dataLen out q (advance aw limbs dataLen out state) by rfl] at htail
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htail

/-- In-bounds full-word output writes preserve the concrete memory size. -/
theorem iterate_size_eq_of_inBounds
    (aw limbs dataLen out : UInt256) (count : Nat) (state : FullState)
    (hin : ∀ q, q < count →
      let current := iterate aw limbs dataLen out q state
      (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size) :
    (iterate aw limbs dataLen out count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance aw limbs dataLen out state
      let dest := (outputAddress state.index dataLen out).toNat
      have hfirst : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hin 0 (by omega)
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp only [next, advance, dest]
        exact toByteArray_write32_size_of_le state.memory _ dest state.memory.size
          state.memory.size rfl (by omega) (by simp; omega)
      have hin' : ∀ q, q < count →
          let current := iterate aw limbs dataLen out q next
          (outputAddress current.index dataLen out).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hin (q + 1) (by omega)
      rw [iterate]
      exact (ih next hin').trans hnextSize

/-- The initial full-word writes are all in bounds when the complete output range is allocated. -/
theorem initial_fullWrites_inBounds
    {mem : ByteArray} {aw limbs out : UInt256} {dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size) :
    ∀ q, q < dataLen / 32 →
      let current := iterate aw limbs (UInt256.ofNat dataLen) out q (initialState mem)
      (outputAddress current.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        current.memory.size := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro hq
      have hprior : ∀ j, j < q →
          let current := iterate aw limbs (UInt256.ofNat dataLen) out j (initialState mem)
          (outputAddress current.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
            current.memory.size := by
        intro j hj
        exact ih j hj (by omega)
      have hsize := iterate_size_eq_of_inBounds aw limbs (UInt256.ofNat dataLen) out q
        (initialState mem) hprior
      dsimp only
      rw [hsize]
      change _ ≤ mem.size
      rw [initial_index]
      rw [outputAddress_toNat hlen hq haddr]
      omega

/-- Full-word serializer source reads still see the original Barrett accumulator even though lower
output addresses have already been written. -/
theorem fullSourceWords_eq_accumulator
    {mem : ByteArray} {aw out : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * (dataLen / 32) < UInt256.size)
    (houtBefore : out.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvalid : ∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q (initialState mem))) :
    fullSourceWords aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out
        (dataLen / 32) (initialState mem) =
      memoryWordsFrom mem (fp + 32) (dataLen / 32) := by
  have hfullIn := initial_fullWrites_inBounds (aw := aw)
    (limbs := UInt256.ofNat fp) (mem := mem) (out := out) (dataLen := dataLen)
    hlen haddr hmem
  apply fullSourceWords_eq_memoryWordsFrom_of_values
  intro q hq
  let current := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
    (initialState mem)
  have hindex : current.index = UInt256.ofNat q := by
    exact initial_index aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q mem
  have hsourceAddr :
      (sourceAddress current.index (UInt256.ofNat fp)).toNat = fp + 32 + 32 * q := by
    rw [hindex]
    exact sourceAddress_toNat (by omega)
  have hsize : current.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      out q (initialState mem) (fun j hj => hfullIn j (by omega))
  have hcurrentCovered : MemoryCovered current.memory aw := by
    unfold MemoryCovered at hcovered ⊢
    rw [hsize]
    exact hcovered
  have hguarded : MultiLimbArithmeticTrace.readWord current.memory aw
        (sourceAddress current.index (UInt256.ofNat fp)) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat current.memory
        (sourceAddress current.index (UInt256.ofNat fp)).toNat) := by
    simpa only using
      (Modexp.MultiLimbSchoolbookMulTrace.readWord_eq_memoryWordOf_covered_padded
        current.memory aw (sourceAddress current.index (UInt256.ofNat fp))
        hcurrentCovered hawFit)
  have hbelow : ∀ j, j < q →
      let prior := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out j
        (initialState mem)
      (outputAddress prior.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        (sourceAddress current.index (UInt256.ofNat fp)).toNat := by
    intro j hj
    dsimp only
    rw [initial_index]
    rw [outputAddress_toNat hlen (by omega) haddr, hsourceAddr]
    omega
  have hframe := iterate_read_above aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
    (initialState mem) (sourceAddress current.index (UInt256.ofNat fp)).toNat
    (fun j hj => hfullIn j (by omega)) hbelow
  have hmemoryWord : MultiLimbMemoryModel.memoryWordNat current.memory
        (sourceAddress current.index (UInt256.ofNat fp)).toNat =
      MultiLimbMemoryModel.memoryWordNat mem (fp + 32 + 32 * q) := by
    unfold MultiLimbMemoryModel.memoryWordNat
    have hframe' : current.memory.readWithPadding
          (sourceAddress current.index (UInt256.ofNat fp)).toNat 32 =
        mem.readWithPadding (sourceAddress current.index (UInt256.ofNat fp)).toNat 32 := by
      simpa only [current, initialState] using hframe
    rw [hsourceAddr] at hframe'
    rw [hsourceAddr]
    exact congrArg fromByteArrayBigEndian hframe'
  rcases hvalid q hq with ⟨_safe, hheader, _sourceAw, _outputAw⟩
  unfold sourceValue
  rw [hheader]
  simpa only [current] using (show
    MultiLimbArithmeticTrace.readWord current.memory aw
        (sourceAddress current.index (UInt256.ofNat fp)) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat mem (fp + 32 + 32 * q)) by
        rw [hguarded, hmemoryWord])

theorem partialSourceAddress_toNat
    {fp dataLen : Nat} (hlen : dataLen ≤ 1024)
    (hfit : fp + 32 + 32 * (dataLen / 32) < UInt256.size) :
    (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat =
      fp + 32 + 32 * (dataLen / 32) := by
  unfold partialSourceAddress
  rw [MultiLimbGenerated.wordClearedRemainder_eq hlen]
  have hfp : fp < UInt256.size := by omega
  have hcleared : 32 * (dataLen / 32) < UInt256.size := by omega
  have hfirst : 32 * (dataLen / 32) + fp < UInt256.size := by
    rw [Nat.add_comm]
    omega
  rw [uadd_toNat, uadd_toNat,
    UInt256.toNat_ofNat_of_lt hcleared, UInt256.toNat_ofNat_of_lt hfp,
    show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The partial serializer source read sees the original top accumulator word after all lower
full-word output writes. -/
theorem partialSourceValue_eq_accumulator
    {mem : ByteArray} {aw out : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * (dataLen / 32 + 1) < UInt256.size)
    (houtBefore : out.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    partialSourceValue
        (limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen).memory
        aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat mem
        (fp + 32 + 32 * (dataLen / 32))) := by
  let count := dataLen / 32
  let state := limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen
  have hfullIn := initial_fullWrites_inBounds (aw := aw)
    (limbs := UInt256.ofNat fp) (mem := mem) (out := out) (dataLen := dataLen)
    hlen haddr hmem
  have hsize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      out count (initialState mem) (by simpa only [count] using hfullIn)
  have hsourceAddr :
      (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat =
        fp + 32 + 32 * count := by
    simpa only [count] using partialSourceAddress_toNat hlen (by omega)
  have hstateCovered : MemoryCovered state.memory aw := by
    unfold MemoryCovered at hcovered ⊢
    rw [hsize]
    exact hcovered
  have hguarded : MultiLimbArithmeticTrace.readWord state.memory aw
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat state.memory
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat) := by
    simpa only using
      (Modexp.MultiLimbSchoolbookMulTrace.readWord_eq_memoryWordOf_covered_padded
        state.memory aw
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen))
        hstateCovered hawFit)
  have hbelow : ∀ j, j < count →
      let prior := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out j
        (initialState mem)
      (outputAddress prior.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat := by
    intro j hj
    dsimp only
    rw [initial_index]
    rw [outputAddress_toNat hlen (by simpa only [count] using hj) haddr, hsourceAddr]
    omega
  have hframe := iterate_read_above aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out count
    (initialState mem) (partialSourceAddress (UInt256.ofNat fp)
      (UInt256.ofNat dataLen)).toNat (by simpa only [count] using hfullIn) hbelow
  have hmemoryWord : MultiLimbMemoryModel.memoryWordNat state.memory
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat =
      MultiLimbMemoryModel.memoryWordNat mem (fp + 32 + 32 * count) := by
    unfold MultiLimbMemoryModel.memoryWordNat
    have hframe' : state.memory.readWithPadding
          (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat 32 =
        mem.readWithPadding
          (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat 32 := by
      simpa only [state, limbsToBytesFullState, count, initialState] using hframe
    rw [hsourceAddr] at hframe'
    rw [hsourceAddr]
    exact congrArg fromByteArrayBigEndian hframe'
  unfold partialSourceValue
  simpa only [state, count] using (show
    MultiLimbArithmeticTrace.readWord state.memory aw
        (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat mem
        (fp + 32 + 32 * count)) by rw [hguarded, hmemoryWord])

/-- The complete concrete serializer source list is exactly the Barrett accumulator limb list. -/
theorem serializedSourceWords_eq_accumulator
    {mem : ByteArray} {aw out : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (houtBefore : out.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvalid : ∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q (initialState mem))) :
    serializedSourceWords mem aw (UInt256.ofNat fp) out dataLen =
      memoryWordsFrom mem (fp + 32) ((dataLen + 31) / 32) := by
  have hqle : dataLen / 32 ≤ (dataLen + 31) / 32 :=
    Nat.div_le_div_right (by omega : dataLen ≤ dataLen + 31)
  have hfull := fullSourceWords_eq_accumulator hlen haddr hmem (by omega)
    houtBefore hcovered hawFit hvalid
  have hdecomp := Nat.mod_add_div dataLen 32
  by_cases hrem : dataLen % 32 = 0
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 := by omega
    unfold serializedSourceWords
    dsimp only
    rw [if_pos hrem, List.append_nil, hfull, hceil]
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
    have htop := partialSourceValue_eq_accumulator hlen haddr hmem (by
      simpa only [hceil] using hsourceFit)
      houtBefore hcovered hawFit
    unfold serializedSourceWords
    dsimp only
    rw [if_neg hrem, hfull, htop, hceil,
      memoryWordsFrom_succ_eq_append]

/-- Allocated source, output, and header words discharge every full serializer iteration's
checked arithmetic and active-memory premises. -/
theorem serializerValid_of_geometry
    {mem : ByteArray} {aw out : UInt256} {fp dataLen kWords : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * (dataLen / 32) < UInt256.size)
    (hsourceActive : fp + 32 + 32 * (dataLen / 32) ≤ 32 * aw.toNat)
    (hcovered : MemoryCovered mem aw)
    (hheader : ∀ q, q < dataLen / 32 →
      headerValue
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
          (initialState mem)).memory aw (UInt256.ofNat fp) = UInt256.ofNat kWords)
    (hkWords : dataLen / 32 ≤ kWords) (hkWordsBound : kWords ≤ 32) :
    ∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
          (initialState mem)) := by
  intro q hq
  let current := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
    (initialState mem)
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := out)
    (dataLen := dataLen) hlen haddr hmem
  have hsize : current.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      out q (initialState mem) (fun j hj => hfullIn j (by omega))
  have hcurrentCovered : MemoryCovered current.memory aw := by
    unfold MemoryCovered at hcovered ⊢
    rw [hsize]
    exact hcovered
  have hindex : current.index = UInt256.ofNat q := by
    exact initial_index aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q mem
  have hsourceAddr : (sourceAddress current.index (UInt256.ofNat fp)).toNat =
      fp + 32 + 32 * q := by
    rw [hindex]
    exact sourceAddress_toNat (by omega)
  have houtputWord :
      (outputAddress current.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        current.memory.size := hfullIn q hq
  have hheaderAccess : (UInt256.ofNat fp).toNat + 32 ≤ 32 * aw.toNat := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)]
    omega
  have hsourceAccess :
      (sourceAddress current.index (UInt256.ofNat fp)).toNat + 32 ≤ 32 * aw.toNat := by
    rw [hsourceAddr]
    omega
  have houtputAccess :
      (outputAddress current.index (UInt256.ofNat dataLen) out).toNat + 32 ≤
        32 * aw.toNat := by
    unfold MemoryCovered at hcurrentCovered
    omega
  have hheaderAw : headerActiveWords aw (UInt256.ofNat fp) = aw := by
    unfold headerActiveWords MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access hheaderAccess, u256_ofNat_toNat]
  have hsourceAw : sourceActiveWords aw current.index (UInt256.ofNat fp) = aw := by
    unfold sourceActiveWords
    rw [hheaderAw]
    unfold MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access hsourceAccess, u256_ofNat_toNat]
  have houtputAw : iterationActiveWords aw current.index (UInt256.ofNat fp)
      (UInt256.ofNat dataLen) out = aw := by
    unfold iterationActiveWords
    rw [hsourceAw]
    unfold MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access houtputAccess, u256_ofNat_toNat]
  have hsafe3 := MultiLimbGenerated.fullWordStepSafe_ofNat
    (i := q) (dataLen := dataLen) (by omega) hlen (by omega)
  have hindexBound : q < UInt256.size := by omega
  have hkBound : kWords < UInt256.size := by omega
  have hlt : (UInt256.ofNat q).lt (UInt256.ofNat kWords) ≠ ⟨0⟩ := by
    have h := ult_one (a := UInt256.ofNat q) (b := UInt256.ofNat kWords) (by
      rw [UInt256.toNat_ofNat_of_lt hindexBound, UInt256.toNat_ofNat_of_lt hkBound]
      omega)
    rw [h]
    decide
  refine ⟨?_, hheaderAw, hsourceAw, houtputAw⟩
  unfold stepSafe
  rw [hindex]
  rcases hsafe3 with ⟨hadd, hshift, hsub⟩
  change (outputOffset (UInt256.ofNat q) (UInt256.ofNat dataLen)).gt
    (UInt256.ofNat dataLen) = ⟨0⟩ at hsub
  refine ⟨hadd, hshift, hsub, ?_⟩
  rw [hheader q hq]
  exact isZero_eq_zero_of_ne hlt

/-- Reversed result stores remain below and therefore preserve the accumulator array header. -/
theorem serializerHeaderValue_preserved
    {mem : ByteArray} {aw out : UInt256} {fp dataLen kWords : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (houtBeforeHeader : out.toNat + 32 + dataLen ≤ fp)
    (hfpFit : fp + 32 < UInt256.size)
    (hheader : headerValue mem aw (UInt256.ofNat fp) = UInt256.ofNat kWords) :
    ∀ q, q < dataLen / 32 →
      headerValue
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
          (initialState mem)).memory aw (UInt256.ofNat fp) = UInt256.ofNat kWords := by
  intro q hq
  let current := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
    (initialState mem)
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := out)
    (dataLen := dataLen) hlen haddr hmem
  have hsize : current.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      out q (initialState mem) (fun j hj => hfullIn j (by omega))
  have hbelow : ∀ j, j < q →
      let prior := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out j
        (initialState mem)
      (outputAddress prior.index (UInt256.ofNat dataLen) out).toNat + 32 ≤ fp := by
    intro j hj
    dsimp only
    rw [initial_index]
    rw [outputAddress_toNat hlen (by omega) haddr]
    omega
  have hframe := iterate_read_above aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
    (initialState mem) fp (fun j hj => hfullIn j (by omega)) hbelow
  have hfp : fp < UInt256.size := by omega
  have hfpNat : (UInt256.ofNat fp).toNat = fp := UInt256.toNat_ofNat_of_lt hfp
  unfold headerValue MultiLimbArithmeticTrace.readWord at hheader ⊢
  rw [hfpNat] at hheader
  rw [hfpNat, hsize]
  have hframe' : current.memory.readWithPadding fp 32 = mem.readWithPadding fp 32 := by
    simpa only [current, initialState] using hframe
  rw [hframe']
  exact hheader

/-- Allocated top-source and padded result words discharge the nonaligned suffix's active-memory
premises. -/
theorem serializerPartialValid_of_geometry
    {mem : ByteArray} {aw out : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hpartialOutIn : out.toNat + 64 ≤ mem.size)
    (hcovered : MemoryCovered mem aw) :
    dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen).memory
      aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out := by
  intro hrem
  let state := limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := out)
    (dataLen := dataLen) hlen haddr hmem
  have hsize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      out (dataLen / 32) (initialState mem) hfullIn
  have hstateCovered : MemoryCovered state.memory aw := by
    unfold MemoryCovered at hcovered ⊢
    rw [hsize]
    exact hcovered
  have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by
    have hdecomp := Nat.mod_add_div dataLen 32
    omega
  have hsourceAddr :
      (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat =
        fp + 32 + 32 * (dataLen / 32) :=
    partialSourceAddress_toNat hlen (by rw [hceil] at hsourceFit; omega)
  have houtAddr : (partialOutputAddress out).toNat = out.toNat + 32 := by
    unfold partialOutputAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hsourceAccess :
      (partialSourceAddress (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat + 32 ≤
        32 * aw.toNat := by
    rw [hsourceAddr]
    rw [hceil] at hsourceActive
    omega
  have houtAccess : (partialOutputAddress out).toNat + 32 ≤ 32 * aw.toNat := by
    unfold MemoryCovered at hstateCovered
    rw [houtAddr, hsize] at *
    omega
  have hsourceAw : partialSourceActiveWords aw (UInt256.ofNat fp)
      (UInt256.ofNat dataLen) = aw := by
    unfold partialSourceActiveWords MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access hsourceAccess, u256_ofNat_toNat]
  have houtAw : partialOutputActiveWords aw (UInt256.ofNat fp)
      (UInt256.ofNat dataLen) out = aw := by
    unfold partialOutputActiveWords
    rw [hsourceAw]
    unfold MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access houtAccess, u256_ofNat_toNat]
  have hstoreAw : partialStoreActiveWords aw (UInt256.ofNat fp)
      (UInt256.ofNat dataLen) out = aw := by
    unfold partialStoreActiveWords
    rw [houtAw]
    unfold MultiLimbArithmeticTrace.readWords1
    rw [machineM_eq_of_access houtAccess, u256_ofNat_toNat]
  exact ⟨hsourceAw, houtAw, hstoreAw⟩

/-- One caller-level geometry package constructs every full and partial serializer validity fact. -/
theorem serializerValidity_of_geometry
    {mem : ByteArray} {aw out : UInt256} {fp dataLen kWords : Nat}
    (hlen : dataLen ≤ 1024)
    (hkWords : kWords = (dataLen + 31) / 32)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hpartialOutIn : out.toNat + 64 ≤ mem.size)
    (houtBeforeHeader : out.toNat + 32 + dataLen ≤ fp)
    (hcovered : MemoryCovered mem aw)
    (hheader : headerValue mem aw (UInt256.ofNat fp) = UInt256.ofNat kWords) :
    (∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out q
          (initialState mem))) ∧
    (dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen).memory
      aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) out) ∧
    (dataLen % 32 ≠ 0 → (partialOutputAddress out).toNat + 32 ≤
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen).memory.size) := by
  have hkBound : kWords ≤ 32 := by rw [hkWords]; omega
  have hqle : dataLen / 32 ≤ kWords := by rw [hkWords]; omega
  have hfullSourceFit : fp + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hdivle : dataLen / 32 ≤ (dataLen + 31) / 32 :=
      Nat.div_le_div_right (by omega)
    omega
  have hheaders := serializerHeaderValue_preserved hlen haddr hmem
    houtBeforeHeader (by omega) hheader
  have hvalid := serializerValid_of_geometry hlen haddr hmem hfullSourceFit
    (by omega) hcovered hheaders hqle hkBound
  have hpartial := serializerPartialValid_of_geometry hlen haddr hmem hsourceFit
    hsourceActive hpartialOutIn hcovered
  refine ⟨hvalid, hpartial, ?_⟩
  intro _hrem
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := out)
    (dataLen := dataLen) hlen haddr hmem
  have hsize := iterate_size_eq_of_inBounds aw (UInt256.ofNat fp)
    (UInt256.ofNat dataLen) out (dataLen / 32) (initialState mem) hfullIn
  have houtAddr : (partialOutputAddress out).toNat = out.toNat + 32 := by
    unfold partialOutputAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by omega)]
  rw [houtAddr]
  simpa only [limbsToBytesFullState, hsize] using hpartialOutIn

/-- If a radix expansion fits `q` complete words plus `rem` bytes, its top word fits those
remaining bytes. -/
theorem topWord_fit_of_value
    {words : List UInt256} {top : UInt256} {q rem : Nat}
    (hlen : words.length = q)
    (hvalue : wordLimbsToNat (words ++ [top]) < 256 ^ (32 * q + rem)) :
    top.toNat < 256 ^ rem := by
  by_contra hnot
  have htop : 256 ^ rem ≤ top.toNat := by omega
  have hradix : UInt256.size ^ q = 256 ^ (32 * q) := by
    rw [show UInt256.size = 256 ^ 32 by native_decide, ← Nat.pow_mul]
  have hlower : 256 ^ (32 * q + rem) ≤ wordLimbsToNat (words ++ [top]) := by
    rw [wordLimbsToNat_append, hlen, hradix]
    simp only [wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
    rw [Nat.pow_add]
    exact le_add_left (Nat.mul_le_mul_left _ htop)
  omega

/-- The concrete partial source limb fits the requested remainder bytes because the complete
Barrett accumulator fits the requested result width. -/
theorem partialSourceValue_fit_of_accumulator_value
    {mem : ByteArray} {aw out : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (houtBefore : out.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvalue : barrettAccumulatorValue
      ((dataLen + 31) / 32) (UInt256.ofNat fp) mem < 256 ^ dataLen) :
    dataLen % 32 ≠ 0 →
      (partialSourceValue
        (limbsToBytesFullState mem aw (UInt256.ofNat fp) out dataLen).memory
        aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)).toNat <
          2 ^ (8 * (dataLen % 32)) := by
  intro hrem
  let q := dataLen / 32
  let rem := dataLen % 32
  have hremPos : 0 < rem := by dsimp only [rem]; omega
  have hceil : (dataLen + 31) / 32 = q + 1 := by
    dsimp only [q, rem] at *
    have hdecomp := Nat.mod_add_div dataLen 32
    omega
  have hfp : fp < UInt256.size := by omega
  have hptr : (UInt256.ofNat fp + ⟨32⟩).toNat = fp + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfp,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hacc : wordLimbsToNat
      (memoryWordsFrom mem (fp + 32) (q + 1)) < 256 ^ (32 * q + rem) := by
    unfold barrettAccumulatorValue at hvalue
    rw [hptr, hceil] at hvalue
    have hdecomp := Nat.mod_add_div dataLen 32
    have hlenEq : dataLen = 32 * q + rem := by dsimp only [q, rem]; omega
    rw [← hlenEq]
    exact hvalue
  rw [memoryWordsFrom_succ_eq_append] at hacc
  have htop := topWord_fit_of_value
    (words := memoryWordsFrom mem (fp + 32) q)
    (top := UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat mem (fp + 32 + 32 * q)))
    (q := q) (rem := rem) (by simp only [memoryWordsFrom_length]) hacc
  have htop' : MultiLimbMemoryModel.memoryWordNat mem (fp + 32 + 32 * q) < 256 ^ rem := by
    simpa only [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] using htop
  have hsource := partialSourceValue_eq_accumulator
    hlen haddr hmem (by simpa only [hceil, q] using hsourceFit)
    houtBefore hcovered hawFit
  rw [hsource, UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
  simpa only [rem, show 2 ^ (8 * (dataLen % 32)) = 256 ^ (dataLen % 32) by
    rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul], q] using htop'

/-- Under the concrete active-memory guards, the serializer's existing-word `MLOAD` is the same
32-byte value used by the pure memory model. -/
theorem partialExistingValue_eq_model
    {mem : ByteArray} {aw limbs out : UInt256} {dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : out.toNat + 32 + dataLen < UInt256.size)
    (haddr64 : out.toNat + 32 + dataLen < 2 ^ 64)
    (hmem : out.toNat + 32 + dataLen ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hpartial : PartialValid
      (limbsToBytesFullState mem aw limbs out dataLen).memory
      aw limbs (UInt256.ofNat dataLen) out)
    (hpartialIn : (partialOutputAddress out).toNat + 32 ≤
      (limbsToBytesFullState mem aw limbs out dataLen).memory.size) :
    Model.bytesToNatPadded
        (limbsToBytesFullState mem aw limbs out dataLen).memory
        (partialOutputAddress out).toNat 32 =
      (partialExistingValue
        (limbsToBytesFullState mem aw limbs out dataLen).memory
        aw limbs (UInt256.ofNat dataLen) out).toNat := by
  let state := limbsToBytesFullState mem aw limbs out dataLen
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := limbs) (mem := mem) (out := out) (dataLen := dataLen)
    hlen haddr hmem
  have hsize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw limbs (UInt256.ofNat dataLen) out
      (dataLen / 32) (initialState mem) hfullIn
  have hstateCovered : MemoryCovered state.memory aw := by
    unfold MemoryCovered at hcovered ⊢
    rw [hsize]
    exact hcovered
  have houtNat : (partialOutputAddress out).toNat = out.toNat + 32 := by
    unfold partialOutputAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hword : (partialOutputAddress out).toNat + 32 ≤ state.memory.size := by
    simpa only [state] using hpartialIn
  rcases hpartial with ⟨hsourceAw, _houtputAw, _hstoreAw⟩
  have hread : MultiLimbArithmeticTrace.readWord state.memory
        (partialSourceActiveWords aw limbs (UInt256.ofNat dataLen))
        (partialOutputAddress out) =
      UInt256.ofNat (MultiLimbMemoryModel.memoryWordNat state.memory
        (partialOutputAddress out).toNat) := by
    rw [hsourceAw]
    unfold MultiLimbArithmeticTrace.readWord
    rw [if_neg (not_or.mpr ⟨by omega,
      wordBelowActive_of_covered state.memory aw (partialOutputAddress out)
        hstateCovered hawFit hword⟩)]
    rfl
  unfold partialExistingValue
  rw [show limbsToBytesFullState mem aw limbs out dataLen = state by rfl]
  rw [hread, UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
  exact (MultiLimbMemoryModel.memoryWordNat_eq_model state.memory
    (partialOutputAddress out).toNat (by rw [houtNat]; omega)).symm

/-- The bytes produced by the complete concrete serializer have exactly the selected Barrett
accumulator value. -/
theorem resultMemory_value_eq_accumulator
    {mem : ByteArray} {aw result : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (houtBefore : result.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvalid : ∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result q
          (initialState mem)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory
      aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result)
    (hpartialIn : dataLen % 32 ≠ 0 → (partialOutputAddress result).toNat + 32 ≤
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory.size)
    (hvalue : barrettAccumulatorValue
      ((dataLen + 31) / 32) (UInt256.ofNat fp) mem < 256 ^ dataLen) :
    Model.bytesToNatPadded
        (limbsToBytesMemory mem aw (UInt256.ofNat fp) result dataLen)
        (result.toNat + 32) dataLen =
      barrettAccumulatorValue ((dataLen + 31) / 32) (UInt256.ofNat fp) mem := by
  have haddr : result.toNat + 32 + dataLen < UInt256.size :=
    haddr64.trans (by decide)
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := result)
    (dataLen := dataLen) hlen haddr hmem
  have hexisting : dataLen % 32 ≠ 0 → Model.bytesToNatPadded
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory
      (partialOutputAddress result).toNat 32 =
    (partialExistingValue
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory
      aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result).toNat := by
    intro hrem
    exact partialExistingValue_eq_model hlen haddr haddr64 hmem hcovered hawFit
      (hpartial hrem) (hpartialIn hrem)
  have hpartialFit := partialSourceValue_fit_of_accumulator_value hlen haddr
    hmem hsourceFit houtBefore hcovered hawFit hvalue
  have hserialized := serializedSourceWords_eq_accumulator hlen haddr hmem hsourceFit
    houtBefore hcovered hawFit hvalid
  have hbytes := limbsToBytesMemory_value hlen haddr64 hfullIn hpartialIn
    hexisting hpartialFit
  rw [hbytes, hserialized]
  unfold barrettAccumulatorValue
  have hfp : fp < UInt256.size := by omega
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfp,
    show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt (by omega)]

/-- Once the exposed exponent selector has established its pure accumulator value, the actual
serializer writes that same value into the result bytes. -/
theorem resultMemory_value_eq
    {mem : ByteArray} {aw result : UInt256} {fp dataLen kWords value : Nat}
    (hlen : dataLen ≤ 1024)
    (hkWords : kWords = (dataLen + 31) / 32)
    (haddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (houtBefore : result.toNat + 32 + dataLen ≤ fp + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvalid : ∀ q, q < dataLen / 32 →
      ValidStep aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result
        (iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result q
          (initialState mem)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory
      aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result)
    (hpartialIn : dataLen % 32 ≠ 0 → (partialOutputAddress result).toNat + 32 ≤
      (limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen).memory.size)
    (haccumulator : barrettAccumulatorValue kWords (UInt256.ofNat fp) mem = value)
    (hvalueFit : value < 256 ^ dataLen) :
    Model.bytesToNatPadded
        (limbsToBytesMemory mem aw (UInt256.ofNat fp) result dataLen)
        (result.toNat + 32) dataLen = value := by
  have hbound : barrettAccumulatorValue ((dataLen + 31) / 32)
      (UInt256.ofNat fp) mem < 256 ^ dataLen := by
    rw [← hkWords, haccumulator]
    exact hvalueFit
  rw [resultMemory_value_eq_accumulator hlen haddr64 hmem hsourceFit
    houtBefore hcovered hawFit hvalid hpartial hpartialIn hbound]
  rw [← hkWords, haccumulator]

/-- A fixed-width padded memory window is the trusted fixed-width encoding of its numeric value. -/
theorem readWithPadding_eq_natToBytes_of_value
    {mem : ByteArray} {start len value : Nat}
    (hstart64 : start < 2 ^ 64) (hlen64 : len < 2 ^ 64)
    (hvalue : Model.bytesToNatPadded mem start len = value)
    (hfit : value < 256 ^ len) :
    mem.readWithPadding start len = Model.natToBytes value len := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply Reasoning.Theory.fromBytesBigEndian_inj_of_length
  · simp only [Array.length_toList]
    change (mem.readWithPadding start len).size = (Model.natToBytes value len).size
    rw [readWithPadding_eq_model_readPadded mem start len hstart64 hlen64,
      model_readPadded_size, model_natToBytes_size]
  · rw [← Reasoning.Theory.byteArray_toList_eq,
      ← Reasoning.Theory.byteArray_toList_eq]
    change fromByteArrayBigEndian (mem.readWithPadding start len) =
      fromByteArrayBigEndian (Model.natToBytes value len)
    rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      ← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      readWithPadding_eq_model_readPadded mem start len hstart64 hlen64,
      model_bytesToBigEndianNat_natToBytes]
    unfold Model.bytesToNatPadded at hvalue
    rw [hvalue, Nat.mod_eq_of_lt hfit]

/-- Numeric correctness of a concrete result memory immediately gives the exact trusted return
byte array at the same width. -/
theorem resultMemory_bytes_eq_natToBytes
    {mem : ByteArray} {result : UInt256} {dataLen value : Nat}
    (haddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hvalue : Model.bytesToNatPadded mem (result.toNat + 32) dataLen = value)
    (hfit : value < 256 ^ dataLen) :
    mem.readWithPadding (result.toNat + 32) dataLen =
      Model.natToBytes value dataLen := by
  exact readWithPadding_eq_natToBytes_of_value (by omega) (by omega) hvalue hfit

/-- The serializer only writes the result payload, so the preallocated bytes header is preserved
on both the aligned and masked-partial paths. -/
theorem resultMemory_header_preserved
    {mem : ByteArray} {aw result : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : result.toNat + 32 + dataLen < UInt256.size)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hpartialIn : dataLen % 32 ≠ 0 → result.toNat + 64 ≤ mem.size) :
    (Modexp.MultiLimbBarrettResult.resultMemory mem aw (UInt256.ofNat fp) result dataLen
        ).readWithPadding result.toNat 32 =
      mem.readWithPadding result.toNat 32 := by
  let state := limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := result)
    (dataLen := dataLen) hlen haddr hmem
  have habove : ∀ q, q < dataLen / 32 →
      let current := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result q
        (initialState mem)
      result.toNat + 32 ≤
        (outputAddress current.index (UInt256.ofNat dataLen) result).toNat := by
    intro q hq
    dsimp only
    rw [initial_index, outputAddress_toNat hlen (by omega) haddr]
    omega
  have hfull := iterate_read_below aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
    result (dataLen / 32) (initialState mem) result.toNat hfullIn habove
  have hstateSize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      result (dataLen / 32) (initialState mem) hfullIn
  by_cases hrem : dataLen % 32 = 0
  · simpa [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory,
      limbsToBytesSuffixMemory, state, hrem] using hfull
  · have hout : (partialOutputAddress result).toNat = result.toNat + 32 := by
      unfold partialOutputAddress
      rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
        Nat.mod_eq_of_lt (by omega)]
    have hpartial :
        (limbsToBytesSuffixMemory state.memory aw (UInt256.ofNat fp) result dataLen
          ).readWithPadding result.toNat 32 =
        state.memory.readWithPadding result.toNat 32 := by
      rw [limbsToBytesSuffixMemory, if_neg hrem]
      unfold partialMemory
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by rw [hout, hstateSize]; have := hpartialIn hrem; omega) (by rw [hout])
    rw [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory]
    exact hpartial.trans (by simpa only [state] using hfull)

/-- Serialization preserves every complete word below the preallocated output payload. -/
theorem resultMemory_read_below
    {mem : ByteArray} {aw result : UInt256} {fp dataLen read : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : result.toNat + 32 + dataLen < UInt256.size)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hpartialIn : dataLen % 32 ≠ 0 → result.toNat + 64 ≤ mem.size)
    (hbelow : read + 32 ≤ result.toNat + 32) :
    (Modexp.MultiLimbBarrettResult.resultMemory mem aw (UInt256.ofNat fp) result dataLen
        ).readWithPadding read 32 = mem.readWithPadding read 32 := by
  let state := limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := result)
    (dataLen := dataLen) hlen haddr hmem
  have habove : ∀ q, q < dataLen / 32 →
      let current := iterate aw (UInt256.ofNat fp) (UInt256.ofNat dataLen) result q
        (initialState mem)
      read + 32 ≤
        (outputAddress current.index (UInt256.ofNat dataLen) result).toNat := by
    intro q hq
    dsimp only
    rw [initial_index, outputAddress_toNat hlen (by omega) haddr]
    omega
  have hfull := iterate_read_below aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
    result (dataLen / 32) (initialState mem) read hfullIn habove
  have hstateSize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      result (dataLen / 32) (initialState mem) hfullIn
  by_cases hrem : dataLen % 32 = 0
  · simpa [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory,
      limbsToBytesSuffixMemory, state, hrem] using hfull
  · have hout : (partialOutputAddress result).toNat = result.toNat + 32 := by
      unfold partialOutputAddress
      rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
        Nat.mod_eq_of_lt (by omega)]
    have hpartial :
        (limbsToBytesSuffixMemory state.memory aw (UInt256.ofNat fp) result dataLen
          ).readWithPadding read 32 = state.memory.readWithPadding read 32 := by
      rw [limbsToBytesSuffixMemory, if_neg hrem]
      unfold partialMemory
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by rw [hout, hstateSize]; have := hpartialIn hrem; omega)
        (by rw [hout]; exact hbelow)
    rw [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory]
    exact hpartial.trans (by simpa only [state] using hfull)

/-- With the caller-provided output allocation, result serialization does not expand memory. -/
theorem resultMemory_size
    {mem : ByteArray} {aw result : UInt256} {fp dataLen : Nat}
    (hlen : dataLen ≤ 1024)
    (haddr : result.toNat + 32 + dataLen < UInt256.size)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hpartialIn : dataLen % 32 ≠ 0 → result.toNat + 64 ≤ mem.size) :
    (Modexp.MultiLimbBarrettResult.resultMemory mem aw (UInt256.ofNat fp) result dataLen
        ).size = mem.size := by
  let state := limbsToBytesFullState mem aw (UInt256.ofNat fp) result dataLen
  have hfullIn := initial_fullWrites_inBounds
    (aw := aw) (limbs := UInt256.ofNat fp) (mem := mem) (out := result)
    (dataLen := dataLen) hlen haddr hmem
  have hstateSize : state.memory.size = mem.size := by
    exact iterate_size_eq_of_inBounds aw (UInt256.ofNat fp) (UInt256.ofNat dataLen)
      result (dataLen / 32) (initialState mem) hfullIn
  by_cases hrem : dataLen % 32 = 0
  · simpa [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory,
      limbsToBytesSuffixMemory, state, hrem] using hstateSize
  · have hout : (partialOutputAddress result).toNat = result.toNat + 32 := by
      unfold partialOutputAddress
      rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
        Nat.mod_eq_of_lt (by omega)]
    rw [Modexp.MultiLimbBarrettResult.resultMemory, limbsToBytesMemory,
      limbsToBytesSuffixMemory, if_neg hrem]
    unfold partialMemory
    rw [write_size_of_inBounds_from]
    · exact hstateSize
    · omega
    · rw [toByteArray_size]
    · rw [hout, hstateSize]
      have := hpartialIn hrem
      omega

/-- Execute the complete selected exponent and serializer path while deriving the serializer's
per-iteration trace validity from caller allocation geometry. -/
theorem exact_of_serializerGeometry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced retBar result ret : UInt256}
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
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultMem : result.toNat + 32 + dataLen ≤ selected.memory.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * selected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ selected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hselectedCovered : MemoryCovered selected.memory selected.activeWords)
    (hselectedHeader : headerValue selected.memory selected.activeWords
      (UInt256.ofNat fp) = UInt256.ofNat k)
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory selected.memory selected.activeWords
        (UInt256.ofNat fp) result dataLen)
      selected.activeWords rdata acc
      (steps + Modexp.MultiLimbBarrettResult.executionSteps selected dataLen)
      (gasUsed + Modexp.MultiLimbBarrettResult.executionGas aw fp k exponent selected dataLen) := by
  have hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    rw [← hkData]
    omega
  have hserializer := serializerValidity_of_geometry hlen hkData hresultAddr hresultMem
    hsourceFit hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedHeader
  exact Modexp.MultiLimbBarrettResult.exact hkTwo hk hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hawFit hfit hread hcalldata valid hlen hserializer.1 hserializer.2.1
    hdepth hretBar h

/-- Turn a completed selected serializer execution into the wrapper's exact trusted return.  The
result header, payload value, active-memory guards, and fixed-width encoding are all derived from
the same pre-serialization state. -/
theorem wrapperReturn_of_memory
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords dataLen value : Nat} {tail : List UInt256}
    {result : UInt256}
    (hlen : dataLen ≤ 1024)
    (hkWords : kWords = (dataLen + 31) / 32)
    (haddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hmem : result.toNat + 32 + dataLen ≤ mem.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ mem.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haccHeader : headerValue mem aw (UInt256.ofNat fp) =
      UInt256.ofNat kWords)
    (haccumulator : barrettAccumulatorValue kWords (UInt256.ofNat fp) mem = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : mem.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (htail : tail.length ≤ 1021)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨173⟩
      (result :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory mem aw
        (UInt256.ofNat fp) result dataLen)
      aw rdata acc steps gasUsed) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen) (gasUsed + 16) := by
  have haddr : result.toNat + 32 + dataLen < UInt256.size :=
    haddr64.trans (by decide)
  have hserializer := serializerValidity_of_geometry hlen hkWords haddr hmem hsourceFit
    hsourceActive hpartialOutIn houtBeforeHeader hcovered haccHeader
  have hnumeric := resultMemory_value_eq hlen hkWords haddr64 hmem hsourceFit
    (by omega) hcovered hawFit hserializer.1 hserializer.2.1 hserializer.2.2
    haccumulator hvalueFit
  have houtput := resultMemory_bytes_eq_natToBytes haddr64 hnumeric hvalueFit
  have hheaderPreserved := resultMemory_header_preserved
    (aw := aw) (fp := fp) hlen haddr hmem (fun _ => hpartialOutIn)
  have hsize := resultMemory_size
    (aw := aw) (fp := fp) hlen haddr hmem (fun _ => hpartialOutIn)
  have hloadActive : result.toNat + 32 ≤ 32 * aw.toNat := by
    unfold MemoryCovered at hcovered
    omega
  have hreturnActive : result.toNat + 32 + dataLen ≤
      32 * aw.toNat := by
    unfold MemoryCovered at hcovered
    omega
  have hresultWord : UInt256.ofNat result.toNat = result := u256_ofNat_toNat result
  have hnotActive : ¬ UInt256.ofNat result.toNat ≥ aw * ⟨32⟩ := by
    rw [hresultWord]
    exact wordBelowActive_of_covered mem aw result hcovered hawFit
      (by omega)
  have hheader :
      (if result.toNat ≥
            (Modexp.MultiLimbBarrettResult.resultMemory mem aw
              (UInt256.ofNat fp) result dataLen).size ∨
          UInt256.ofNat result.toNat ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((Modexp.MultiLimbBarrettResult.resultMemory mem aw
            (UInt256.ofNat fp) result dataLen).readWithPadding result.toNat 32))) =
        UInt256.ofNat dataLen := by
    rw [if_neg (not_or.mpr ⟨by rw [hsize]; omega, hnotActive⟩),
      hheaderPreserved, hresultHeader, fromByteArrayBigEndian_toByteArray,
      u256_ofNat_toNat]
  have hret := Modexp.wrapperReturnExact
    (ptr := result.toNat) (len := dataLen) (tail := tail)
    (mem := Modexp.MultiLimbBarrettResult.resultMemory mem aw
      (UInt256.ofNat fp) result dataLen)
    (aw := aw) (output := Model.natToBytes value dataLen)
    hlen (by omega) hloadActive hreturnActive hheader houtput
    htail (by simpa only [hresultWord] using h)
  exact hret

/-- Selector-specialized wrapper retained for the reused-scratch result theorem. -/
theorem wrapperReturn_of_resultMemory
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {selected : BarrettLoopSetupSelection}
    {steps gasUsed fp kWords dataLen value : Nat} {tail : List UInt256}
    {result ret : UInt256}
    (hlen : dataLen ≤ 1024)
    (hkWords : kWords = (dataLen + 31) / 32)
    (haddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hmem : result.toNat + 32 + dataLen ≤ selected.memory.size)
    (hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * selected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ selected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hcovered : MemoryCovered selected.memory selected.activeWords)
    (hawFit : selected.activeWords.toNat * 32 < UInt256.size)
    (haccHeader : headerValue selected.memory selected.activeWords (UInt256.ofNat fp) =
      UInt256.ofNat kWords)
    (haccumulator : barrettAccumulatorValue kWords (UInt256.ofNat fp) selected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : selected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (htail : tail.length + 1 ≤ 1021)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨173⟩
      (result :: ret :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory selected.memory selected.activeWords
        (UInt256.ofNat fp) result dataLen)
      selected.activeWords rdata acc steps gasUsed) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen) (gasUsed + 16) :=
  wrapperReturn_of_memory (tail := ret :: tail) hlen hkWords haddr64 hmem hsourceFit
    hsourceActive hpartialOutIn houtBeforeHeader hcovered hawFit haccHeader haccumulator
    hvalueFit hresultHeader (by simpa using htail) h

/-- Complete PC 1718 through the external wrapper return, retaining the exposed exponent selector
and its exact path-sensitive gas while returning the trusted fixed-width value. -/
theorem exactReturn_of_serializerGeometry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen value : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced result ret : UInt256}
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
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ selected.memory.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * selected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ selected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hselectedCovered : MemoryCovered selected.memory selected.activeWords)
    (hselectedAwFit : selected.activeWords.toNat * 32 < UInt256.size)
    (hselectedHeader : headerValue selected.memory selected.activeWords
      (UInt256.ofNat fp) = UInt256.ofNat k)
    (haccumulator : barrettAccumulatorValue k (UInt256.ofNat fp) selected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : selected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨173⟩ :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (gasUsed + Modexp.MultiLimbBarrettResult.executionGas aw fp k exponent selected dataLen +
        16) := by
  have rd173 := exact_of_serializerGeometry hkTwo hk hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hawFit hfit hread hcalldata valid hlen hkData hresultAddr hresultMem
    hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedHeader hdepth
    (by native_decide) h
  exact wrapperReturn_of_resultMemory hlen hkData hresultAddr64 hresultMem
    (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
      rw [← hkData]
      omega)
    hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered
    hselectedAwFit
    hselectedHeader haccumulator hvalueFit hresultHeader (by omega) rd173

/-- Fresh-scratch counterpart of `exactReturn_of_serializerGeometry`. The exposed selector
controls both execution indices and the accumulator value serialized by the wrapper. -/
theorem freshExactReturn_of_serializerGeometry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen value : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced result ret : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : FreshBarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ selected.memory.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * selected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ selected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hselectedCovered : MemoryCovered selected.memory selected.activeWords)
    (hselectedAwFit : selected.activeWords.toNat * 32 < UInt256.size)
    (hselectedHeader : headerValue selected.memory selected.activeWords
      (UInt256.ofNat fp) = UInt256.ofNat k)
    (haccumulator : barrettAccumulatorValue k (UInt256.ofNat fp) selected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : selected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨173⟩ :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (gasUsed + Modexp.MultiLimbBarrettResult.freshExecutionGas
        aw fp k exponent selected dataLen + 16) := by
  have hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    rw [← hkData]
    omega
  have hserializer := serializerValidity_of_geometry hlen hkData hresultAddr hresultMem
    hsourceFit hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedHeader
  have rd173 := Modexp.MultiLimbBarrettResult.freshExact
    hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit hfit hread hcalldata
    valid hlen hserializer.1 hserializer.2.1 hdepth (by native_decide) h
  exact wrapperReturn_of_memory (tail := ret :: tail) hlen hkData hresultAddr64 hresultMem hsourceFit
    hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedAwFit
    hselectedHeader haccumulator hvalueFit hresultHeader
    (by simp only [List.length_cons]; omega) rd173

/-- Fresh-scratch result path used by the deployed multi-limb caller.  Unlike the direct helper
form above, the serializer first returns to PC 1271, whose swap/jump trampoline then enters the
external wrapper at PC 173.  The trampoline contributes exactly 12 gas. -/
theorem freshExactReturnVia1271_of_serializerGeometry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen value : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced result : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : FreshBarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ selected.memory.size)
    (hsourceActive : fp + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * selected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ selected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ fp)
    (hselectedCovered : MemoryCovered selected.memory selected.activeWords)
    (hselectedAwFit : selected.activeWords.toNat * 32 < UInt256.size)
    (hselectedHeader : headerValue selected.memory selected.activeWords
      (UInt256.ofNat fp) = UInt256.ofNat k)
    (haccumulator : barrettAccumulatorValue k (UInt256.ofNat fp) selected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : selected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨1271⟩ :: result :: ⟨173⟩ :: tail)
      mem aw rdata acc steps gasUsed) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (gasUsed + Modexp.MultiLimbBarrettResult.freshExecutionGas
        aw fp k exponent selected dataLen + 28) := by
  have hsourceFit : fp + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    rw [← hkData]
    omega
  have hserializer := serializerValidity_of_geometry hlen hkData hresultAddr hresultMem
    hsourceFit hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedHeader
  have rd1271 := Modexp.MultiLimbBarrettResult.freshExact
    hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit hfit hread hcalldata
    valid hlen hserializer.1 hserializer.2.1 hdepth (by native_decide) h
  have rd173 := evm_run rd1271 with [jumpdest, swap1, jump (by native_decide)]
  have hret := wrapperReturn_of_memory (tail := tail) hlen hkData hresultAddr64 hresultMem
    hsourceFit hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedAwFit
    hselectedHeader haccumulator hvalueFit hresultHeader (by omega) rd173
  simpa only [Nat.add_assoc, show 12 + 16 = 28 by decide] using hret

end Modexp.MultiLimbBarrettResultSemantic
