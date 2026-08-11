import Examples.Precompiles.Modexp.MultiLimbArithmeticTrace
import Examples.Precompiles.Modexp.MultiLimbMultiplicationTraceBridge
import Examples.Precompiles.Modexp.MultiLimbMontgomeryArithmetic

/-!
# Generated CIOS Montgomery trace segments

The CIOS multiply pass at PC 4499 has the same full-width multiply/add arithmetic as the
reduction pass at PC 4440, but writes to the current scratch limb rather than the preceding limb.
This file exposes that exact generated transition and arbitrary finite iterations of it.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryTrace

open Modexp.MultiLimbMemoryModel
open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def multiplyPassMemory
    (mem : ByteArray) (aw operandPtr resultPtr a carry : UInt256) : ByteArray :=
  let step := schoolbookStep mem aw operandPtr resultPtr a carry
  step.1.toByteArray.write 0 mem resultPtr.toNat 32

def multiplyPassAw (aw operandPtr resultPtr : UInt256) : UInt256 :=
  let aw1 := readWords1 aw operandPtr
  let aw2 := readWords1 aw1 resultPtr
  UInt256.ofNat (MachineState.M aw2.toNat resultPtr.toNat 32)

def multiplyPassGas (aw operandPtr resultPtr : UInt256) : Nat :=
  let aw1 := readWords1 aw operandPtr
  let aw2 := readWords1 aw1 resultPtr
  let aw3 := multiplyPassAw aw operandPtr resultPtr
  172 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

def ciosBoundaryTk (mem : ByteArray) (aw tEnd : UInt256) : UInt256 :=
  readWord mem aw tEnd

def ciosBoundaryTkNew
    (mem : ByteArray) (aw tEnd multiplyCarry : UInt256) : UInt256 :=
  ciosBoundaryTk mem aw tEnd + multiplyCarry

def ciosBoundaryMem1
    (mem : ByteArray) (aw tEnd multiplyCarry : UInt256) : ByteArray :=
  (ciosBoundaryTkNew mem aw tEnd multiplyCarry).toByteArray.write
    0 mem tEnd.toNat 32

def ciosBoundaryAw1 (aw tEnd : UInt256) : UInt256 :=
  readWords1 aw tEnd

def ciosBoundaryAw2 (aw tEnd : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ciosBoundaryAw1 aw tEnd).toNat tEnd.toNat 32)

def ciosBoundaryOverflow
    (mem : ByteArray) (aw tEnd multiplyCarry : UInt256) : UInt256 :=
  (ciosBoundaryTkNew mem aw tEnd multiplyCarry).lt (ciosBoundaryTk mem aw tEnd)

def ciosBoundaryTk1
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off : UInt256) : UInt256 :=
  readWord (ciosBoundaryMem1 mem aw tEnd multiplyCarry)
    (ciosBoundaryAw2 aw tEnd) tk1Off

def ciosBoundaryMem2
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off : UInt256) : ByteArray :=
  (ciosBoundaryTk1 mem aw tEnd multiplyCarry tk1Off +
      ciosBoundaryOverflow mem aw tEnd multiplyCarry).toByteArray.write
    0 (ciosBoundaryMem1 mem aw tEnd multiplyCarry) tk1Off.toNat 32

def ciosBoundaryAw3 (aw tEnd tk1Off : UInt256) : UInt256 :=
  readWords1 (ciosBoundaryAw2 aw tEnd) tk1Off

def ciosBoundaryAw4 (aw tEnd tk1Off : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ciosBoundaryAw3 aw tEnd tk1Off).toNat tk1Off.toNat 32)

def ciosBoundaryT0
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP : UInt256) : UInt256 :=
  readWord (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off)
    (ciosBoundaryAw4 aw tEnd tk1Off) tP

def ciosBoundaryAw5 (aw tEnd tk1Off tP : UInt256) : UInt256 :=
  readWords1 (ciosBoundaryAw4 aw tEnd tk1Off) tP

def ciosBoundaryN0
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP nP : UInt256) : UInt256 :=
  readWord (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off)
    (ciosBoundaryAw5 aw tEnd tk1Off tP) nP

def ciosBoundaryAw
    (aw tEnd tk1Off tP nP : UInt256) : UInt256 :=
  readWords1 (ciosBoundaryAw5 aw tEnd tk1Off tP) nP

def ciosBoundaryFactor
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP n0inv : UInt256) : UInt256 :=
  UInt256.mul (ciosBoundaryT0 mem aw tEnd multiplyCarry tk1Off tP) n0inv

def ciosBoundaryCarry
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP nP n0inv : UInt256) : UInt256 :=
  let m := ciosBoundaryFactor mem aw tEnd multiplyCarry tk1Off tP n0inv
  let n0 := ciosBoundaryN0 mem aw tEnd multiplyCarry tk1Off tP nP
  let t0 := ciosBoundaryT0 mem aw tEnd multiplyCarry tk1Off tP
  let low := UInt256.mul m n0
  evmMulHigh m n0 + (low + t0).lt low

def ciosBoundaryGas (aw tEnd tk1Off tP nP : UInt256) : Nat :=
  let aw1 := ciosBoundaryAw1 aw tEnd
  let aw2 := ciosBoundaryAw2 aw tEnd
  let aw3 := ciosBoundaryAw3 aw tEnd tk1Off
  let aw4 := ciosBoundaryAw4 aw tEnd tk1Off
  let aw5 := ciosBoundaryAw5 aw tEnd tk1Off tP
  let aw6 := ciosBoundaryAw aw tEnd tk1Off tP nP
  180 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) +
    (Cₘ aw3 - Cₘ aw2) + (Cₘ aw4 - Cₘ aw3) +
    (Cₘ aw5 - Cₘ aw4) + (Cₘ aw6 - Cₘ aw5)

def ciosBoundaryGasAfter (C : Nat) (aw tEnd tk1Off tP nP : UInt256) : Nat :=
  let aw1 := ciosBoundaryAw1 aw tEnd
  let aw2 := ciosBoundaryAw2 aw tEnd
  let aw3 := ciosBoundaryAw3 aw tEnd tk1Off
  let aw4 := ciosBoundaryAw4 aw tEnd tk1Off
  let aw5 := ciosBoundaryAw5 aw tEnd tk1Off tP
  let aw6 := ciosBoundaryAw aw tEnd tk1Off tP nP
  180 + C + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) +
    (Cₘ aw3 - Cₘ aw2) + (Cₘ aw4 - Cₘ aw3) +
    (Cₘ aw5 - Cₘ aw4) + (Cₘ aw6 - Cₘ aw5)

theorem ciosBoundaryGasAfter_eq
    (C : Nat) (aw tEnd tk1Off tP nP : UInt256) :
    ciosBoundaryGasAfter C aw tEnd tk1Off tP nP =
      C + ciosBoundaryGas aw tEnd tk1Off tP nP := by
  simp only [ciosBoundaryGasAfter, ciosBoundaryGas]
  omega

/-- EVM multiplication computes the low-word Montgomery factor used by the natural model. -/
theorem evmMontgomeryFactor_toNat (x nInv : UInt256) :
    (UInt256.mul x nInv).toNat =
      montgomeryFactor UInt256.size nInv.toNat x.toNat := by
  rw [u256_mul_toNat]
  simp [montgomeryFactor]

/-- The low reduction word vanishes under the standard negative-inverse condition. -/
theorem evmMontgomeryLow_zero
    (x n0 nInv : UInt256)
    (hinv : n0.toNat * nInv.toNat % UInt256.size = UInt256.size - 1) :
    UInt256.mul (UInt256.mul x nInv) n0 + x = ⟨0⟩ := by
  have hdvd := montgomeryFactor_divides
    (radix := UInt256.size) (modulus := n0.toNat)
    (nInv := nInv.toNat) (x := x.toNat)
    (by norm_num [UInt256.size]) hinv
  apply u256_inj
  rw [uadd_toNat, u256_mul_toNat, evmMontgomeryFactor_toNat]
  change (montgomeryFactor UInt256.size nInv.toNat x.toNat * n0.toNat %
      UInt256.size + x.toNat) % UInt256.size = 0
  have hx : x.toNat % UInt256.size = x.toNat := Nat.mod_eq_of_lt x.val.isLt
  have hmod := Nat.add_mod
    (montgomeryFactor UInt256.size nInv.toNat x.toNat * n0.toNat)
    x.toNat UInt256.size
  rw [hx] at hmod
  rw [← hmod]
  simpa [Nat.add_comm] using Nat.mod_eq_zero_of_dvd hdvd

/-- The carry expression at the generated boundary is the carry of a schoolbook update with
zero incoming carry. -/
theorem ciosBoundaryCarry_eq_schoolbook
    (m n0 t0 : UInt256) :
    evmMulHigh m n0 + (UInt256.mul m n0 + t0).lt (UInt256.mul m n0) =
      (evmSchoolbookStep m n0 t0 ⟨0⟩).2 := by
  simp only [evmSchoolbookStep]
  have haddZero (a : UInt256) : a + ⟨0⟩ = a := by
    rw [u256_add_comm, u256_zero_add]
  rw [haddZero]
  have hlt : UInt256.lt (UInt256.mul m n0 + t0)
      (UInt256.mul m n0 + t0) = ⟨0⟩ := ult_zero (Nat.le_refl _)
  rw [hlt, haddZero]

/-- The generated peeled low-limb reduction computes an exact unbounded quotient column. -/
theorem evmMontgomeryPeeled_recompose
    (x n0 nInv : UInt256)
    (hinv : n0.toNat * nInv.toNat % UInt256.size = UInt256.size - 1) :
    UInt256.size *
        (evmMulHigh (UInt256.mul x nInv) n0 +
          (UInt256.mul (UInt256.mul x nInv) n0 + x).lt
            (UInt256.mul (UInt256.mul x nInv) n0)).toNat =
      x.toNat + (UInt256.mul x nInv).toNat * n0.toNat := by
  let m := UInt256.mul x nInv
  have hlow : UInt256.mul m n0 + x = ⟨0⟩ := by
    exact evmMontgomeryLow_zero x n0 nInv hinv
  have haddZero (a : UInt256) : a + ⟨0⟩ = a := by
    rw [u256_add_comm, u256_zero_add]
  have hfirst : (evmSchoolbookStep m n0 x ⟨0⟩).1 = ⟨0⟩ := by
    simp only [evmSchoolbookStep]
    rw [haddZero, hlow]
  have hstep := evmSchoolbookStep_recompose m n0 x ⟨0⟩
  dsimp only at hstep
  rw [hfirst] at hstep
  rw [← ciosBoundaryCarry_eq_schoolbook] at hstep
  simpa [m, Nat.add_comm] using hstep

/-- Arithmetic meaning of the factor and carry placed on the reduction-loop stack by PC 4338. -/
theorem ciosBoundaryPeeled_recompose
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP nP n0inv : UInt256)
    (hinv :
      (ciosBoundaryN0 mem aw tEnd multiplyCarry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1) :
    UInt256.size *
        (ciosBoundaryCarry mem aw tEnd multiplyCarry tk1Off tP nP n0inv).toNat =
      (ciosBoundaryT0 mem aw tEnd multiplyCarry tk1Off tP).toNat +
        (ciosBoundaryFactor mem aw tEnd multiplyCarry tk1Off tP n0inv).toNat *
          (ciosBoundaryN0 mem aw tEnd multiplyCarry tk1Off tP nP).toNat := by
  simpa only [ciosBoundaryCarry, ciosBoundaryFactor] using
    evmMontgomeryPeeled_recompose
      (ciosBoundaryT0 mem aw tEnd multiplyCarry tk1Off tP)
      (ciosBoundaryN0 mem aw tEnd multiplyCarry tk1Off tP nP)
      n0inv hinv

/-- The multiply pass's carry propagation preserves the complete two-word upper value. -/
theorem ciosBoundaryUpper_recompose
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off : UInt256)
    (hfit :
      (ciosBoundaryTk1 mem aw tEnd multiplyCarry tk1Off).toNat +
          (ciosBoundaryOverflow mem aw tEnd multiplyCarry).toNat < UInt256.size) :
    (ciosBoundaryTkNew mem aw tEnd multiplyCarry).toNat + UInt256.size *
        (ciosBoundaryTk1 mem aw tEnd multiplyCarry tk1Off +
          ciosBoundaryOverflow mem aw tEnd multiplyCarry).toNat =
      (ciosBoundaryTk mem aw tEnd).toNat + multiplyCarry.toNat + UInt256.size *
        (ciosBoundaryTk1 mem aw tEnd multiplyCarry tk1Off).toNat := by
  have hsum := evmAddCarry_recompose
    (ciosBoundaryTk mem aw tEnd) multiplyCarry
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit, Nat.mul_add]
  change (ciosBoundaryTk mem aw tEnd + multiplyCarry).toNat +
      UInt256.size *
        ((ciosBoundaryTk mem aw tEnd + multiplyCarry).lt
          (ciosBoundaryTk mem aw tEnd)).toNat =
      (ciosBoundaryTk mem aw tEnd).toNat + multiplyCarry.toNat at hsum
  simp only [ciosBoundaryTkNew, ciosBoundaryOverflow]
  omega

def ciosShiftTk (mem : ByteArray) (aw tEnd : UInt256) : UInt256 :=
  readWord mem aw tEnd

def ciosShiftSum
    (mem : ByteArray) (aw reductionCarry tEnd : UInt256) : UInt256 :=
  ciosShiftTk mem aw tEnd + reductionCarry

def ciosShiftAw1 (aw tEnd : UInt256) : UInt256 :=
  readWords1 aw tEnd

def ciosShiftMem1
    (mem : ByteArray) (aw reductionCarry shiftedOut tEnd : UInt256) : ByteArray :=
  (ciosShiftSum mem aw reductionCarry tEnd).toByteArray.write
    0 mem shiftedOut.toNat 32

def ciosShiftAw2 (aw shiftedOut tEnd : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ciosShiftAw1 aw tEnd).toNat shiftedOut.toNat 32)

def ciosShiftOverflow
    (mem : ByteArray) (aw reductionCarry tEnd : UInt256) : UInt256 :=
  (ciosShiftSum mem aw reductionCarry tEnd).lt (ciosShiftTk mem aw tEnd)

def ciosShiftTk1
    (mem : ByteArray)
    (aw reductionCarry shiftedOut tk1Off tEnd : UInt256) : UInt256 :=
  readWord (ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd)
    (ciosShiftAw2 aw shiftedOut tEnd) tk1Off

def ciosShiftAw3 (aw shiftedOut tk1Off tEnd : UInt256) : UInt256 :=
  readWords1 (ciosShiftAw2 aw shiftedOut tEnd) tk1Off

def ciosShiftMem2
    (mem : ByteArray)
    (aw reductionCarry shiftedOut tk1Off tEnd : UInt256) : ByteArray :=
  (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd +
      ciosShiftOverflow mem aw reductionCarry tEnd).toByteArray.write
    0 (ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd) tEnd.toNat 32

def ciosShiftAw4 (aw shiftedOut tk1Off tEnd : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (ciosShiftAw3 aw shiftedOut tk1Off tEnd).toNat tEnd.toNat 32)

def ciosShiftMemory
    (mem : ByteArray)
    (aw reductionCarry shiftedOut tk1Off tEnd : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (ciosShiftMem2 mem aw reductionCarry shiftedOut tk1Off tEnd) tk1Off.toNat 32

def ciosShiftAw (aw shiftedOut tk1Off tEnd : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (ciosShiftAw4 aw shiftedOut tk1Off tEnd).toNat tk1Off.toNat 32)

def ciosShiftGasAfter
    (C : Nat) (aw shiftedOut tk1Off tEnd : UInt256) : Nat :=
  let aw1 := ciosShiftAw1 aw tEnd
  let aw2 := ciosShiftAw2 aw shiftedOut tEnd
  let aw3 := ciosShiftAw3 aw shiftedOut tk1Off tEnd
  let aw4 := ciosShiftAw4 aw shiftedOut tk1Off tEnd
  let aw5 := ciosShiftAw aw shiftedOut tk1Off tEnd
  122 + C + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) +
    (Cₘ aw3 - Cₘ aw2) + (Cₘ aw4 - Cₘ aw3) +
    (Cₘ aw5 - Cₘ aw4)

/-- The first upper-limb write preserves the exact unbounded addition. -/
theorem ciosShiftSum_recompose
    (mem : ByteArray) (aw reductionCarry tEnd : UInt256) :
    (ciosShiftSum mem aw reductionCarry tEnd).toNat + UInt256.size *
        (ciosShiftOverflow mem aw reductionCarry tEnd).toNat =
      (ciosShiftTk mem aw tEnd).toNat + reductionCarry.toNat := by
  simpa only [ciosShiftSum, ciosShiftOverflow] using
    evmAddCarry_recompose (ciosShiftTk mem aw tEnd) reductionCarry

/-- Combining the shifted limb with the old extra word preserves the complete upper value.
The small-extra-word premise is the standard CIOS bound later maintained by the outer invariant. -/
theorem ciosShiftUpper_recompose
    (mem : ByteArray)
    (aw reductionCarry shiftedOut tk1Off tEnd : UInt256)
    (hfit :
      (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd).toNat +
          (ciosShiftOverflow mem aw reductionCarry tEnd).toNat < UInt256.size) :
    (ciosShiftSum mem aw reductionCarry tEnd).toNat + UInt256.size *
        (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd +
          ciosShiftOverflow mem aw reductionCarry tEnd).toNat =
      (ciosShiftTk mem aw tEnd).toNat + reductionCarry.toNat + UInt256.size *
        (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd).toNat := by
  have hsum := ciosShiftSum_recompose mem aw reductionCarry tEnd
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  rw [Nat.mul_add]
  omega

def ciosOuterAi (mem : ByteArray) (aw aOff : UInt256) : UInt256 :=
  readWord mem aw aOff

def ciosOuterAw (aw aOff : UInt256) : UInt256 :=
  readWords1 aw aOff

def ciosOuterGasAfter (C : Nat) (aw aOff : UInt256) : Nat :=
  63 + C + (Cₘ (ciosOuterAw aw aOff) - Cₘ aw)

/-- Exact setup of one CIOS outer iteration, through the first multiply-pass guard. -/
theorem ciosOuterToMultiplyGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {aOff bP nP shiftedOut tk1Off aEnd s6 s7 tP drop9 tEnd : UInt256}
    (hdepth : tail.length + 11 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (aOff :: bP :: nP :: shiftedOut :: tk1Off :: aEnd :: s6 :: s7 :: tP ::
        drop9 :: tEnd :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4337⟩
      (⟨4499⟩ :: tP.lt tEnd :: ciosOuterAi mem aw aOff :: bP :: tP :: ⟨0⟩ ::
        aOff :: bP :: nP :: shiftedOut :: tk1Off :: aEnd :: s6 :: s7 :: tP ::
        tEnd :: tail)
      mem (ciosOuterAw aw aOff) rdata acc (23 + k)
      (ciosOuterGasAfter C aw aOff) := by
  have rd := GeneratedTraces.trace_4312_body hdepth h
  simpa only [ciosOuterAi, ciosOuterAw, ciosOuterGasAfter, readWord, readWords1]
    using rd

/-- Exact upper-carry shift and return to the CIOS outer-loop guard. -/
theorem ciosReductionToOuterBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 reductionCarry aOff s5 s6 shiftedOut tk1Off aEnd
      s10 s11 s12 tEnd s14 s15 s16 : UInt256}
    (hdepth : tail.length + 17 ≤ 1023)
    (h : RDx runtimeBytecode ee g s0 ⟨4401⟩
      (drop0 :: drop1 :: drop2 :: reductionCarry :: aOff :: s5 :: s6 ::
        shiftedOut :: tk1Off :: aEnd :: s10 :: s11 :: s12 :: tEnd :: s14 ::
        s15 :: s16 :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4146⟩
      (⟨4312⟩ :: (aOff + ⟨32⟩).lt aEnd :: (aOff + ⟨32⟩) :: s5 :: s6 ::
        shiftedOut :: tk1Off :: aEnd :: s10 :: s11 :: s12 :: s16 :: tEnd :: s14 ::
        s15 :: s16 :: tail)
      (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd)
      (ciosShiftAw aw shiftedOut tk1Off tEnd)
      rdata acc (41 + k) (ciosShiftGasAfter C aw shiftedOut tk1Off tEnd) := by
  have rd := GeneratedTraces.trace_4401_body hdepth h
  simpa only [ciosShiftTk, ciosShiftSum, ciosShiftAw1, ciosShiftMem1,
    ciosShiftAw2, ciosShiftOverflow, ciosShiftTk1, ciosShiftAw3, ciosShiftMem2,
    ciosShiftAw4, ciosShiftMemory, ciosShiftAw, ciosShiftGasAfter, readWord,
    readWords1] using rd

/-- Exact carry propagation and peeled `j = 0` reduction block between the generated CIOS
multiply and reduction passes. -/
theorem ciosMultiplyToReductionBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 multiplyCarry s4 s5 n0inv s7 tk1Off s9 tOff nBefore
      tP tEnd nP : UInt256}
    (hdepth : tail.length + 15 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨4338⟩
      (drop0 :: drop1 :: drop2 :: multiplyCarry :: s4 :: s5 :: n0inv :: s7 ::
        tk1Off :: s9 :: tOff :: nBefore :: tP :: tEnd :: nP :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4400⟩
      (⟨4440⟩ :: tOff.lt tEnd :: (nBefore + ⟨64⟩) ::
        ciosBoundaryFactor mem aw tEnd multiplyCarry tk1Off tP n0inv :: tOff ::
        ciosBoundaryCarry mem aw tEnd multiplyCarry tk1Off tP nP n0inv ::
        s4 :: s5 :: n0inv :: s7 :: tk1Off :: s9 :: tOff :: nBefore :: tP ::
        tEnd :: nP :: tail)
      (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off)
      (ciosBoundaryAw aw tEnd tk1Off tP nP)
      rdata acc (59 + k) (ciosBoundaryGasAfter C aw tEnd tk1Off tP nP) := by
  have rd := GeneratedTraces.trace_4338_body hdepth h
  simpa only [ciosBoundaryTk, ciosBoundaryTkNew, ciosBoundaryMem1, ciosBoundaryAw1,
    ciosBoundaryAw2, ciosBoundaryOverflow, ciosBoundaryTk1, ciosBoundaryMem2,
    ciosBoundaryAw3, ciosBoundaryAw4, ciosBoundaryT0, ciosBoundaryAw5,
    ciosBoundaryN0, ciosBoundaryAw, ciosBoundaryFactor, ciosBoundaryCarry,
    ciosBoundaryGasAfter, readWord, readWords1, evmMulHigh,
    lnotZero_eq_max] using rd

/-- One exact generated CIOS multiply-pass body, including full product recovery, both carry
tests, the scratch write, pointer updates, next guard, and exact gas. -/
theorem multiplyPassBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {a operandPtr resultPtr carry s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (hdepth : tail.length + 14 ≤ 1015)
    (h : RDx runtimeBytecode ee g s0 ⟨4499⟩
      (a :: operandPtr :: resultPtr :: carry :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 ::
        s10 :: s11 :: s12 :: stop :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4337⟩
      (⟨4499⟩ :: (resultPtr + ⟨32⟩).lt stop :: a :: (operandPtr + ⟨32⟩) ::
        (resultPtr + ⟨32⟩) :: (schoolbookStep mem aw operandPtr resultPtr a carry).2 ::
        s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail)
      (multiplyPassMemory mem aw operandPtr resultPtr a carry)
      (multiplyPassAw aw operandPtr resultPtr)
      rdata acc (k + 55) (C + multiplyPassGas aw operandPtr resultPtr) := by
  have rd := GeneratedTraces.trace_4499_body hdepth h
  simpa [schoolbookStep, schoolbookOperands, multiplyPassMemory, multiplyPassAw,
    multiplyPassGas, readWord, readWords1, evmSchoolbookStep, evmMulHigh,
    lnotZero_eq_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- The generated multiply pass stores exactly the low limb of the unbounded column equation. -/
theorem multiplyPassMemory_word
    (mem : ByteArray) (aw operandPtr resultPtr a carry : UInt256)
    (hgap : resultPtr.toNat - mem.size < USize.size) :
    memoryWordNat (multiplyPassMemory mem aw operandPtr resultPtr a carry) resultPtr.toNat =
      (schoolbookStep mem aw operandPtr resultPtr a carry).1.toNat := by
  unfold multiplyPassMemory memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

structure MultiplyPassState where
  operandPtr : UInt256
  resultPtr : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def multiplyPassAdvance (a : UInt256) (s : MultiplyPassState) : MultiplyPassState where
  operandPtr := s.operandPtr + ⟨32⟩
  resultPtr := s.resultPtr + ⟨32⟩
  carry := (schoolbookStep s.memory s.activeWords s.operandPtr s.resultPtr a s.carry).2
  memory := multiplyPassMemory s.memory s.activeWords s.operandPtr s.resultPtr a s.carry
  activeWords := multiplyPassAw s.activeWords s.operandPtr s.resultPtr

def multiplyPassIterate (a : UInt256) : Nat → MultiplyPassState → MultiplyPassState
  | 0, s => s
  | n + 1, s => multiplyPassIterate a n (multiplyPassAdvance a s)

def multiplyPassIterationsGas (a : UInt256) : Nat → MultiplyPassState → Nat
  | 0, _ => 0
  | n + 1, s => multiplyPassGas s.activeWords s.operandPtr s.resultPtr + 10 +
      multiplyPassIterationsGas a n (multiplyPassAdvance a s)

def multiplyPassLoopStack (s : MultiplyPassState) (a : UInt256)
    (fixed : List UInt256) : List UInt256 :=
  a :: s.operandPtr :: s.resultPtr :: s.carry :: fixed

def multiplyPassOperandWords (a : UInt256) : Nat → MultiplyPassState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).1 ::
      multiplyPassOperandWords a n (multiplyPassAdvance a state)

def multiplyPassPriorWords (a : UInt256) : Nat → MultiplyPassState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).2.1 ::
      multiplyPassPriorWords a n (multiplyPassAdvance a state)

def multiplyPassOutputWords (a : UInt256) : Nat → MultiplyPassState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry).1 ::
      multiplyPassOutputWords a n (multiplyPassAdvance a state)

@[simp] theorem multiplyPassOperandWords_length
    (a : UInt256) (n : Nat) (state : MultiplyPassState) :
    (multiplyPassOperandWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [multiplyPassOperandWords, ih]

@[simp] theorem multiplyPassPriorWords_length
    (a : UInt256) (n : Nat) (state : MultiplyPassState) :
    (multiplyPassPriorWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [multiplyPassPriorWords, ih]

/-- The words read and written by the generated multiply pass form one exact pure schoolbook
row, including the final carry. -/
theorem multiplyPassCollectors_eq_row
    (a : UInt256) (n : Nat) (state : MultiplyPassState) :
    Modexp.evmSchoolbookRow a
      (multiplyPassOperandWords a n state)
      (multiplyPassPriorWords a n state) state.carry =
      (multiplyPassOutputWords a n state, (multiplyPassIterate a n state).carry) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [multiplyPassOperandWords, multiplyPassPriorWords,
        multiplyPassOutputWords, Modexp.evmSchoolbookRow, multiplyPassIterate]
      let step := schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry
      change
        (step.1 ::
            (Modexp.evmSchoolbookRow a
              (multiplyPassOperandWords a n (multiplyPassAdvance a state))
              (multiplyPassPriorWords a n (multiplyPassAdvance a state)) step.2).1,
          (Modexp.evmSchoolbookRow a
            (multiplyPassOperandWords a n (multiplyPassAdvance a state))
            (multiplyPassPriorWords a n (multiplyPassAdvance a state)) step.2).2) =
        (step.1 :: multiplyPassOutputWords a n (multiplyPassAdvance a state),
          (multiplyPassIterate a n (multiplyPassAdvance a state)).carry)
      have hcarry : step.2 = (multiplyPassAdvance a state).carry := by
        rfl
      rw [hcarry, ih (multiplyPassAdvance a state)]

/-- Unbounded arithmetic equation for all exact words observed by a multiply pass. -/
theorem multiplyPassCollectors_recompose
    (a : UInt256) (n : Nat) (state : MultiplyPassState) :
    Modexp.wordLimbsToNat (multiplyPassOutputWords a n state) +
        UInt256.size ^ n * (multiplyPassIterate a n state).carry.toNat =
      Modexp.wordLimbsToNat (multiplyPassPriorWords a n state) +
        a.toNat * Modexp.wordLimbsToNat (multiplyPassOperandWords a n state) +
        state.carry.toNat := by
  have hrow := Modexp.evmSchoolbookRow_recompose a
    (multiplyPassOperandWords a n state)
    (multiplyPassPriorWords a n state) state.carry
    (by simp)
  rw [multiplyPassCollectors_eq_row] at hrow
  simpa using hrow

@[simp] theorem multiplyPassIterate_advance (a : UInt256) (n : Nat)
    (s : MultiplyPassState) :
    multiplyPassIterate a n (multiplyPassAdvance a s) =
      multiplyPassIterate a (n + 1) s := by
  rfl

theorem multiplyPassAdvance_iterate (a : UInt256) (n : Nat)
    (s : MultiplyPassState) :
    multiplyPassAdvance a (multiplyPassIterate a n s) =
      multiplyPassIterate a (n + 1) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change multiplyPassAdvance a
        (multiplyPassIterate a n (multiplyPassAdvance a s)) =
          multiplyPassIterate a (n + 1) (multiplyPassAdvance a s)
      exact ih (multiplyPassAdvance a s)

theorem multiplyPassIterate_operandPtr_toNat
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hbound : state.operandPtr.toNat + 32 * n < UInt256.size) :
    (multiplyPassIterate a n state).operandPtr.toNat =
      state.operandPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => simp [multiplyPassIterate]
  | succ n ih =>
      rw [show multiplyPassIterate a (n + 1) state =
        multiplyPassIterate a n (multiplyPassAdvance a state) by rfl]
      have hstep : (multiplyPassAdvance a state).operandPtr.toNat =
          state.operandPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      rw [ih]
      · rw [hstep]
        omega
      · rw [hstep]
        omega

theorem multiplyPassIterate_resultPtr_toNat
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hbound : state.resultPtr.toNat + 32 * n < UInt256.size) :
    (multiplyPassIterate a n state).resultPtr.toNat =
      state.resultPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => simp [multiplyPassIterate]
  | succ n ih =>
      rw [show multiplyPassIterate a (n + 1) state =
        multiplyPassIterate a n (multiplyPassAdvance a state) by rfl]
      have hstep : (multiplyPassAdvance a state).resultPtr.toNat =
          state.resultPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      rw [ih]
      · rw [hstep]
        omega
      · rw [hstep]
        omega

/-- Contiguous no-wrap pointers determine all taken guards and the final exiting guard. -/
theorem multiplyPassGuardFacts
    (a stop : UInt256) (columns : Nat) (state : MultiplyPassState)
    (hcolumns : 0 < columns)
    (hbound : state.resultPtr.toNat + 32 * columns < UInt256.size)
    (hstop : stop.toNat = state.resultPtr.toNat + 32 * columns) :
    (∀ j, j < columns - 1 →
      (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩) ∧
    (multiplyPassAdvance a
      (multiplyPassIterate a (columns - 1) state)).resultPtr.lt stop = ⟨0⟩ := by
  have hiter (j : Nat) (hj : j < columns) :
      (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.toNat =
        state.resultPtr.toNat + 32 * (j + 1) := by
    rw [multiplyPassAdvance_iterate]
    rw [multiplyPassIterate_resultPtr_toNat]
    omega
  constructor
  · intro j hj
    have hlt :
        (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.toNat <
          stop.toNat := by
      rw [hiter j (by omega), hstop]
      omega
    rw [ult_one hlt]
    decide
  · have heq :
        (multiplyPassAdvance a
          (multiplyPassIterate a (columns - 1) state)).resultPtr.toNat = stop.toNat := by
      rw [hiter (columns - 1) (by omega), hstop]
      congr 1
      omega
    apply ult_zero
    omega

/-- Execute any number of generated CIOS multiply-pass bodies whose guard continues. -/
theorem multiplyPassIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (state : MultiplyPassState)
    (hdepth : tail.length + 14 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4499⟩
      (multiplyPassLoopStack state a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4499⟩
      (multiplyPassLoopStack (multiplyPassIterate a n state) a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      (multiplyPassIterate a n state).memory
      (multiplyPassIterate a n state).activeWords rdata acc
      (k + 56 * n) (C + multiplyPassIterationsGas a n state) := by
  induction n generalizing state k C with
  | zero => simpa [multiplyPassIterate, multiplyPassIterationsGas]
  | succ n ih =>
      have rd4337 := multiplyPassBody hdepth h
      have rdNext := rd4337.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (multiplyPassAdvance a
            (multiplyPassIterate a j (multiplyPassAdvance a state))).resultPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [multiplyPassIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := multiplyPassAdvance a state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 56 * (n + 1)) (by omega) rfl
      simpa [multiplyPassLoopStack, multiplyPassIterate, multiplyPassAdvance,
        multiplyPassIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

def multiplyPassThroughExitGas
    (a : UInt256) (n : Nat) (state : MultiplyPassState) : Nat :=
  multiplyPassIterationsGas a n state +
    multiplyPassGas (multiplyPassIterate a n state).activeWords
      (multiplyPassIterate a n state).operandPtr
      (multiplyPassIterate a n state).resultPtr + 10

/-- Execute the continuing multiply columns and the final column whose guard exits at PC 4338. -/
theorem multiplyPassThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (state : MultiplyPassState)
    (hdepth : tail.length + 14 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩)
    (hexit :
      (multiplyPassAdvance a (multiplyPassIterate a n state)).resultPtr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4499⟩
      (multiplyPassLoopStack state a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    let final := multiplyPassAdvance a (multiplyPassIterate a n state)
    RDx runtimeBytecode ee g s0 ⟨4338⟩
      (multiplyPassLoopStack final a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      final.memory final.activeWords rdata acc
      (k + 56 * (n + 1)) (C + multiplyPassThroughExitGas a n state) := by
  have rdIterations := multiplyPassIterations state hdepth hcontinue h
  have rdBody := multiplyPassBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 56 * (n + 1)) (by omega) rfl
  simpa [multiplyPassLoopStack, multiplyPassAdvance, multiplyPassThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-- The first half of one concrete CIOS outer iteration: load `a[i]`, execute every multiply
column, propagate its upper carry, and peel the zero reduction column. -/
theorem ciosOuterThroughPeeledReduction
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {aOff bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (hdepth : tail.length + 17 ≤ 1015)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hcontinue : ∀ j, j < n →
      (multiplyPassAdvance (ciosOuterAi mem aw aOff)
        (multiplyPassIterate (ciosOuterAi mem aw aOff) j
          { operandPtr := bP, resultPtr := tP, carry := ⟨0⟩,
            memory := mem, activeWords := ciosOuterAw aw aOff })).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hexit :
      (multiplyPassAdvance (ciosOuterAi mem aw aOff)
        (multiplyPassIterate (ciosOuterAi mem aw aOff) n
          { operandPtr := bP, resultPtr := tP, carry := ⟨0⟩,
            memory := mem, activeWords := ciosOuterAw aw aOff })).resultPtr.lt tEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff :: nBefore ::
        tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      mem aw rdata acc k C) :
    let ai := ciosOuterAi mem aw aOff
    let multiplyInitial : MultiplyPassState :=
      { operandPtr := bP, resultPtr := tP, carry := ⟨0⟩,
        memory := mem, activeWords := ciosOuterAw aw aOff }
    let multiplyFinal := multiplyPassAdvance ai (multiplyPassIterate ai n multiplyInitial)
    RDx runtimeBytecode ee g s0 ⟨4400⟩
      (⟨4440⟩ :: tOff.lt tEnd :: (nBefore + ⟨64⟩) ::
        ciosBoundaryFactor multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry tk1Off tP n0inv :: tOff ::
        ciosBoundaryCarry multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry tk1Off tP nP n0inv ::
        aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff :: nBefore ::
        tP :: tEnd :: nP :: tail0 :: tail1 :: tail)
      (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry tk1Off)
      (ciosBoundaryAw multiplyFinal.activeWords tEnd tk1Off tP nP)
      rdata acc (k + 83 + 56 * (n + 1))
      (ciosBoundaryGasAfter
        (ciosOuterGasAfter C aw aOff + 10 +
          multiplyPassThroughExitGas ai n multiplyInitial)
        multiplyFinal.activeWords tEnd tk1Off tP nP) := by
  let ai := ciosOuterAi mem aw aOff
  let multiplyInitial : MultiplyPassState :=
    { operandPtr := bP, resultPtr := tP, carry := ⟨0⟩,
      memory := mem, activeWords := ciosOuterAw aw aOff }
  let multiplyFinal := multiplyPassAdvance ai (multiplyPassIterate ai n multiplyInitial)
  have rdOuter := ciosOuterToMultiplyGuard
    (tail := nP :: tail0 :: tail1 :: tail)
    (by simp only [List.length_cons]; omega) h
  have rdStart := rdOuter.jumpiT (by native_decide) houter (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMultiply := multiplyPassThroughExit
    (s4 := aOff) (s5 := bP) (s6 := n0inv) (s7 := shiftedOut)
    (s8 := tk1Off) (s9 := aEnd) (s10 := tOff) (s11 := nBefore) (s12 := tP)
    (stop := tEnd) (tail := nP :: tail0 :: tail1 :: tail)
    multiplyInitial (by simp only [List.length_cons]; omega) hcontinue hexit
    (by
      simpa only [ai, multiplyInitial, multiplyPassLoopStack] using rdStart)
  have rdBoundary := ciosMultiplyToReductionBody (tail := tail0 :: tail1 :: tail)
    (by simp only [List.length_cons]; omega) (by
      simpa only [ai, multiplyInitial, multiplyFinal, multiplyPassLoopStack] using rdMultiply)
  have normalized := rdBoundary.withIndices
    (k' := k + 83 + 56 * (n + 1)) (by omega) rfl
  simpa only [ai, multiplyInitial, multiplyFinal, Nat.add_assoc] using normalized

/-- The second half of one concrete CIOS outer iteration: execute every remaining reduction
column, shift the upper limbs, clear the extra word, and return to the outer guard. -/
theorem ciosReductionThroughOuterGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {operandPtr factor resultPtr carry aOff bP n0inv shiftedOut tk1Off aEnd
      initialResult nBefore tP tEnd nP tail0 tail1 : UInt256}
    (hdepth : tail.length + 17 ≤ 1014)
    (hstart : resultPtr.lt tEnd ≠ ⟨0⟩)
    (hcontinue : ∀ j, j < n →
      (schoolbookAdvance factor
        (schoolbookIterate factor j
          { operandPtr := operandPtr, resultPtr := resultPtr, carry := carry,
            memory := mem, activeWords := aw })).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hexit :
      (schoolbookAdvance factor
        (schoolbookIterate factor n
          { operandPtr := operandPtr, resultPtr := resultPtr, carry := carry,
            memory := mem, activeWords := aw })).resultPtr.lt tEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4400⟩
      (⟨4440⟩ :: resultPtr.lt tEnd :: operandPtr :: factor :: resultPtr :: carry ::
        aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: initialResult ::
        nBefore :: tP :: tEnd :: nP :: tail0 :: tail1 :: tail)
      mem aw rdata acc k C) :
    let reductionInitial : SchoolbookState :=
      { operandPtr := operandPtr, resultPtr := resultPtr, carry := carry,
        memory := mem, activeWords := aw }
    let reductionFinal :=
      schoolbookAdvance factor (schoolbookIterate factor n reductionInitial)
    RDx runtimeBytecode ee g s0 ⟨4146⟩
      (⟨4312⟩ :: (aOff + ⟨32⟩).lt aEnd :: (aOff + ⟨32⟩) :: bP :: n0inv ::
        shiftedOut :: tk1Off :: aEnd :: initialResult :: nBefore :: tP :: tail1 ::
        tEnd :: nP :: tail0 :: tail1 :: tail)
      (ciosShiftMemory reductionFinal.memory reductionFinal.activeWords
        reductionFinal.carry shiftedOut tk1Off tEnd)
      (ciosShiftAw reductionFinal.activeWords shiftedOut tk1Off tEnd)
      rdata acc (k + 42 + 61 * (n + 1))
      (ciosShiftGasAfter
        (C + 10 + schoolbookThroughExitGas factor n reductionInitial)
        reductionFinal.activeWords shiftedOut tk1Off tEnd) := by
  let reductionInitial : SchoolbookState :=
    { operandPtr := operandPtr, resultPtr := resultPtr, carry := carry,
      memory := mem, activeWords := aw }
  let reductionFinal :=
    schoolbookAdvance factor (schoolbookIterate factor n reductionInitial)
  have rdStart := h.jumpiT (by native_decide) hstart (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdReduction := schoolbookThroughExit
    (s4 := aOff) (s5 := bP) (s6 := n0inv) (s7 := shiftedOut)
    (s8 := tk1Off) (s9 := aEnd) (s10 := initialResult) (s11 := nBefore)
    (s12 := tP) (stop := tEnd) (tail := nP :: tail0 :: tail1 :: tail)
    reductionInitial (by simp only [List.length_cons]; omega) hcontinue hexit
    (by simpa only [reductionInitial, schoolbookLoopStack] using rdStart)
  have rdShift := ciosReductionToOuterBody (tail := tail) (by omega) (by
    simpa only [reductionInitial, reductionFinal, schoolbookLoopStack] using rdReduction)
  have normalized := rdShift.withIndices
    (k' := k + 42 + 61 * (n + 1)) (by omega) rfl
  simpa only [reductionInitial, reductionFinal, Nat.add_assoc] using normalized

/-- Exact generated execution and its unbounded row equation, exposed together. -/
theorem multiplyPassIterations_exact_recompose
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (state : MultiplyPassState)
    (hdepth : tail.length + 14 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (multiplyPassAdvance a (multiplyPassIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4499⟩
      (multiplyPassLoopStack state a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4499⟩
        (multiplyPassLoopStack (multiplyPassIterate a n state) a
          (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
        (multiplyPassIterate a n state).memory
        (multiplyPassIterate a n state).activeWords rdata acc
        (k + 56 * n) (C + multiplyPassIterationsGas a n state) ∧
      Modexp.wordLimbsToNat (multiplyPassOutputWords a n state) +
          UInt256.size ^ n * (multiplyPassIterate a n state).carry.toNat =
        Modexp.wordLimbsToNat (multiplyPassPriorWords a n state) +
          a.toNat * Modexp.wordLimbsToNat (multiplyPassOperandWords a n state) +
          state.carry.toNat := by
  exact ⟨multiplyPassIterations state hdepth hcontinue h,
    multiplyPassCollectors_recompose a n state⟩

end Modexp.MultiLimbMontgomeryTrace
