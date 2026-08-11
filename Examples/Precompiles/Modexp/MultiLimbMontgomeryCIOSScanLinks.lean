import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSOutputLinks

/-! # Loop-wide CIOS scan semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Source limbs consumed by the generated outer loop, in execution order. -/
def ciosOuterDigits (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256) :
    Nat → CIOSOuterState → List Nat
  | 0, _ => []
  | iterations + 1, state =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
          iterations state ++
        [(ciosOuterAi current.memory current.activeWords current.aOff).toNat]

/-- The pure scan over an appended final digit is one final pure CIOS step. -/
theorem montgomeryCIOSScan_append_singleton
    (radix modulus nInv b t ai : Nat) (digits : List Nat) :
    Modexp.montgomeryCIOSScan radix modulus nInv b t (digits ++ [ai]) =
      Modexp.montgomeryCIOSStep radix modulus nInv b
        (Modexp.montgomeryCIOSScan radix modulus nInv b t digits) ai := by
  induction digits generalizing t with
  | nil => rfl
  | cons digit digits ih =>
      simpa only [List.cons_append, Modexp.montgomeryCIOSScan] using
        ih (Modexp.montgomeryCIOSStep radix modulus nInv b t digit)

/-- Iterating the generated CIOS outer transition is exactly the pure CIOS scan, assuming the
operand and modulus collectors retain their fixed values at each iteration. -/
theorem ciosOuterIterate_eq_montgomeryCIOSScan
    (iterations columns modulus multiplier : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0)
    (hmodulus : ∀ i, i < iterations →
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut i state
      ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        current = modulus)
    (hmultiplier : ∀ i, i < iterations →
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut i state
      ciosIterationMultiplier columns bP tP current = multiplier)
    (hinv : ∀ i, i < iterations →
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut i state
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP current).memory
        (ciosMultiplyFinal columns bP tP current).activeWords tEnd
        (ciosMultiplyFinal columns bP tP current).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1) :
    ciosScratchValue columns tP tEnd tk1Off
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) =
      Modexp.montgomeryCIOSScan UInt256.size modulus n0inv.toNat multiplier
        (ciosScratchValue columns tP tEnd tk1Off state)
        (ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      let digits := ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      let ai := (ciosOuterAi current.memory current.activeWords current.aOff).toNat
      have hcurrentLayout :=
        (ciosOuterIterate_layout iterations columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut state layout
          (fun i hi => haFit i (by omega))).1
      have hcurrentExtra := ciosOuterIterate_extraWord_zero iterations columns bP tP
        tEnd tk1Off nP n0inv tOff nBefore shiftedOut state layout
        (fun i hi => haFit i (by omega)) hextra
      have hstep := ciosScratchValue_outerAdvance_eq_montgomeryCIOSStep columns bP
        tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut current hcurrentLayout
        hcurrentExtra (by simpa only [current] using hinv iterations (by omega))
      have hfixedModulus :
          ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore
            current = modulus := by
        simpa only [current] using hmodulus iterations (by omega)
      have hfixedMultiplier : ciosIterationMultiplier columns bP tP current =
          multiplier := by
        simpa only [current] using hmultiplier iterations (by omega)
      rw [hfixedModulus, hfixedMultiplier] at hstep
      have hprevious := ih
        (fun i hi => haFit i (by omega))
        (fun i hi => hmodulus i (by omega))
        (fun i hi => hmultiplier i (by omega))
        (fun i hi => hinv i (by omega))
      calc
        ciosScratchValue columns tP tEnd tk1Off
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
              shiftedOut (iterations + 1) state) =
          ciosScratchValue columns tP tEnd tk1Off
            (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
              shiftedOut current) := by rfl
        _ = Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat multiplier
              (ciosScratchValue columns tP tEnd tk1Off current) ai := by
          simpa only [ai] using hstep
        _ = Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat multiplier
              (Modexp.montgomeryCIOSScan UInt256.size modulus n0inv.toNat multiplier
                (ciosScratchValue columns tP tEnd tk1Off state) digits) ai := by
          rw [show ciosScratchValue columns tP tEnd tk1Off current =
              Modexp.montgomeryCIOSScan UInt256.size modulus n0inv.toNat multiplier
                (ciosScratchValue columns tP tEnd tk1Off state) digits by
            simpa only [current, digits] using hprevious]
        _ = Modexp.montgomeryCIOSScan UInt256.size modulus n0inv.toNat multiplier
              (ciosScratchValue columns tP tEnd tk1Off state) (digits ++ [ai]) := by
          symm
          exact montgomeryCIOSScan_append_singleton UInt256.size modulus n0inv.toNat
            multiplier (ciosScratchValue columns tP tEnd tk1Off state) ai digits
        _ = Modexp.montgomeryCIOSScan UInt256.size modulus n0inv.toNat multiplier
              (ciosScratchValue columns tP tEnd tk1Off state)
              (ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore
                shiftedOut (iterations + 1) state) := by rfl

end Modexp.MultiLimbMontgomeryCIOSSemantic
