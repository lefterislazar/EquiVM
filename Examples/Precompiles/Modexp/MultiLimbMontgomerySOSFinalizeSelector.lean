import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalize

/-! # Executable exact SOS final comparison selector -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSFinalize

open Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSCompareSelection where
  tOff : UInt256
  nOff : UInt256
  activeWords : UInt256
  doSub : UInt256
  steps : Nat
  gas : Nat

/-- Follow the deployed descending comparison, with explicit fuel for totality. -/
def selectSOSCompare (fuel : Nat) (mem : ByteArray)
    (tP activeWords tOff nOff prevTOff : UInt256) : Option SOSCompareSelection :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if (compareNWord mem activeWords tOff nOff).toNat <
          (compareTWord mem activeWords tOff).toNat then
        some {
          tOff := tP
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨1⟩
          steps := 45
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 97 }
      else if (compareTWord mem activeWords tOff).toNat <
          (compareNWord mem activeWords tOff nOff).toNat then
        some {
          tOff := tP
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨0⟩
          steps := 47
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 101 }
      else if prevTOff.gt tP ≠ ⟨0⟩ then
        match selectSOSCompare fuel mem tP (compareAw activeWords tOff nOff)
            prevTOff (comparePrev nOff) (comparePrev prevTOff) with
        | none => none
        | some rest => some {
            tOff := rest.tOff
            nOff := rest.nOff
            activeWords := rest.activeWords
            doSub := rest.doSub
            steps := 39 + rest.steps
            gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 + rest.gas }
      else
        some {
          tOff := prevTOff
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨1⟩
          steps := 39
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 }

/-- The selector's returned option directly describes its exact deployed trace. -/
theorem sosCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {tP junk resultPtr nP bytes : UInt256}
    {activeWords tOff nOff prevTOff : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hprev : prevTOff = comparePrev tOff)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk ::
        ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem activeWords rdata acc k C) :
    match selectSOSCompare fuel mem tP activeWords tOff nOff prevTOff with
    | none => True
    | some selected =>
        SOSComparePost ee g s0 selected.tOff selected.nOff tP bytes
          selected.doSub resultPtr nP tail mem selected.activeWords rdata acc
          (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing activeWords tOff nOff prevTOff k C junk with
  | zero => simp [selectSOSCompare]
  | succ fuel ih =>
      simp only [selectSOSCompare]
      by_cases hgreater :
          (compareNWord mem activeWords tOff nOff).toNat <
            (compareTWord mem activeWords tOff).toNat
      · rw [if_pos hgreater]
        exact sosCompareGreaterToCopy
          (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
          (k := k) (C := C)
          (mem := mem) (aw := activeWords)
          (tail := tail) (tOff := tOff) (nOff := nOff)
          (tP := tP) (junk := junk) (resultPtr := resultPtr)
          (nP := nP) (bytes := bytes) hdepth hgreater h
      · rw [if_neg hgreater]
        by_cases hless :
            (compareTWord mem activeWords tOff).toNat <
              (compareNWord mem activeWords tOff nOff).toNat
        · rw [if_pos hless]
          exact sosCompareLessToCopy
            (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
            (k := k) (C := C)
            (mem := mem) (aw := activeWords)
            (tail := tail) (tOff := tOff) (nOff := nOff)
            (tP := tP) (junk := junk) (resultPtr := resultPtr)
            (nP := nP) (bytes := bytes) hdepth hless h
        · rw [if_neg hless]
          have hequal : compareTWord mem activeWords tOff =
              compareNWord mem activeWords tOff nOff := by
            apply u256_inj
            omega
          by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
          · rw [if_pos hguard]
            have hcontinuePrev : tP.toNat < prevTOff.toNat := by
              by_contra hnot
              apply hguard
              exact ugt_zero (by omega)
            have hcontinue : tP.toNat < (comparePrev tOff).toNat := by
              rw [← hprev]
              exact hcontinuePrev
            let nextAw := compareAw activeWords tOff nOff
            let nextTOff := prevTOff
            let nextNOff := comparePrev nOff
            let nextPrevTOff := comparePrev prevTOff
            cases hrest : selectSOSCompare fuel mem tP nextAw nextTOff nextNOff
                nextPrevTOff with
            | none => exact True.intro
            | some rest =>
                change SOSComparePost ee g s0 rest.tOff rest.nOff tP bytes
                  rest.doSub resultPtr nP tail mem rest.activeWords rdata acc
                  (k + (39 + rest.steps))
                  (C + (compareLoadGasAfter 0 activeWords tOff nOff + 77 +
                    rest.gas))
                have rdNext := sosCompareEqualContinue hdepth hequal hcontinue h
                have rdFinal := ih (junk := bytes) (activeWords := nextAw)
                  (tOff := nextTOff) (nOff := nextNOff)
                  (prevTOff := nextPrevTOff) (by
                    simpa [nextPrevTOff, nextTOff]) (by
                    simpa [nextAw, nextTOff, nextNOff, hprev] using rdNext)
                rw [hrest] at rdFinal
                simpa only [Nat.add_assoc] using rdFinal
          · rw [if_neg hguard]
            have hexitPrev : prevTOff.toNat ≤ tP.toNat := by
              by_contra hnot
              have hone := ugt_one (show tP.toNat < prevTOff.toNat by omega)
              apply hguard
              rw [hone]
              native_decide
            have hexit : (comparePrev tOff).toNat ≤ tP.toNat := by
              rw [← hprev]
              exact hexitPrev
            have rd := sosCompareEqualExit hdepth hequal hexit h
            simpa only [hprev] using rd

/-- Every successful named SOS comparison selection is its exact deployed trace. -/
theorem selectedSOSCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {tP junk resultPtr nP bytes : UInt256}
    {activeWords tOff nOff prevTOff : UInt256} (selected : SOSCompareSelection)
    (hdepth : tail.length + 8 ≤ 1021)
    (hprev : prevTOff = comparePrev tOff)
    (hselect : selectSOSCompare fuel mem tP activeWords tOff nOff prevTOff = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk ::
        ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem activeWords rdata acc k C) :
    SOSComparePost ee g s0 selected.tOff selected.nOff tP bytes
      selected.doSub resultPtr nP tail mem selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  have rd := sosCompareExact (fuel := fuel) hdepth hprev h
  rw [hselect] at rd
  exact rd

end Modexp.MultiLimbMontgomerySOSFinalize
