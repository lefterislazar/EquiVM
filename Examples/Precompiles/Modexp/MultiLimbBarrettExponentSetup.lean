import Examples.Precompiles.Modexp.MultiLimbBarrettExponentTrace
import Examples.Precompiles.Modexp.MultiLimbBarrettExponentLoop

/-!
# Executable Barrett exponent setup

This module exposes the two data-dependent setup scans in `_barrettModexpLoop`: leading zero
exponent bytes and leading zero bits in the first nonzero byte. The selectors retain every branch,
so their step and gas totals compose with the byte-loop selector without existential gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettExponentSetup

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbBarrettExponentLoop
open Modexp.MultiLimbBarrettExponentTrace
open Modexp.MultiLimbExponentTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

inductive BarrettTopBitSelection where
  | zeroCursor
  | setBit (topBit : UInt256)
  | skipZero (rest : BarrettTopBitSelection)

namespace BarrettTopBitSelection

def topBit : BarrettTopBitSelection → UInt256
  | .zeroCursor => ⟨0⟩
  | .setBit topBit => topBit
  | .skipZero rest => rest.topBit

def steps : BarrettTopBitSelection → Nat
  | .zeroCursor => 21
  | .setBit _ => 33
  | .skipZero rest => 40 + rest.steps

def gas : BarrettTopBitSelection → Nat
  | .zeroCursor => 70
  | .setBit _ => 108
  | .skipZero rest => 149 + rest.gas

end BarrettTopBitSelection

def selectBarrettTopBit : Nat → UInt256 → UInt256 → Option BarrettTopBitSelection
  | 0, _, _ => none
  | fuel + 1, byte, topBit =>
      if topBit = ⟨0⟩ then some .zeroCursor
      else if barrettTopBitTest byte topBit ≠ ⟨0⟩ then some (.setBit topBit)
      else match selectBarrettTopBit fuel byte (topBit - ⟨1⟩) with
        | some rest => some (.skipZero rest)
        | none => none

/-- One unit of fuel per remaining bit, including the terminal zero cursor, makes the top-bit
selector total. -/
theorem selectBarrettTopBit_exists
    {fuel : Nat} {byte topBit : UInt256} (hfuel : topBit.toNat < fuel) :
    ∃ selected, selectBarrettTopBit fuel byte topBit = some selected := by
  induction fuel generalizing topBit with
  | zero => omega
  | succ fuel ih =>
      by_cases hzero : topBit = ⟨0⟩
      · simp [selectBarrettTopBit, hzero]
      · by_cases hset : barrettTopBitTest byte topBit ≠ ⟨0⟩
        · simp [selectBarrettTopBit, hzero, hset]
        · have htopPos : 0 < topBit.toNat := by
            apply Nat.pos_of_ne_zero
            intro hnat
            apply hzero
            apply u256_inj
            simpa using hnat
          have hprevious : (topBit - ⟨1⟩).toNat = topBit.toNat - 1 := by
            change (UInt256.sub topBit ⟨1⟩).toNat = topBit.toNat - 1
            have hone : (⟨1⟩ : UInt256).toNat = 1 := by decide
            rw [usub_toNat (by rw [hone]; omega), hone]
          have hrestFuel : (topBit - ⟨1⟩).toNat < fuel := by
            rw [hprevious]
            omega
          rcases ih hrestFuel with ⟨rest, hrest⟩
          simp only [selectBarrettTopBit, hzero, if_false, hset]
          rw [hrest]
          exact ⟨_, rfl⟩

inductive BarrettTopBitValid (byte : UInt256) :
    UInt256 → BarrettTopBitSelection → Prop where
  | zeroCursor : BarrettTopBitValid byte ⟨0⟩ .zeroCursor
  | setBit {topBit : UInt256}
      (positive : topBit ≠ ⟨0⟩)
      (bitSet : barrettTopBitTest byte topBit ≠ ⟨0⟩) :
      BarrettTopBitValid byte topBit (.setBit topBit)
  | skipZero {topBit : UInt256} {rest : BarrettTopBitSelection}
      (positive : topBit ≠ ⟨0⟩)
      (bitZero : barrettTopBitTest byte topBit = ⟨0⟩)
      (restValid : BarrettTopBitValid byte (topBit - ⟨1⟩) rest) :
      BarrettTopBitValid byte topBit (.skipZero rest)

theorem selectBarrettTopBit_valid
    {fuel : Nat} {byte topBit : UInt256} {selected : BarrettTopBitSelection}
    (hselect : selectBarrettTopBit fuel byte topBit = some selected) :
    BarrettTopBitValid byte topBit selected := by
  induction fuel generalizing topBit selected with
  | zero => simp [selectBarrettTopBit] at hselect
  | succ fuel ih =>
      simp only [selectBarrettTopBit] at hselect
      split at hselect
      next hzero =>
        cases hselect
        subst topBit
        exact .zeroCursor
      next hpositive =>
        split at hselect
        next hset =>
          cases hselect
          exact .setBit hpositive hset
        next hzero =>
          split at hselect
          next rest hrest =>
            cases hselect
            exact .skipZero hpositive (not_ne_iff.mp hzero) (ih hrest)
          next => contradiction

/-- A valid top-bit scan never returns a bit above its initial cursor. -/
theorem BarrettTopBitValid.topBit_le
    {byte startBit : UInt256} {selected : BarrettTopBitSelection}
    (valid : BarrettTopBitValid byte startBit selected) :
    selected.topBit.toNat ≤ startBit.toNat := by
  induction valid with
  | zeroCursor => simp [BarrettTopBitSelection.topBit]
  | setBit => simp [BarrettTopBitSelection.topBit]
  | @skipZero topBit rest positive bitZero restValid ih =>
      simp only [BarrettTopBitSelection.topBit]
      have hpos : 0 < topBit.toNat := by
        apply Nat.pos_of_ne_zero
        intro hnat
        apply positive
        apply u256_inj
        simpa using hnat
      have hone : (⟨1⟩ : UInt256).toNat = 1 := by decide
      have hprevious : (topBit - ⟨1⟩).toNat = topBit.toNat - 1 := by
        change (UInt256.sub topBit ⟨1⟩).toNat = topBit.toNat - 1
        rw [usub_toNat (by rw [hone]; omega), hone]
      rw [hprevious] at ih
      omega

theorem BarrettTopBitValid.exact
    {byte topBit : UInt256} {selected : BarrettTopBitSelection}
    (valid : BarrettTopBitValid byte topBit selected)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent mu freeMemBase a words expLen n r : UInt256}
    (hdepth : tail.length + 11 ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack topBit startByte exponent mu freeMemBase a words expLen n r byte tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack startByte exponent selected.topBit mu freeMemBase a words
        expLen n r tail)
      mem aw rdata acc (steps + selected.steps) (gasUsed + selected.gas) := by
  induction valid generalizing steps gasUsed with
  | zeroCursor =>
      simpa [BarrettTopBitSelection.topBit, BarrettTopBitSelection.steps,
        BarrettTopBitSelection.gas] using barrettTopBitZeroCursorToByteGuard hdepth h
  | setBit positive bitSet =>
      simpa [BarrettTopBitSelection.topBit, BarrettTopBitSelection.steps,
        BarrettTopBitSelection.gas] using
        barrettTopBitSetToByteGuard hdepth positive bitSet h
  | @skipZero topBit rest positive bitZero restValid ih =>
      have rdNext := barrettTopBitZeroToGuard hdepth positive bitZero h
      have rdFinal := ih (steps := steps + 40) (gasUsed := gasUsed + 149)
        (by simpa [barrettTopBitStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using rdNext)
      simpa [BarrettTopBitSelection.topBit, BarrettTopBitSelection.steps,
        BarrettTopBitSelection.gas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

inductive BarrettLeadingScanSelection where
  | exhausted (memory : ByteArray) (activeWords startByte : UInt256)
  | found (memory : ByteArray) (activeWords startByte scanWord : UInt256) (loadGas : Nat)
  | skipZero (scanWord : UInt256) (loadGas : Nat) (rest : BarrettLeadingScanSelection)

namespace BarrettLeadingScanSelection

def memory : BarrettLeadingScanSelection → ByteArray
  | .exhausted mem _ _ => mem
  | .found mem _ _ _ _ => mem
  | .skipZero _ _ rest => rest.memory

def activeWords : BarrettLeadingScanSelection → UInt256
  | .exhausted _ aw _ => aw
  | .found _ aw _ _ _ => aw
  | .skipZero _ _ rest => rest.activeWords

def startByte : BarrettLeadingScanSelection → UInt256
  | .exhausted _ _ startByte => startByte
  | .found _ _ startByte _ _ => startByte
  | .skipZero _ _ rest => rest.startByte

def isExhausted : BarrettLeadingScanSelection → Bool
  | .exhausted .. => true
  | .found .. => false
  | .skipZero _ _ rest => rest.isExhausted

def steps : BarrettLeadingScanSelection → Nat
  | .exhausted .. => 11
  | .found .. => 45
  | .skipZero _ _ rest => 63 + rest.steps

def gas : BarrettLeadingScanSelection → Nat
  | .exhausted .. => 43
  | .found _ _ _ _ loadGas => loadGas + 17
  | .skipZero _ loadGas rest => loadGas + 88 + rest.gas

end BarrettLeadingScanSelection

def selectBarrettLeadingScan : Nat → ByteArray → UInt256 → UInt256 → UInt256 →
    UInt256 → Option BarrettLeadingScanSelection
  | 0, _, _, _, _, _ => none
  | fuel + 1, mem, aw, exponent, expLen, startByte =>
      if startByte.lt expLen = ⟨0⟩ then some (.exhausted mem aw startByte) else
      let aw' := exponentByteLoadAw aw exponent startByte
      let scanWord := barrettScanMaskedWord mem (exponentArrayLengthAw aw exponent)
        exponent startByte
      let loadGas := barrettScanLoadGas aw exponent startByte
      if scanWord = ⟨0⟩ then
        match selectBarrettLeadingScan fuel mem aw' exponent expLen (startByte + ⟨1⟩) with
        | some rest => some (.skipZero scanWord loadGas rest)
        | none => none
      else some (.found mem aw' startByte scanWord loadGas)

/-- The leading-byte scan is total with one fuel unit per remaining byte plus the terminal guard
check. -/
theorem selectBarrettLeadingScan_exists
    {fuel : Nat} {mem : ByteArray} {aw exponent expLen startByte : UInt256}
    (hfuel : expLen.toNat - startByte.toNat < fuel) :
    ∃ selected,
      selectBarrettLeadingScan fuel mem aw exponent expLen startByte = some selected := by
  induction fuel generalizing aw startByte with
  | zero => omega
  | succ fuel ih =>
      by_cases hguard : startByte.lt expLen = ⟨0⟩
      · simp [selectBarrettLeadingScan, hguard]
      · have hidxLt : startByte.toNat < expLen.toNat := by
          by_contra hnot
          exact hguard (ult_zero (by omega))
        let aw' := exponentByteLoadAw aw exponent startByte
        let scanWord := barrettScanMaskedWord mem (exponentArrayLengthAw aw exponent)
          exponent startByte
        let loadGas := barrettScanLoadGas aw exponent startByte
        by_cases hword : scanWord = ⟨0⟩
        · have hexpFit : expLen.toNat < UInt256.size := expLen.val.isLt
          have hnextFit : startByte.toNat + 1 < UInt256.size := by omega
          have hnextNat : (startByte + ⟨1⟩).toNat = startByte.toNat + 1 := by
            rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
              Nat.mod_eq_of_lt hnextFit]
          have hrestFuel : expLen.toNat - (startByte + ⟨1⟩).toNat < fuel := by
            rw [hnextNat]
            omega
          rcases ih (aw := aw') hrestFuel with ⟨rest, hrest⟩
          simp only [selectBarrettLeadingScan, hguard, if_false]
          rw [if_pos hword, hrest]
          exact ⟨_, rfl⟩
        · simp only [selectBarrettLeadingScan, hguard, if_false]
          rw [if_neg hword]
          exact ⟨_, rfl⟩

inductive BarrettLeadingScanValid (exponent expLen : UInt256) :
    ByteArray → UInt256 → UInt256 → BarrettLeadingScanSelection → Prop where
  | exhausted {mem aw startByte}
      (guardZero : startByte.lt expLen = ⟨0⟩) :
      BarrettLeadingScanValid exponent expLen mem aw startByte (.exhausted mem aw startByte)
  | found {mem aw startByte scanWord}
      (guardSet : startByte.lt expLen ≠ ⟨0⟩)
      (indexValid : (startByte.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
      (wordEq : scanWord = barrettScanMaskedWord mem
        (exponentArrayLengthAw aw exponent) exponent startByte)
      (wordNonzero : scanWord ≠ ⟨0⟩) :
      BarrettLeadingScanValid exponent expLen mem aw startByte
        (.found mem (exponentByteLoadAw aw exponent startByte) startByte scanWord
          (barrettScanLoadGas aw exponent startByte))
  | skipZero {mem aw startByte scanWord rest}
      (guardSet : startByte.lt expLen ≠ ⟨0⟩)
      (indexValid : (startByte.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
      (wordEq : scanWord = barrettScanMaskedWord mem
        (exponentArrayLengthAw aw exponent) exponent startByte)
      (wordZero : scanWord = ⟨0⟩)
      (incrementValid : startByte ≠ UInt256.lnot ⟨0⟩)
      (restValid : BarrettLeadingScanValid exponent expLen mem
        (exponentByteLoadAw aw exponent startByte) (startByte + ⟨1⟩) rest) :
      BarrettLeadingScanValid exponent expLen mem aw startByte
        (.skipZero scanWord (barrettScanLoadGas aw exponent startByte) rest)

theorem selectBarrettLeadingScan_valid
    {fuel : Nat} {mem : ByteArray} {aw exponent expLen startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (hindex : ∀ (aw' startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      (startByte'.lt (exponentArrayLength mem aw' exponent)).isZero = ⟨0⟩)
    (hinc : ∀ (startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hselect : selectBarrettLeadingScan fuel mem aw exponent expLen startByte = some selected) :
    BarrettLeadingScanValid exponent expLen mem aw startByte selected := by
  induction fuel generalizing aw startByte selected with
  | zero => simp [selectBarrettLeadingScan] at hselect
  | succ fuel ih =>
      simp only [selectBarrettLeadingScan] at hselect
      split at hselect
      next hguard =>
        cases hselect
        exact .exhausted hguard
      next hguard =>
        split at hselect
        next hzero =>
          split at hselect
          next rest hrest =>
            cases hselect
            exact .skipZero hguard (hindex aw startByte hguard) rfl hzero
              (hinc startByte hguard) (ih hrest)
          next => contradiction
        next hnonzero =>
          cases hselect
          exact .found hguard (hindex aw startByte hguard) rfl hnonzero

theorem BarrettLeadingScanValid.memoryEq
    {mem : ByteArray} {aw exponent expLen startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected) :
    selected.memory = mem := by
  induction valid with
  | exhausted => rfl
  | found => rfl
  | skipZero _ _ _ _ _ _ ih => exact ih

/-- Selector-tied leading-scan validity.  The dynamic-array guard is recovered from the one
concrete exponent header under each actual active-word counter reached by the scan. -/
theorem selectBarrettLeadingScan_validInvariantFramed
    {I : ExecutionEnv} {fuel kWords fp rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent expLen startByte r a n mu : UInt256}
    {selected : BarrettLeadingScanSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hinc : forall startByte', startByte'.lt expLen ≠ ⟨0⟩ ->
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hselect : selectBarrettLeadingScan fuel mem aw exponent expLen startByte = some selected) :
    BarrettLeadingScanValid exponent expLen mem aw startByte selected /\
      InitialBarrettExponentInvariant I selected.memory selected.activeWords kWords fp
        r a n mu rValue baseValue nValue := by
  induction fuel generalizing aw startByte selected with
  | zero => simp [selectBarrettLeadingScan] at hselect
  | succ fuel ih =>
      simp only [selectBarrettLeadingScan] at hselect
      split at hselect
      next hguard =>
        cases hselect
        exact ⟨.exhausted hguard, invariant⟩
      next hguard =>
        have hlength : exponentArrayLength mem aw exponent = expLen :=
          exponentArrayLength_eq_of_header invariant.covered invariant.activeWordsFit
            access.headerConcrete access.header
        have hindex : (startByte.lt (exponentArrayLength mem aw exponent)).isZero =
            ⟨0⟩ := by
          rw [hlength]
          exact isZero_eq_zero_of_ne hguard
        have loaded := invariant.afterExponentByteLoad access.exponentFit
          (access.byteFit startByte hguard)
        split at hselect
        next hzero =>
          split at hselect
          next rest hrest =>
            cases hselect
            rcases ih loaded hrest with ⟨restValid, restInvariant⟩
            exact ⟨.skipZero hguard hindex rfl hzero (hinc startByte hguard) restValid,
              restInvariant⟩
          next => contradiction
        next hnonzero =>
          cases hselect
          exact ⟨.found hguard hindex rfl hnonzero, loaded⟩

/-- The leading-zero scan is read-only. Its checked length/byte loads preserve every arithmetic
fact in the persistent Barrett invariant while updating the active-word counter exactly. -/
theorem BarrettLeadingScanValid.preserveInvariant
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : ∀ (idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size) :
    BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
      rValue baseValue nValue := by
  induction valid with
  | exhausted =>
      simpa [BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords] using invariant
  | @found aw startByte scanWord guardSet indexValid wordEq wordNonzero =>
      have loaded := invariant.afterExponentByteLoad hexponentFit
        (hbyteFit startByte guardSet)
      simpa [BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords] using loaded
  | @skipZero aw startByte scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have loaded := invariant.afterExponentByteLoad hexponentFit
        (hbyteFit startByte guardSet)
      exact ih loaded

/-- A selected non-exhausted scan ends at a byte whose loop guard is set. -/
theorem BarrettLeadingScanValid.finalGuardSet
    {exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (hnonexhausted : selected.isExhausted = false) :
    selected.startByte.lt expLen ≠ ⟨0⟩ := by
  induction valid with
  | exhausted =>
      simp [BarrettLeadingScanSelection.isExhausted] at hnonexhausted
  | found guardSet =>
      simpa [BarrettLeadingScanSelection.startByte] using guardSet
  | skipZero _ _ _ _ _ restValid ih =>
      exact ih hnonexhausted

/-- A valid leading scan is exhausted exactly at the exponent length; every non-exhausted result
stops strictly before it.  This follows from the selected scan recursion and does not require a
separate path assumption. -/
theorem BarrettLeadingScanValid.exhaustionStart
    {exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (hstartLe : startByte.toNat ≤ expLen.toNat) :
    (selected.isExhausted = true → selected.startByte = expLen) ∧
      (selected.isExhausted = false → selected.startByte ≠ expLen) := by
  induction valid with
  | @exhausted aw current guardZero =>
      constructor
      · intro _
        apply u256_inj
        have hnotLt : ¬ current.toNat < expLen.toNat := by
          intro hlt
          have hone := ult_one (a := current) (b := expLen) hlt
          exact (by native_decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
            (hone.symm.trans guardZero)
        have hreverse : expLen.toNat ≤ current.toNat := by omega
        simpa [BarrettLeadingScanSelection.startByte] using
          Nat.le_antisymm hstartLe hreverse
      · simp [BarrettLeadingScanSelection.isExhausted]
  | @found aw current scanWord guardSet indexValid wordEq wordNonzero =>
      constructor
      · simp [BarrettLeadingScanSelection.isExhausted]
      · intro _ heq
        have heq' : current = expLen := by
          simpa [BarrettLeadingScanSelection.startByte] using heq
        rw [heq'] at guardSet
        exact guardSet (ult_zero (by omega))
  | @skipZero aw current scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have hcurrentLt : current.toNat < expLen.toNat := by
        by_contra hnot
        exact guardSet (ult_zero (by omega))
      have hnextNat : (current + ⟨1⟩).toNat = current.toNat + 1 := by
        have hlenFit : expLen.toNat < UInt256.size := by
          simpa [UInt256.toNat] using expLen.val.isLt
        rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
          Nat.mod_eq_of_lt (by omega)]
      have hnextLe : (current + ⟨1⟩).toNat ≤ expLen.toNat := by
        rw [hnextNat]
        omega
      exact ih hnextLe

theorem BarrettLeadingScanValid.exact
    {exponent expLen mem aw startByte selected}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {a words n r mu : UInt256}
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨3162⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3190⟩
      (barrettSetupStack selected.startByte exponent a words expLen n r mu tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction valid generalizing k C with
  | exhausted guardZero =>
      simpa [BarrettLeadingScanSelection.startByte, BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords, BarrettLeadingScanSelection.steps,
        BarrettLeadingScanSelection.gas] using
        barrettScanExhaustedToExit (by omega) guardZero h
  | @found aw0 start0 scanWord guardSet indexValid wordEq wordNonzero =>
      have rd3171 := barrettScanByteExact (by omega) guardSet indexValid h
      have rd3190 := barrettScanNonzeroToExit (tail := tail) (scanWord := scanWord)
        (by omega) wordNonzero (by
        simpa [wordEq] using rd3171)
      simpa [BarrettLeadingScanSelection.startByte, BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords, BarrettLeadingScanSelection.steps,
        BarrettLeadingScanSelection.gas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using rd3190
  | @skipZero aw0 start0 scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have rd3171 := barrettScanByteExact (by omega) guardSet indexValid h
      have rdNext := barrettScanZeroToGuard (by omega) wordZero incrementValid (by
        simpa [wordEq] using rd3171)
      have rdFinal := ih (k := k + 63)
        (C := C + barrettScanLoadGas aw0 exponent start0 + 88) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      simpa [BarrettLeadingScanSelection.startByte, BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords, BarrettLeadingScanSelection.steps,
        BarrettLeadingScanSelection.gas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using rdFinal

inductive BarrettLoopSetupSelection where
  | allZero (scan : BarrettLeadingScanSelection)
  | nonzero (scan : BarrettLeadingScanSelection) (top : BarrettTopBitSelection)
      (bytes : BarrettByteLoopSelection)

namespace BarrettLoopSetupSelection

def memory : BarrettLoopSetupSelection → ByteArray
  | .allZero scan => scan.memory
  | .nonzero _ _ bytes => bytes.memory

def activeWords : BarrettLoopSetupSelection → UInt256
  | .allZero scan => scan.activeWords
  | .nonzero _ _ bytes => bytes.activeWords

def steps : BarrettLoopSetupSelection → Nat
  | .allZero scan => 8 + scan.steps + 18
  | .nonzero scan top bytes => 8 + scan.steps + 45 + top.steps + bytes.steps + 17

def gas (initialAw exponent : UInt256) : BarrettLoopSetupSelection → Nat
  | .allZero scan => barrettSetupGas initialAw exponent + scan.gas + 55
  | .nonzero scan top bytes =>
      barrettSetupGas initialAw exponent + scan.gas +
        barrettTopByteLoadGas scan.activeWords exponent scan.startByte +
        top.gas + bytes.gas + 52

end BarrettLoopSetupSelection

def selectBarrettLoopSetup (scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat)
    (mem : ByteArray) (aw exponent r a n mu expLen : UInt256) :
    Option BarrettLoopSetupSelection :=
  let scanAw := exponentArrayLengthAw aw exponent
  match selectBarrettLeadingScan scanFuel mem scanAw exponent expLen ⟨0⟩ with
  | none => none
  | some scan =>
      if scan.isExhausted then some (.allZero scan) else
      let aw0 := readWords1 scan.activeWords ⟨64⟩
      let aw1 := exponentArrayLengthAw aw0 exponent
      let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
      let byte := barrettExponentByteValue scan.memory aw1 exponent scan.startByte
      match selectBarrettTopBit topFuel byte ⟨7⟩ with
      | none => none
      | some top =>
          match selectBarrettByteLoop byteFuel bitFuel callFuel scan.memory aw2 kWords fp
              scan.startByte exponent top.topBit expLen r a n mu with
          | none => none
          | some bytes => some (.nonzero scan top bytes)

/-- Canonical exposed selector for arbitrary exponent data. Every fuel component is a concrete
input-derived bound; it does not contribute an existential or approximate gas quantity. -/
def selectCompleteBarrettLoopSetup (kWords fp : Nat)
    (mem : ByteArray) (aw exponent r a n mu expLen : UInt256) :
    Option BarrettLoopSetupSelection :=
  selectBarrettLoopSetup (expLen.toNat + 1) 8 expLen.toNat 8 kWords kWords fp
    mem aw exponent r a n mu expLen

/-- The canonical selector exposes a concrete all-zero or nonzero execution path for every
positive limb count and arbitrary bounded exponent memory. -/
theorem selectCompleteBarrettLoopSetup_exists
    {kWords fp : Nat} {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    (hkPos : 0 < kWords) :
    ∃ selected,
      selectCompleteBarrettLoopSetup kWords fp mem aw exponent r a n mu expLen =
        some selected := by
  have hscanFuel : expLen.toNat - (⟨0⟩ : UInt256).toNat < expLen.toNat + 1 := by
    simp
  rcases selectBarrettLeadingScan_exists (mem := mem)
    (aw := exponentArrayLengthAw aw exponent) (exponent := exponent) (expLen := expLen)
    (startByte := ⟨0⟩) hscanFuel with ⟨scan, hscan⟩
  unfold selectCompleteBarrettLoopSetup selectBarrettLoopSetup
  simp only [hscan]
  by_cases hexhausted : scan.isExhausted = true
  · rw [if_pos hexhausted]
    exact ⟨_, rfl⟩
  · have hnotExhausted : scan.isExhausted = false := by
      cases h : scan.isExhausted <;> simp_all
    rw [if_neg hexhausted]
    let aw0 := readWords1 scan.activeWords ⟨64⟩
    let aw1 := exponentArrayLengthAw aw0 exponent
    let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
    let byte := barrettExponentByteValue scan.memory aw1 exponent scan.startByte
    have htopFuel : (⟨7⟩ : UInt256).toNat < 8 := by decide
    rcases selectBarrettTopBit_exists (byte := byte) htopFuel with ⟨top, htop⟩
    have topValid := selectBarrettTopBit_valid htop
    have htopLe : top.topBit.toNat ≤ 7 := by
      have hle := topValid.topBit_le
      simpa using hle
    have htopPlus : (top.topBit + ⟨1⟩).toNat = top.topBit.toNat + 1 := by
      rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
        Nat.mod_eq_of_lt (by
          have hsize : 8 < UInt256.size := by decide
          omega)]
    have htopBits : (top.topBit + ⟨1⟩).toNat ≤ 8 := by
      rw [htopPlus]
      omega
    have hremaining : expLen.toNat - scan.startByte.toNat ≤ expLen.toNat :=
      Nat.sub_le _ _
    rcases selectBarrettByteLoop_exists (mem := scan.memory) (aw := aw2)
      (byteIdx := scan.startByte) (exponent := exponent) (topBit := top.topBit)
      (expLen := expLen) (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
      hkPos (le_refl kWords) hremaining htopBits (by omega) with ⟨bytes, hbytes⟩
    simp only [aw0, aw1, aw2, byte, htop, hbytes]
    exact ⟨_, rfl⟩

inductive BarrettLoopSetupValid (I : ExecutionEnv) (callFuel kWords fp : Nat)
    (r a n mu exponent expLen : UInt256) (mem : ByteArray) (aw : UInt256) :
    BarrettLoopSetupSelection → Prop where
  | allZero {scan : BarrettLeadingScanSelection}
      (scanValid : BarrettLeadingScanValid exponent expLen mem
        (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
      (exhausted : scan.startByte.eq expLen ≠ ⟨0⟩) :
      BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
        (.allZero scan)
  | nonzero {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
      {bytes : BarrettByteLoopSelection}
      (scanValid : BarrettLeadingScanValid exponent expLen mem
        (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
      (nonexhausted : scan.startByte.eq expLen = ⟨0⟩)
      (indexValid : (scan.startByte.lt (exponentArrayLength scan.memory
        (readWords1 scan.activeWords ⟨64⟩) exponent)).isZero = ⟨0⟩)
      (freePointer : readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
      (topValid : BarrettTopBitValid
        (barrettExponentByteValue scan.memory
          (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
          exponent scan.startByte) ⟨7⟩ top)
      (bytesValid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        scan.memory
        (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
        scan.startByte top.topBit bytes) :
      BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
        (.nonzero scan top bytes)

theorem selectBarrettLoopSetup_valid
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : BarrettLoopSetupSelection}
    (hscanIndex : ∀ (aw' startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      (startByte'.lt (exponentArrayLength mem aw' exponent)).isZero = ⟨0⟩)
    (hscanInc : ∀ (startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hexhausted : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = true → scan.startByte.eq expLen ≠ ⟨0⟩)
    (hnonexhausted : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false → scan.startByte.eq expLen = ⟨0⟩)
    (htopIndex : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false →
      (scan.startByte.lt (exponentArrayLength scan.memory
        (readWords1 scan.activeWords ⟨64⟩) exponent)).isZero = ⟨0⟩)
    (hfree : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false →
      readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
    (hbytes : ∀ (scan : BarrettLeadingScanSelection) (top : BarrettTopBitSelection)
      (bytes : BarrettByteLoopSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false →
      BarrettTopBitValid
        (barrettExponentByteValue scan.memory
          (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
          exponent scan.startByte) ⟨7⟩ top →
      selectBarrettByteLoop byteFuel bitFuel callFuel scan.memory
        (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
        kWords fp scan.startByte exponent top.topBit expLen r a n mu = some bytes →
      BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen scan.memory
        (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
        scan.startByte top.topBit bytes)
    (hselect : selectBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel kWords fp
      mem aw exponent r a n mu expLen = some selected) :
    BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected := by
  unfold selectBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem (exponentArrayLengthAw aw exponent)
      exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have scanValid := selectBarrettLeadingScan_valid hscanIndex hscanInc hscan
      simp only [hscan] at hselect
      by_cases he : scan.isExhausted = true
      · simp [he] at hselect
        subst selected
        exact .allZero scanValid (hexhausted scan scanValid he)
      · have hne : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw1 := exponentArrayLengthAw aw0 exponent
        let byte := barrettExponentByteValue scan.memory aw1 exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel byte ⟨7⟩ with
        | none => simp [aw0, aw1, byte, htop] at hselect
        | some top =>
            have topValid := selectBarrettTopBit_valid htop
            cases hloop : selectBarrettByteLoop byteFuel bitFuel callFuel scan.memory
                (exponentByteLoadAw aw0 exponent scan.startByte) kWords fp scan.startByte
                exponent top.topBit expLen r a n mu with
            | none => simp [aw0, aw1, byte, htop, hloop] at hselect
            | some bytes =>
                simp [aw0, aw1, byte, htop, hloop] at hselect
                subst selected
                exact .nonzero scanValid (hnonexhausted scan scanValid hne)
                  (htopIndex scan scanValid hne) (hfree scan scanValid hne) topValid
                  (hbytes scan top bytes scanValid hne topValid (by simpa [aw0] using hloop))

/-- Construct setup validity and the final persistent arithmetic invariant directly from the
exposed selector. The remaining providers describe only the leading scan and checked Solidity
array geometry; every selected square and multiply is discharged by `BarrettExponentInvariant`. -/
theorem selectBarrettLoopSetup_validInvariant
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : BarrettLoopSetupSelection}
    (invariant : BarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hscanIndex : ∀ (aw' startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      (startByte'.lt (exponentArrayLength mem aw' exponent)).isZero = ⟨0⟩)
    (hscanInc : ∀ (startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ →
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hexhausted : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = true → scan.startByte.eq expLen ≠ ⟨0⟩)
    (hnonexhausted : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false → scan.startByte.eq expLen = ⟨0⟩)
    (htopIndex : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false →
      (scan.startByte.lt (exponentArrayLength scan.memory
        (readWords1 scan.activeWords ⟨64⟩) exponent)).isZero = ⟨0⟩)
    (hfree : ∀ (scan : BarrettLeadingScanSelection),
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan →
      scan.isExhausted = false →
      readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt expLen ≠ ⟨0⟩ →
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel kWords fp
      mem aw exponent r a n mu expLen = some selected) :
    ∃ finalValue,
      BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected ∧
      BarrettExponentInvariant I selected.memory selected.activeWords kWords fp r a n mu
        finalValue baseValue nValue := by
  unfold selectBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem (exponentArrayLengthAw aw exponent)
      exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have scanValid := selectBarrettLeadingScan_valid hscanIndex hscanInc hscan
      have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
      have scanInvariant := scanValid.preserveInvariant scanStartInvariant hexponentFit
        (fun idx hguard =>
          (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
      simp only [hscan] at hselect
      by_cases he : scan.isExhausted = true
      · simp [he] at hselect
        subst selected
        exact ⟨rValue, .allZero scanValid (hexhausted scan scanValid he), scanInvariant⟩
      · have hne : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw1 := exponentArrayLengthAw aw0 exponent
        let byte := barrettExponentByteValue scan.memory aw1 exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel byte ⟨7⟩ with
        | none => simp [aw0, aw1, byte, htop] at hselect
        | some top =>
            have topValid := selectBarrettTopBit_valid htop
            have htopBound : top.topBit.toNat ≤ 7 := by
              simpa using topValid.topBit_le
            cases hloop : selectBarrettByteLoop byteFuel bitFuel callFuel scan.memory
                (exponentByteLoadAw aw0 exponent scan.startByte) kWords fp scan.startByte
                exponent top.topBit expLen r a n mu with
            | none => simp [aw0, aw1, byte, htop, hloop] at hselect
            | some bytes =>
                simp [aw0, aw1, byte, htop, hloop] at hselect
                subst selected
                have hguard := scanValid.finalGuardSet hne
                have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
                  (by native_decide)
                rcases haccess scan.memory aw0 scan.startByte hguard with
                  ⟨indexValid, exponentFit, byteFit⟩
                have byteStartInvariant :=
                  freeInvariant.afterExponentByteLoad exponentFit byteFit
                rcases selectBarrettByteLoop_validInvariant byteStartInvariant htopBound
                    haccess hloop with ⟨finalValue, bytesValid, finalInvariant⟩
                exact ⟨finalValue,
                  .nonzero scanValid (hnonexhausted scan scanValid hne)
                    (htopIndex scan scanValid hne) (hfree scan scanValid hne) topValid bytesValid,
                  finalInvariant⟩

theorem BarrettLoopSetupValid.exact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : BarrettLoopSetupSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {returnPc : UInt256}
    (valid : BarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected)
    (hexpLen : expLen = exponentArrayLength mem aw exponent)
    (hdepth : tail.length + 37 ≤ 1016)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3154⟩
      (r :: a :: exponent :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc (r :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas aw exponent) := by
  have rd3162 := barrettSetupToScanExact (by
    simp only [List.length_cons]
    omega) h
  rw [← hexpLen] at rd3162
  cases valid with
  | allZero scanValid exhausted =>
      have rd3190 := scanValid.exact (by
        simp only [List.length_cons]
        omega) rd3162
      have rdReturn := barrettAllZeroReturn (by omega) exhausted hreturn rd3190
      simpa [BarrettLoopSetupSelection.memory, BarrettLoopSetupSelection.activeWords,
        BarrettLoopSetupSelection.steps, BarrettLoopSetupSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn
  | nonzero scanValid nonexhausted indexValid freePointer topValid bytesValid =>
      have rd3190 := scanValid.exact (by
        simp only [List.length_cons]
        omega) rd3162
      have rd3266 := barrettExitToTopBitGuardExact (by
        simp only [List.length_cons]
        omega) nonexhausted indexValid rd3190
      rw [freePointer] at rd3266
      have rd3304 := topValid.exact (by
        simp only [List.length_cons]
        omega) rd3266
      have rdReturn := validBarrettByteLoopReturnExact bytesValid hdepth hreturn rd3304
      simpa [BarrettLoopSetupSelection.memory, BarrettLoopSetupSelection.activeWords,
        BarrettLoopSetupSelection.steps, BarrettLoopSetupSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

/-! ## Fresh first-call setup selector -/

/-- Canonical arbitrary-exponent setup selection.  A nonzero exponent separates the first byte,
whose first square materializes scratch, from the ordinary reused-scratch byte loop. -/
inductive FreshBarrettLoopSetupSelection where
  | allZero (scan : BarrettLeadingScanSelection)
  | nonzero (scan : BarrettLeadingScanSelection) (top : BarrettTopBitSelection)
      (first : FreshBarrettByteSelection) (rest : BarrettByteLoopSelection)

namespace FreshBarrettLoopSetupSelection

def memory : FreshBarrettLoopSetupSelection -> ByteArray
  | .allZero scan => scan.memory
  | .nonzero _ _ _ rest => rest.memory

def activeWords : FreshBarrettLoopSetupSelection -> UInt256
  | .allZero scan => scan.activeWords
  | .nonzero _ _ _ rest => rest.activeWords

def steps : FreshBarrettLoopSetupSelection -> Nat
  | .allZero scan => 8 + scan.steps + 18
  | .nonzero scan top first rest =>
      8 + scan.steps + 45 + top.steps + first.steps + rest.steps + 17

def gas (initialAw exponent : UInt256) : FreshBarrettLoopSetupSelection -> Nat
  | .allZero scan => barrettSetupGas initialAw exponent + scan.gas + 55
  | .nonzero scan top first rest =>
      barrettSetupGas initialAw exponent + scan.gas +
        barrettTopByteLoadGas scan.activeWords exponent scan.startByte + top.gas +
        first.gas (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩)
          exponent scan.startByte) exponent scan.startByte + rest.gas + 52

end FreshBarrettLoopSetupSelection

def selectFreshBarrettLoopSetup (scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat)
    (mem : ByteArray) (aw exponent r a n mu expLen : UInt256) :
    Option FreshBarrettLoopSetupSelection :=
  let scanAw := exponentArrayLengthAw aw exponent
  match selectBarrettLeadingScan scanFuel mem scanAw exponent expLen ⟨0⟩ with
  | none => none
  | some scan =>
      if scan.isExhausted then some (.allZero scan) else
      let aw0 := readWords1 scan.activeWords ⟨64⟩
      let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
      let byte := barrettExponentByteValue scan.memory
        (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
      match selectBarrettTopBit topFuel byte ⟨7⟩ with
      | none => none
      | some top =>
          match selectFreshBarrettByte bitFuel callFuel scan.memory aw2 kWords fp
              scan.startByte exponent top.topBit r a n mu with
          | none => none
          | some first =>
              match selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
                  first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩
                  expLen r a n mu with
              | none => none
              | some rest => some (.nonzero scan top first rest)

/-- Exposed selector with concrete input-derived fuel. -/
def selectCompleteFreshBarrettLoopSetup (kWords fp : Nat)
    (mem : ByteArray) (aw exponent r a n mu expLen : UInt256) :
    Option FreshBarrettLoopSetupSelection :=
  selectFreshBarrettLoopSetup (expLen.toNat + 1) 8 expLen.toNat 8 kWords kWords fp
    mem aw exponent r a n mu expLen

theorem selectCompleteFreshBarrettLoopSetup_exists
    {kWords fp : Nat} {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    (hkPos : 0 < kWords) :
    exists selected, selectCompleteFreshBarrettLoopSetup kWords fp mem aw exponent
      r a n mu expLen = some selected := by
  have hscanFuel : expLen.toNat - (⟨0⟩ : UInt256).toNat < expLen.toNat + 1 := by simp
  rcases selectBarrettLeadingScan_exists (mem := mem)
    (aw := exponentArrayLengthAw aw exponent) (exponent := exponent) (expLen := expLen)
    (startByte := ⟨0⟩) hscanFuel with ⟨scan, hscan⟩
  unfold selectCompleteFreshBarrettLoopSetup selectFreshBarrettLoopSetup
  simp only [hscan]
  by_cases hexhausted : scan.isExhausted = true
  · rw [if_pos hexhausted]
    exact ⟨_, rfl⟩
  · have hfalse : scan.isExhausted = false := by
      cases h : scan.isExhausted <;> simp_all
    rw [if_neg hexhausted]
    let aw0 := readWords1 scan.activeWords ⟨64⟩
    let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
    let byte := barrettExponentByteValue scan.memory
      (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
    rcases selectBarrettTopBit_exists (byte := byte) (by decide : (⟨7⟩ : UInt256).toNat < 8)
      with ⟨top, htop⟩
    have htopBound : top.topBit.toNat <= 7 := by
      simpa using (selectBarrettTopBit_valid htop).topBit_le
    rcases selectFreshBarrettByte_exists (mem := scan.memory) (aw := aw2)
      (byteIdx := scan.startByte) (exponent := exponent) (topBit := top.topBit)
      (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
      hkPos (le_refl kWords) (by omega : top.topBit.toNat <= 8) with ⟨first, hfirst⟩
    rcases selectBarrettByteLoop_exists (byteFuel := expLen.toNat) (bitFuel := 8)
      (callFuel := kWords) (mem := first.memory) (aw := first.activeWords)
      (byteIdx := scan.startByte + ⟨1⟩) (exponent := exponent) (topBit := ⟨7⟩)
      (expLen := expLen) (r := r) (a := a) (n := n) (mu := mu) (fp := fp)
      hkPos (le_refl kWords) (Nat.sub_le _ _) (by native_decide) (by decide) with
      ⟨rest, hrest⟩
    simp only [aw0, aw2, byte, htop, hfirst, hrest]
    exact ⟨_, rfl⟩

inductive FreshBarrettLoopSetupValid (I : ExecutionEnv) (callFuel kWords fp : Nat)
    (r a n mu exponent expLen : UInt256) (mem : ByteArray) (aw : UInt256) :
    FreshBarrettLoopSetupSelection -> Prop where
  | allZero {scan : BarrettLeadingScanSelection}
      (scanValid : BarrettLeadingScanValid exponent expLen mem
        (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
      (exhausted : scan.startByte.eq expLen ≠ ⟨0⟩) :
      FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
        (.allZero scan)
  | nonzero {scan : BarrettLeadingScanSelection} {top : BarrettTopBitSelection}
      {first : FreshBarrettByteSelection} {rest : BarrettByteLoopSelection}
      (scanValid : BarrettLeadingScanValid exponent expLen mem
        (exponentArrayLengthAw aw exponent) ⟨0⟩ scan)
      (nonexhausted : scan.startByte.eq expLen = ⟨0⟩)
      (indexValid : (scan.startByte.lt (exponentArrayLength scan.memory
        (readWords1 scan.activeWords ⟨64⟩) exponent)).isZero = ⟨0⟩)
      (freePointer : readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
      (topValid : BarrettTopBitValid
        (barrettExponentByteValue scan.memory
          (exponentArrayLengthAw (readWords1 scan.activeWords ⟨64⟩) exponent)
          exponent scan.startByte) ⟨7⟩ top)
      (firstValid : FreshBarrettByteValid I callFuel kWords fp r a n mu scan.memory
        (exponentByteLoadAw (readWords1 scan.activeWords ⟨64⟩) exponent scan.startByte)
        scan.startByte exponent top.topBit expLen first)
      (restValid : BarrettByteLoopValid I callFuel kWords fp r a n mu exponent expLen
        first.memory first.activeWords (scan.startByte + ⟨1⟩) ⟨7⟩ rest) :
      FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw
        (.nonzero scan top first rest)

/-- The read-only leading scan preserves compact pre-scratch state. -/
theorem BarrettLeadingScanValid.preserveInitialInvariant
    {I : ExecutionEnv} {kWords fp rValue baseValue nValue : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw startByte : UInt256}
    {selected : BarrettLeadingScanSelection}
    (valid : BarrettLeadingScanValid exponent expLen mem aw startByte selected)
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hbyteFit : forall idx, idx.lt expLen ≠ ⟨0⟩ ->
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size) :
    InitialBarrettExponentInvariant I selected.memory selected.activeWords kWords fp
      r a n mu rValue baseValue nValue := by
  induction valid with
  | exhausted =>
      simpa [BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords] using invariant
  | @found aw startByte scanWord guardSet indexValid wordEq wordNonzero =>
      have loaded := invariant.afterExponentByteLoad hexponentFit
        (hbyteFit startByte guardSet)
      simpa [BarrettLeadingScanSelection.memory,
        BarrettLeadingScanSelection.activeWords] using loaded
  | @skipZero aw startByte scanWord rest guardSet indexValid wordEq wordZero
      incrementValid restValid ih =>
      have loaded := invariant.afterExponentByteLoad hexponentFit
        (hbyteFit startByte guardSet)
      exact ih loaded

/-- A selected fresh setup is valid and establishes the reused invariant on every nonzero path. -/
theorem selectFreshBarrettLoopSetup_validInvariant
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (hscanIndex : forall (aw' startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ ->
      (startByte'.lt (exponentArrayLength mem aw' exponent)).isZero = ⟨0⟩)
    (hscanInc : forall (startByte' : UInt256), startByte'.lt expLen ≠ ⟨0⟩ ->
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hexhausted : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = true -> scan.startByte.eq expLen ≠ ⟨0⟩)
    (hnonexhausted : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = false -> scan.startByte.eq expLen = ⟨0⟩)
    (htopIndex : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = false ->
      (scan.startByte.lt (exponentArrayLength scan.memory
        (readWords1 scan.activeWords ⟨64⟩) exponent)).isZero = ⟨0⟩)
    (hfree : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = false ->
      readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
    (haccess : forall mem' aw' idx, idx.lt expLen ≠ ⟨0⟩ ->
      (idx.lt (exponentArrayLength mem' aw' exponent)).isZero = ⟨0⟩ /\
      exponent.toNat + 32 + 31 < UInt256.size /\
      (exponentByteAddress exponent idx).toNat + 32 + 31 < UInt256.size)
    (hselect : selectFreshBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel
      kWords fp mem aw exponent r a n mu expLen = some selected) :
    FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected /\
      (match selected with
      | .allZero _ => True
      | .nonzero _ _ _ _ => exists finalValue,
          BarrettExponentInvariant I selected.memory selected.activeWords kWords fp
            r a n mu finalValue baseValue nValue) := by
  unfold selectFreshBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem (exponentArrayLengthAw aw exponent)
      exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have scanValid := selectBarrettLeadingScan_valid hscanIndex hscanInc hscan
      have scanStartInvariant := invariant.afterExponentArrayLengthLoad hexponentFit
      have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant hexponentFit
        (fun idx hguard => (haccess mem (exponentArrayLengthAw aw exponent) idx hguard).2.2)
      simp only [hscan] at hselect
      by_cases he : scan.isExhausted = true
      · simp [he] at hselect
        subst selected
        exact ⟨.allZero scanValid (hexhausted scan scanValid he), trivial⟩
      · have hne : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
        let byte := barrettExponentByteValue scan.memory
          (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel byte ⟨7⟩ with
        | none => simp [aw0, aw2, byte, htop] at hselect
        | some top =>
            have topValid := selectBarrettTopBit_valid htop
            have htopBound : top.topBit.toNat <= 7 := by simpa using topValid.topBit_le
            have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
              intro hz
              have hzNat := congrArg UInt256.toNat hz
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  omega)] at hzNat
              simp at hzNat
            have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  omega)]
              omega
            cases hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory aw2
                kWords fp scan.startByte exponent top.topBit r a n mu with
            | none => simp [aw0, aw2, byte, htop, hfirst] at hselect
            | some first =>
                cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
                    first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩
                    expLen r a n mu with
                | none => simp [aw0, aw2, byte, htop, hfirst, hrest] at hselect
                | some rest =>
                    simp [aw0, aw2, byte, htop, hfirst, hrest] at hselect
                    subst selected
                    have hguard := scanValid.finalGuardSet hne
                    have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
                      (by native_decide)
                    rcases haccess scan.memory aw0 scan.startByte hguard with
                      ⟨indexValid, exponentFit, byteFit⟩
                    have topLoadInvariant :=
                      freeInvariant.afterExponentByteLoad exponentFit byteFit
                    rcases haccess scan.memory aw2 scan.startByte hguard with
                      ⟨firstIndexValid, firstExponentFit, firstByteFit⟩
                    rcases selectFreshBarrettByte_validInvariant topLoadInvariant hguard
                        firstIndexValid htopGuard hcounter firstExponentFit firstByteFit
                        (by simpa only [aw2] using hfirst) with
                      ⟨firstValue, firstValid, firstInvariant⟩
                    rcases selectBarrettByteLoop_validInvariant firstInvariant (by decide)
                        haccess hrest with ⟨finalValue, restValid, finalInvariant⟩
                    exact ⟨.nonzero scanValid (hnonexhausted scan scanValid hne)
                      (htopIndex scan scanValid hne) (hfree scan scanValid hne)
                      topValid firstValid restValid, ⟨finalValue, finalInvariant⟩⟩

/-- Fresh setup validity from one concrete exponent access frame.  The leading scan and every
recursive byte are tied to their actual selected active-word counters. -/
theorem selectFreshBarrettLoopSetup_validInvariantFramed
    {I : ExecutionEnv} {scanFuel topFuel byteFuel bitFuel callFuel kWords fp : Nat}
    {rValue baseValue nValue : Nat}
    {mem : ByteArray} {aw exponent r a n mu expLen : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (invariant : InitialBarrettExponentInvariant I mem aw kWords fp r a n mu
      rValue baseValue nValue)
    (access : BarrettExponentAccessFrame mem exponent expLen r)
    (hscanInc : forall startByte', startByte'.lt expLen ≠ ⟨0⟩ ->
      startByte' ≠ UInt256.lnot ⟨0⟩)
    (hexhausted : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = true -> scan.startByte.eq expLen ≠ ⟨0⟩)
    (hnonexhausted : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = false -> scan.startByte.eq expLen = ⟨0⟩)
    (hfree : forall scan,
      BarrettLeadingScanValid exponent expLen mem (exponentArrayLengthAw aw exponent) ⟨0⟩ scan ->
      scan.isExhausted = false ->
      readWord scan.memory scan.activeWords ⟨64⟩ = UInt256.ofNat fp)
    (hselect : selectFreshBarrettLoopSetup scanFuel topFuel byteFuel bitFuel callFuel
      kWords fp mem aw exponent r a n mu expLen = some selected) :
    FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen mem aw selected /\
      (match selected with
      | .allZero _ => True
      | .nonzero _ _ _ _ => exists finalValue,
          BarrettExponentInvariant I selected.memory selected.activeWords kWords fp
            r a n mu finalValue baseValue nValue) := by
  unfold selectFreshBarrettLoopSetup at hselect
  cases hscan : selectBarrettLeadingScan scanFuel mem (exponentArrayLengthAw aw exponent)
      exponent expLen ⟨0⟩ with
  | none => simp [hscan] at hselect
  | some scan =>
      have scanStartInvariant := invariant.afterExponentArrayLengthLoad access.exponentFit
      rcases selectBarrettLeadingScan_validInvariantFramed scanStartInvariant access hscanInc
          hscan with ⟨scanValid, scanInvariant⟩
      have scanAccess : BarrettExponentAccessFrame scan.memory exponent expLen r := by
        simpa only [scanValid.memoryEq] using access
      simp only [hscan] at hselect
      by_cases he : scan.isExhausted = true
      · simp [he] at hselect
        subst selected
        exact ⟨.allZero scanValid (hexhausted scan scanValid he), trivial⟩
      · have hne : scan.isExhausted = false := by
          cases h : scan.isExhausted <;> simp_all
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hselect
        let aw0 := readWords1 scan.activeWords ⟨64⟩
        let aw2 := exponentByteLoadAw aw0 exponent scan.startByte
        let byte := barrettExponentByteValue scan.memory
          (exponentArrayLengthAw aw0 exponent) exponent scan.startByte
        cases htop : selectBarrettTopBit topFuel byte ⟨7⟩ with
        | none => simp [aw0, aw2, byte, htop] at hselect
        | some top =>
            have topValid := selectBarrettTopBit_valid htop
            have htopBound : top.topBit.toNat <= 7 := by
              simpa using topValid.topBit_le
            have hcounter : top.topBit + ⟨1⟩ ≠ ⟨0⟩ := by
              intro hz
              have hzNat := congrArg UInt256.toNat hz
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  omega)] at hzNat
              simp at hzNat
            have htopGuard : top.topBit.gt (top.topBit + ⟨1⟩) = ⟨0⟩ := by
              apply ugt_zero
              rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
                Nat.mod_eq_of_lt (by
                  have hs : 8 < UInt256.size := by decide
                  omega)]
              omega
            cases hfirst : selectFreshBarrettByte bitFuel callFuel scan.memory aw2
                kWords fp scan.startByte exponent top.topBit r a n mu with
            | none => simp [aw0, aw2, byte, htop, hfirst] at hselect
            | some first =>
                cases hrest : selectBarrettByteLoop byteFuel bitFuel callFuel first.memory
                    first.activeWords kWords fp (scan.startByte + ⟨1⟩) exponent ⟨7⟩
                    expLen r a n mu with
                | none => simp [aw0, aw2, byte, htop, hfirst, hrest] at hselect
                | some rest =>
                    simp [aw0, aw2, byte, htop, hfirst, hrest] at hselect
                    subst selected
                    have hguard := scanValid.finalGuardSet hne
                    have freeInvariant := scanInvariant.afterReadWords1 (ptr := ⟨64⟩)
                      (by native_decide)
                    have hlength0 : exponentArrayLength scan.memory aw0 exponent = expLen :=
                      exponentArrayLength_eq_of_header freeInvariant.covered
                        freeInvariant.activeWordsFit scanAccess.headerConcrete scanAccess.header
                    have indexValid :
                        (scan.startByte.lt (exponentArrayLength scan.memory aw0 exponent)).isZero =
                          ⟨0⟩ := by
                      rw [hlength0]
                      exact isZero_eq_zero_of_ne hguard
                    have topLoadInvariant := freeInvariant.afterExponentByteLoad
                      scanAccess.exponentFit (scanAccess.byteFit scan.startByte hguard)
                    have hlength2 : exponentArrayLength scan.memory aw2 exponent = expLen :=
                      exponentArrayLength_eq_of_header topLoadInvariant.covered
                        topLoadInvariant.activeWordsFit scanAccess.headerConcrete scanAccess.header
                    have firstIndexValid :
                        (scan.startByte.lt (exponentArrayLength scan.memory aw2 exponent)).isZero =
                          ⟨0⟩ := by
                      rw [hlength2]
                      exact isZero_eq_zero_of_ne hguard
                    rcases selectFreshBarrettByteAndLoop_validInvariantFramed topLoadInvariant
                        hguard firstIndexValid htopGuard hcounter scanAccess
                        (by simpa only [aw2] using hfirst) hrest with
                      ⟨_, finalValue, firstValid, restValid, finalInvariant, _⟩
                    exact ⟨.nonzero scanValid (hnonexhausted scan scanValid hne)
                      indexValid (hfree scan scanValid hne) topValid firstValid restValid,
                      ⟨finalValue, finalInvariant⟩⟩

theorem FreshBarrettLoopSetupValid.exact
    {cA gh bl σ σ₀ A I} {g : Sat256} {callFuel kWords fp : Nat}
    {r a n mu exponent expLen : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {returnPc : UInt256}
    (valid : FreshBarrettLoopSetupValid I callFuel kWords fp r a n mu exponent expLen
      mem aw selected)
    (hexpLen : expLen = exponentArrayLength mem aw exponent)
    (hdepth : tail.length + 37 <= 1016)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3154⟩
      (r :: a :: exponent :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc (r :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas aw exponent) := by
  have rd3162 := barrettSetupToScanExact (by
    simp only [List.length_cons]
    omega) h
  rw [← hexpLen] at rd3162
  cases valid with
  | allZero scanValid exhausted =>
      have rd3190 := scanValid.exact (by simp only [List.length_cons]; omega) rd3162
      have rdReturn := barrettAllZeroReturn (by omega) exhausted hreturn rd3190
      simpa [FreshBarrettLoopSetupSelection.memory,
        FreshBarrettLoopSetupSelection.activeWords, FreshBarrettLoopSetupSelection.steps,
        FreshBarrettLoopSetupSelection.gas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using rdReturn
  | nonzero scanValid nonexhausted indexValid freePointer topValid firstValid restValid =>
      have rd3190 := scanValid.exact (by simp only [List.length_cons]; omega) rd3162
      have rd3266 := barrettExitToTopBitGuardExact (by
        simp only [List.length_cons]
        omega) nonexhausted indexValid rd3190
      rw [freePointer] at rd3266
      have rd3304 := topValid.exact (by simp only [List.length_cons]; omega) rd3266
      have rdNext := validFreshBarrettByteExact firstValid (by
        simp only [List.length_cons]
        omega) rd3304
      have rdReturn := validBarrettByteLoopReturnExact restValid hdepth hreturn rdNext
      simpa [FreshBarrettLoopSetupSelection.memory,
        FreshBarrettLoopSetupSelection.activeWords, FreshBarrettLoopSetupSelection.steps,
        FreshBarrettLoopSetupSelection.gas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using rdReturn

end Modexp.MultiLimbBarrettExponentSetup
