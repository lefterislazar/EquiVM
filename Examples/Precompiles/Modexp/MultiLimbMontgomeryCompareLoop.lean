import Examples.Precompiles.Modexp.MultiLimbMontgomeryCompareTrace

/-! # Arbitrary-length generated Montgomery comparison loop -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure CompareState where
  tOff : UInt256
  nOff : UInt256
  activeWords : UInt256

def compareAdvance (state : CompareState) : CompareState where
  tOff := comparePrev state.tOff
  nOff := comparePrev state.nOff
  activeWords := compareAw state.activeWords state.tOff state.nOff

def compareIterate : Nat → CompareState → CompareState
  | 0, state => state
  | n + 1, state => compareAdvance (compareIterate n state)

def compareLoadGas (state : CompareState) : Nat :=
  compareLoadGasAfter 0 state.activeWords state.tOff state.nOff

def compareIterationsGas : Nat → CompareState → Nat
  | 0, _ => 0
  | n + 1, state =>
      compareIterationsGas n state + compareLoadGas (compareIterate n state) + 77

def compareLoopJunk (n : Nat) (initial bytes : UInt256) : UInt256 :=
  if n = 0 then initial else bytes

/-- Execute any number of equal high-limb iterations, retaining exact active-memory growth and
gas before the first differing or final limb. -/
theorem compareEqualIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {tP junk r0 r1 bytes : UInt256}
    (state : CompareState)
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : ∀ j, j < n →
      compareTWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff =
        compareNWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff (compareIterate j state).nOff)
    (hcontinue : ∀ j, j < n →
      tP.toNat < (comparePrev (compareIterate j state).tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (state.tOff :: state.nOff :: tP :: junk ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4255⟩
      ((compareIterate n state).tOff :: (compareIterate n state).nOff ::
        tP :: compareLoopJunk n junk bytes ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareIterate n state).activeWords rdata acc
      (k + 39 * n) (C + compareIterationsGas n state) := by
  induction n generalizing k C with
  | zero =>
      simpa [compareIterate, compareIterationsGas, compareLoopJunk]
  | succ n ih =>
      have hequalPrefix : ∀ j, j < n →
          compareTWord mem (compareIterate j state).activeWords
              (compareIterate j state).tOff =
            compareNWord mem (compareIterate j state).activeWords
              (compareIterate j state).tOff (compareIterate j state).nOff := by
        intro j hj
        exact hequal j (by omega)
      have hcontinuePrefix : ∀ j, j < n →
          tP.toNat < (comparePrev (compareIterate j state).tOff).toNat := by
        intro j hj
        exact hcontinue j (by omega)
      have rdPrefix := ih hequalPrefix hcontinuePrefix h
      have rdNext := compareEqualContinue hdepth (hequal n (by omega))
        (hcontinue n (by omega)) rdPrefix
      have normalized := rdNext.withIndices
        (k' := k + 39 * (n + 1))
        (C' := C + compareIterationsGas (n + 1) state)
        (by ring) (by
          simp only [compareIterationsGas, compareLoadGas, compareLoadGasAfter]
          ring)
      simpa [compareIterate, compareAdvance, compareLoopJunk,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

def compareGreaterAfterGas (n : Nat) (state : CompareState) : Nat :=
  compareIterationsGas n state + compareLoadGas (compareIterate n state) + 97

def compareLessAfterGas (n : Nat) (state : CompareState) : Nat :=
  compareIterationsGas n state + compareLoadGas (compareIterate n state) + 101

/-- After any equal prefix, the first greater limb selects subtraction. -/
theorem compareEqualThenGreater
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {tP junk r0 r1 bytes : UInt256}
    (state : CompareState)
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : ∀ j, j < n →
      compareTWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff =
        compareNWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff (compareIterate j state).nOff)
    (hcontinue : ∀ j, j < n →
      tP.toNat < (comparePrev (compareIterate j state).tOff).toNat)
    (hgreater :
      (compareNWord mem (compareIterate n state).activeWords
          (compareIterate n state).tOff (compareIterate n state).nOff).toNat <
        (compareTWord mem (compareIterate n state).activeWords
          (compareIterate n state).tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (state.tOff :: state.nOff :: tP :: junk ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem state.activeWords rdata acc k C) :
    let final := compareIterate n state
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tP :: comparePrev final.nOff :: tP :: bytes ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareAdvance final).activeWords rdata acc
      (k + 39 * n + 45) (C + compareGreaterAfterGas n state) := by
  have rdPrefix := compareEqualIterations state hdepth hequal hcontinue h
  have rdFinal := compareGreaterToCopy hdepth hgreater rdPrefix
  have normalized := rdFinal.withIndices
    (k' := k + 39 * n + 45) (C' := C + compareGreaterAfterGas n state)
    (by ring) (by
      simp only [compareGreaterAfterGas, compareLoadGas, compareLoadGasAfter]
      ring)
  simpa [compareAdvance] using normalized

/-- After any equal prefix, the first smaller limb suppresses subtraction. -/
theorem compareEqualThenLess
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {tP junk r0 r1 bytes : UInt256}
    (state : CompareState)
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : ∀ j, j < n →
      compareTWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff =
        compareNWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff (compareIterate j state).nOff)
    (hcontinue : ∀ j, j < n →
      tP.toNat < (comparePrev (compareIterate j state).tOff).toNat)
    (hless :
      (compareTWord mem (compareIterate n state).activeWords
          (compareIterate n state).tOff).toNat <
        (compareNWord mem (compareIterate n state).activeWords
          (compareIterate n state).tOff (compareIterate n state).nOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (state.tOff :: state.nOff :: tP :: junk ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem state.activeWords rdata acc k C) :
    let final := compareIterate n state
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tP :: comparePrev final.nOff :: tP :: bytes ::
        ⟨0⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareAdvance final).activeWords rdata acc
      (k + 39 * n + 47) (C + compareLessAfterGas n state) := by
  have rdPrefix := compareEqualIterations state hdepth hequal hcontinue h
  have rdFinal := compareLessToCopy hdepth hless rdPrefix
  have normalized := rdFinal.withIndices
    (k' := k + 39 * n + 47) (C' := C + compareLessAfterGas n state)
    (by ring) (by
      simp only [compareLessAfterGas, compareLoadGas, compareLoadGasAfter]
      ring)
  simpa [compareAdvance] using normalized

/-- If every preceding limb and the final limb are equal, comparison keeps `doSub = 1`. -/
theorem compareAllEqualToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {tP junk r0 r1 bytes : UInt256}
    (state : CompareState)
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : ∀ j, j ≤ n →
      compareTWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff =
        compareNWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff (compareIterate j state).nOff)
    (hcontinue : ∀ j, j < n →
      tP.toNat < (comparePrev (compareIterate j state).tOff).toNat)
    (hexit :
      (comparePrev (compareIterate n state).tOff).toNat ≤ tP.toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (state.tOff :: state.nOff :: tP :: junk ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem state.activeWords rdata acc k C) :
    let final := compareIterate n state
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (comparePrev final.tOff :: comparePrev final.nOff :: tP :: bytes ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareAdvance final).activeWords rdata acc
      (k + 39 * (n + 1))
      (C + compareIterationsGas (n + 1) state) := by
  have hequalPrefix : ∀ j, j < n →
      compareTWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff =
        compareNWord mem (compareIterate j state).activeWords
          (compareIterate j state).tOff (compareIterate j state).nOff := by
    intro j hj
    exact hequal j (by omega)
  have rdPrefix := compareEqualIterations state hdepth hequalPrefix hcontinue h
  have rdFinal := compareEqualExit hdepth (hequal n (by omega)) hexit rdPrefix
  have normalized := rdFinal.withIndices
    (k' := k + 39 * (n + 1))
    (C' := C + compareIterationsGas (n + 1) state)
    (by ring) (by
      simp only [compareIterationsGas, compareLoadGas, compareLoadGasAfter]
      ring)
  simpa [compareIterate, compareAdvance] using normalized

end Modexp.MultiLimbMontgomeryCompareTrace
