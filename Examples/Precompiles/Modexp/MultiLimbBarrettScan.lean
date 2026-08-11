import Examples.Precompiles.Modexp.GeneratedTraces

/-!
# Generated Barrett leading-zero scan

The even-modulus backend strips leading zero bytes before selecting its effective limb width.  This
file composes the generated traces at PCs 1603 and 1618 into exact arbitrary-length scan rules.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettScan

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def scanStack (ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ptr :: exponentPtr :: modulusPtr :: modulusLen :: ret :: resultPtr :: end_ :: tail

def scanReadValue (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  if ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))

def scanActiveWords (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def scanContinue (mem : ByteArray) (aw ptr end_ : UInt256) : UInt256 :=
  UInt256.land (UInt256.lt ptr end_)
    (UInt256.isZero (UInt256.byteAt ⟨0⟩ (scanReadValue mem aw ptr)))

def scanInitialGas (aw ptr : UInt256) : Nat :=
  43 + (Cₘ (scanActiveWords aw ptr) - Cₘ aw)

def scanStepGas (aw ptr : UInt256) : Nat :=
  let ptr' := ⟨1⟩ + ptr
  60 + (Cₘ (scanActiveWords aw ptr') - Cₘ aw)

theorem scanInitialContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (hcontinue : UInt256.isZero (scanContinue mem aw ptr end_) = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨1603⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1618⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem (scanActiveWords aw ptr) rdata acc (k + 13) (C + scanInitialGas aw ptr) := by
  have rd := GeneratedTraces.trace_1603_notTaken
    (tail := tail) hdepth h (by native_decide) hcontinue
  simpa [scanStack, scanContinue, scanReadValue, scanActiveWords, scanInitialGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

theorem scanInitialExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (hexit : UInt256.isZero (scanContinue mem aw ptr end_) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨1603⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1625⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem (scanActiveWords aw ptr) rdata acc (k + 13) (C + scanInitialGas aw ptr) := by
  have rd := GeneratedTraces.trace_1603_taken
    (tail := tail) hdepth h (by native_decide) hexit (by native_decide)
  simpa [scanStack, scanContinue, scanReadValue, scanActiveWords, scanInitialGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

theorem scanStepContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (hcontinue :
      UInt256.isZero (scanContinue mem aw (⟨1⟩ + ptr) end_) = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨1618⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1618⟩
      (scanStack (⟨1⟩ + ptr) exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem (scanActiveWords aw (⟨1⟩ + ptr)) rdata acc
      (k + 17) (C + scanStepGas aw ptr) := by
  have rd := GeneratedTraces.trace_1618_notTaken
    (tail := tail) hdepth h (by native_decide) hcontinue
  simpa [scanStack, scanContinue, scanReadValue, scanActiveWords, scanStepGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

theorem scanStepExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (hexit : UInt256.isZero (scanContinue mem aw (⟨1⟩ + ptr) end_) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨1618⟩
      (scanStack ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1625⟩
      (scanStack (⟨1⟩ + ptr) exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem (scanActiveWords aw (⟨1⟩ + ptr)) rdata acc
      (k + 17) (C + scanStepGas aw ptr) := by
  have rd := GeneratedTraces.trace_1618_taken
    (tail := tail) hdepth h (by native_decide) hexit (by native_decide)
  simpa [scanStack, scanContinue, scanReadValue, scanActiveWords, scanStepGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

structure ScanState where
  ptr : UInt256
  activeWords : UInt256

def scanAdvance (s : ScanState) : ScanState where
  ptr := ⟨1⟩ + s.ptr
  activeWords := scanActiveWords s.activeWords (⟨1⟩ + s.ptr)

def scanIterate : Nat → ScanState → ScanState
  | 0, s => s
  | n + 1, s => scanIterate n (scanAdvance s)

def scanIterationsGas : Nat → ScanState → Nat
  | 0, _ => 0
  | n + 1, s => scanStepGas s.activeWords s.ptr + scanIterationsGas n (scanAdvance s)

@[simp] theorem scanIterate_advance (n : Nat) (s : ScanState) :
    scanIterate n (scanAdvance s) = scanIterate (n + 1) s := by
  rfl

/-- Execute any positive number of byte advances from PC 1618 and exit exactly at the requested
stop byte.  The caller supplies the genuine zero-prefix and stop predicates, while memory growth
and gas remain computed by the bytecode state. -/
theorem scanIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {exponentPtr modulusPtr modulusLen ret resultPtr end_ : UInt256}
    (state : ScanState)
    (hdepth : tail.length + 7 ≤ 1021)
    (hn : 0 < n)
    (hcontinue : ∀ j, j + 1 < n →
      UInt256.isZero
        (scanContinue mem (scanIterate j state).activeWords
          (scanAdvance (scanIterate j state)).ptr end_) = ⟨0⟩)
    (hfinished : UInt256.isZero
      (scanContinue mem (scanIterate (n - 1) state).activeWords
        (scanAdvance (scanIterate (n - 1) state)).ptr end_) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨1618⟩
      (scanStack state.ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1625⟩
      (scanStack (scanIterate n state).ptr exponentPtr modulusPtr modulusLen ret resultPtr end_ tail)
      mem (scanIterate n state).activeWords rdata acc
      (k + 17 * n) (C + scanIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have rd := scanStepExit hdepth (by simpa [scanIterate] using hfinished) h
      simpa [scanIterate, scanAdvance, scanIterationsGas, scanStepGas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd
    | succ n =>
      have rdNext := scanStepContinue hdepth (hcontinue 0 (by omega)) h
      have hcontinue' : ∀ j, j + 1 < n + 1 →
          UInt256.isZero
            (scanContinue mem
              (scanIterate j (scanAdvance state)).activeWords
              (scanAdvance (scanIterate j (scanAdvance state))).ptr end_) = ⟨0⟩ := by
        intro j hj
        simpa [scanIterate_advance] using hcontinue (j + 1) (by omega)
      have hfinished' : UInt256.isZero
          (scanContinue mem
            (scanIterate (n + 1 - 1) (scanAdvance state)).activeWords
            (scanAdvance (scanIterate (n + 1 - 1) (scanAdvance state))).ptr end_) ≠ ⟨0⟩ := by
        simpa [scanIterate_advance, Nat.add_assoc] using hfinished
      have rdRest := ih (state := scanAdvance state) (by omega)
        hcontinue' hfinished' rdNext
      have normalized := rdRest.withIndices (k' := k + 17 * (n + 2)) (by omega) rfl
      simpa [scanIterate, scanAdvance, scanIterationsGas, scanStepGas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

end Modexp.MultiLimbBarrettScan
