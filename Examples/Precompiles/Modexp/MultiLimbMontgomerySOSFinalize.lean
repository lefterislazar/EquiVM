import Examples.Precompiles.Modexp.MultiLimbMontgomeryCompareLoop

/-! # Exact selected SOS final comparison -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSFinalize

open Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Shared exact postcondition for every terminal SOS comparison path. -/
@[irreducible] def SOSComparePost
    (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (tOff nOff tP bytes doSub resultPtr nP : UInt256) (tail : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : Nat) : Prop :=
  RDx runtimeBytecode ee g s0 ⟨7347⟩
    (tOff :: nOff :: tP :: bytes :: doSub :: resultPtr :: nP :: bytes :: tail)
    mem aw rdata acc k C

/-- A greater high limb selects subtraction in the SOS finalizer. -/
theorem sosCompareGreaterToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk resultPtr nP bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hgreater : (compareNWord mem aw tOff nOff).toNat <
      (compareTWord mem aw tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem aw rdata acc k C) :
    SOSComparePost ee g s0 tP (comparePrev nOff) tP bytes ⟨1⟩ resultPtr nP tail
      mem (compareAw aw tOff nOff) rdata acc (k + 45)
      (C + (compareLoadGasAfter 0 aw tOff nOff + 97)) := by
  have rd7459 := GeneratedTraces.trace_7429_body
    (tail := ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7485 := rd7459.jumpiT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated,
        ugt_one hgreater]
      native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd7465 := GeneratedTraces.trace_7478_body
    (by simp only [List.length_cons]; omega) rd7485
  have rd7466 := rd7465.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated]
      exact ult_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7435 := GeneratedTraces.trace_7459_body
    (by omega) rd7466
  have hguard : (tP.gt tP).isZero ≠ ⟨0⟩ := by
    rw [ugt_zero (by omega)]
    native_decide
  have rd7354 := rd7435.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated] at rd7354
  have normalized := rd7354.withIndices
    (k' := k + 45) (C' := C + (compareLoadGasAfter 0 aw tOff nOff + 97))
    (by ring) (by simp [compareLoadGasAfter]; ring)
  simpa [SOSComparePost, comparePrev] using normalized

/-- A smaller high limb suppresses subtraction in the SOS finalizer. -/
theorem sosCompareLessToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk resultPtr nP bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hless : (compareTWord mem aw tOff).toNat <
      (compareNWord mem aw tOff nOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem aw rdata acc k C) :
    SOSComparePost ee g s0 tP (comparePrev nOff) tP bytes ⟨0⟩ resultPtr nP tail
      mem (compareAw aw tOff nOff) rdata acc (k + 47)
      (C + (compareLoadGasAfter 0 aw tOff nOff + 101)) := by
  have rd7459 := GeneratedTraces.trace_7429_body
    (tail := ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7460 := rd7459.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7465 := GeneratedTraces.trace_7453_body
    (by simp only [List.length_cons]; omega) rd7460
  have rd7475 := rd7465.jumpiT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, ult_one hless]
      native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd7435 := GeneratedTraces.trace_7468_body
    (by omega) rd7475
  have hguard : (tP.gt tP).isZero ≠ ⟨0⟩ := by
    rw [ugt_zero (by omega)]
    native_decide
  have rd7354 := rd7435.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated] at rd7354
  have normalized := rd7354.withIndices
    (k' := k + 47) (C' := C + (compareLoadGasAfter 0 aw tOff nOff + 101))
    (by ring) (by simp [compareLoadGasAfter]; ring)
  simpa [SOSComparePost, comparePrev] using normalized

/-- Equal limbs advance both descending pointers and execute the next SOS compare guard. -/
theorem sosCompareEqualContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk resultPtr nP bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : compareTWord mem aw tOff = compareNWord mem aw tOff nOff)
    (hcontinue : tP.toNat < (comparePrev tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7429⟩
      (comparePrev tOff :: comparePrev nOff :: tP :: bytes ::
        ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem (compareAw aw tOff nOff) rdata acc (k + 39)
      (C + (compareLoadGasAfter 0 aw tOff nOff + 77)) := by
  have rd7459 := GeneratedTraces.trace_7429_body
    (tail := ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7460 := rd7459.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7465 := GeneratedTraces.trace_7453_body
    (by simp only [List.length_cons]; omega) rd7460
  have rd7466 := rd7465.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ult_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7435 := GeneratedTraces.trace_7459_body
    (by omega) rd7466
  have hguard : (((⟨31⟩ : UInt256).lnot + tOff).gt tP).isZero = ⟨0⟩ := by
    rw [comparePrev_generated, ugt_one hcontinue]
    native_decide
  have rd7436 := rd7435.jumpiNT (by native_decide) hguard
    (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated,
    comparePrev_generated] at rd7436
  have normalized := rd7436.withIndices
    (k' := k + 39) (C' := C + (compareLoadGasAfter 0 aw tOff nOff + 77))
    (by ring) (by simp [compareLoadGasAfter]; ring)
  exact normalized

/-- Equal final limbs retain the default subtraction decision. -/
theorem sosCompareEqualExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk resultPtr nP bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : compareTWord mem aw tOff = compareNWord mem aw tOff nOff)
    (hexit : (comparePrev tOff).toNat ≤ tP.toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨7429⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem aw rdata acc k C) :
    SOSComparePost ee g s0 (comparePrev tOff) (comparePrev nOff) tP bytes
      ⟨1⟩ resultPtr nP tail mem (compareAw aw tOff nOff) rdata acc (k + 39)
      (C + (compareLoadGasAfter 0 aw tOff nOff + 77)) := by
  have rd7459 := GeneratedTraces.trace_7429_body
    (tail := ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7460 := rd7459.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7465 := GeneratedTraces.trace_7453_body
    (by simp only [List.length_cons]; omega) rd7460
  have rd7466 := rd7465.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ult_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd7435 := GeneratedTraces.trace_7459_body
    (by omega) rd7466
  have hguard : (((⟨31⟩ : UInt256).lnot + tOff).gt tP).isZero ≠ ⟨0⟩ := by
    rw [comparePrev_generated, ugt_zero hexit]
    native_decide
  have rd7354 := rd7435.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated,
    comparePrev_generated] at rd7354
  have normalized := rd7354.withIndices
    (k' := k + 39) (C' := C + (compareLoadGasAfter 0 aw tOff nOff + 77))
    (by ring) (by simp [compareLoadGasAfter]; ring)
  simpa only [SOSComparePost] using normalized

end Modexp.MultiLimbMontgomerySOSFinalize
