import Examples.Precompiles.Modexp.MultiLimbMontgomeryFinalize

/-! # Generated descending-limb comparison trace -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryCompareTrace

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def comparePrev (ptr : UInt256) : UInt256 :=
  ptr + UInt256.lnot ⟨31⟩

def compareTWord (mem : ByteArray) (aw tOff : UInt256) : UInt256 :=
  readWord mem aw (comparePrev tOff)

def compareAw1 (aw tOff : UInt256) : UInt256 :=
  readWords1 aw (comparePrev tOff)

def compareNWord (mem : ByteArray) (aw tOff nOff : UInt256) : UInt256 :=
  readWord mem (compareAw1 aw tOff) (comparePrev nOff)

def compareAw (aw tOff nOff : UInt256) : UInt256 :=
  readWords1 (compareAw1 aw tOff) (comparePrev nOff)

def compareLoadGasAfter (C : Nat) (aw tOff nOff : UInt256) : Nat :=
  59 + C + (Cₘ (compareAw1 aw tOff) - Cₘ aw) +
    (Cₘ (compareAw aw tOff nOff) - Cₘ (compareAw1 aw tOff))

theorem comparePrev_generated (ptr : UInt256) :
    (⟨31⟩ : UInt256).lnot + ptr = comparePrev ptr := by
  unfold comparePrev
  exact (u256_add_comm ptr (⟨31⟩ : UInt256).lnot).symm

theorem compareTWord_generated (mem : ByteArray) (aw tOff : UInt256) :
    compareTWord mem aw tOff =
      if ((⟨31⟩ : UInt256).lnot + tOff).toNat ≥ mem.size ∨
          (⟨31⟩ : UInt256).lnot + tOff ≥ aw * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding ((⟨31⟩ : UInt256).lnot + tOff).toNat 32)) := by
  unfold compareTWord comparePrev readWord
  rw [u256_add_comm tOff (⟨31⟩ : UInt256).lnot]

theorem compareAw1_generated (aw tOff : UInt256) :
    compareAw1 aw tOff =
      UInt256.ofNat
        (MachineState.M aw.toNat ((⟨31⟩ : UInt256).lnot + tOff).toNat 32) := by
  unfold compareAw1 comparePrev readWords1
  rw [u256_add_comm tOff (⟨31⟩ : UInt256).lnot]

theorem compareNWord_generated (mem : ByteArray) (aw tOff nOff : UInt256) :
    compareNWord mem aw tOff nOff =
      if (nOff + (⟨31⟩ : UInt256).lnot).toNat ≥ mem.size ∨
          nOff + (⟨31⟩ : UInt256).lnot ≥
            UInt256.ofNat
              (MachineState.M aw.toNat
                ((⟨31⟩ : UInt256).lnot + tOff).toNat 32) * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding (nOff + (⟨31⟩ : UInt256).lnot).toNat 32)) := by
  unfold compareNWord comparePrev readWord
  rw [compareAw1_generated]

theorem compareAw_generated (aw tOff nOff : UInt256) :
    compareAw aw tOff nOff =
      UInt256.ofNat
        (MachineState.M
          (UInt256.ofNat
            (MachineState.M aw.toNat
              ((⟨31⟩ : UInt256).lnot + tOff).toNat 32)).toNat
          (nOff + (⟨31⟩ : UInt256).lnot).toNat 32) := by
  unfold compareAw comparePrev readWords1
  rw [compareAw1_generated]

/-- A strictly greater current limb terminates the descending comparison with `doSub = 1`. -/
theorem compareGreaterToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk r0 r1 bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hgreater : (compareNWord mem aw tOff nOff).toNat <
      (compareTWord mem aw tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tP :: comparePrev nOff :: tP :: bytes :: ⟨1⟩ ::
        r0 :: r1 :: bytes :: tail)
      mem (compareAw aw tOff nOff) rdata acc (k + 45)
      (compareLoadGasAfter C aw tOff nOff + 97) := by
  have rd4278 := GeneratedTraces.trace_4255_body
    (tail := ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have hgtWord :
      (compareTWord mem aw tOff).gt (compareNWord mem aw tOff nOff) ≠ ⟨0⟩ := by
    rw [ugt_one hgreater]
    native_decide
  have hgtRaw :
      (if ((⟨31⟩ : UInt256).lnot + tOff).toNat ≥ mem.size ∨
            (⟨31⟩ : UInt256).lnot + tOff ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding ((⟨31⟩ : UInt256).lnot + tOff).toNat 32))).gt
        (if (nOff + (⟨31⟩ : UInt256).lnot).toNat ≥ mem.size ∨
              nOff + (⟨31⟩ : UInt256).lnot ≥
                UInt256.ofNat (MachineState.M aw.toNat
                  ((⟨31⟩ : UInt256).lnot + tOff).toNat 32) * ⟨32⟩ then
            ⟨0⟩
          else UInt256.ofNat (fromByteArrayBigEndian
            (mem.readWithPadding (nOff + (⟨31⟩ : UInt256).lnot).toNat 32))) ≠ ⟨0⟩ := by
    rw [← compareTWord_generated, ← compareNWord_generated]
    exact hgtWord
  have rd4304 := rd4278.jumpiT (by native_decide) hgtRaw
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd4284 := GeneratedTraces.trace_4304_body
    (by simp only [List.length_cons]; omega) rd4304
  have hltWord :
      (compareTWord mem aw tOff).lt (compareNWord mem aw tOff nOff) = ⟨0⟩ :=
    ult_zero (by omega)
  have hltRaw :
      (if ((⟨31⟩ : UInt256).lnot + tOff).toNat ≥ mem.size ∨
            (⟨31⟩ : UInt256).lnot + tOff ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding ((⟨31⟩ : UInt256).lnot + tOff).toNat 32))).lt
        (if (nOff + (⟨31⟩ : UInt256).lnot).toNat ≥ mem.size ∨
              nOff + (⟨31⟩ : UInt256).lnot ≥
                UInt256.ofNat (MachineState.M aw.toNat
                  ((⟨31⟩ : UInt256).lnot + tOff).toNat 32) * ⟨32⟩ then
            ⟨0⟩
          else UInt256.ofNat (fromByteArrayBigEndian
            (mem.readWithPadding (nOff + (⟨31⟩ : UInt256).lnot).toNat 32))) = ⟨0⟩ := by
    rw [← compareTWord_generated, ← compareNWord_generated]
    exact hltWord
  have rd4285 := rd4284.jumpiNT (by native_decide) hltRaw
    (by simp only [List.length_cons]; omega)
  have rd4254 := GeneratedTraces.trace_4285_body (by omega) rd4285
  have htPZero : tP.gt tP = ⟨0⟩ := ugt_zero (by omega)
  have hguard : (tP.gt tP).isZero ≠ ⟨0⟩ := by
    rw [htPZero]
    native_decide
  have rd4165 := rd4254.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated] at rd4165
  have normalized := rd4165.withIndices
    (k' := k + 45) (C' := compareLoadGasAfter C aw tOff nOff + 97)
    (by ring) (by simp [compareLoadGasAfter]; ring)
  simpa [comparePrev] using normalized

/-- A strictly smaller current limb terminates the descending comparison with `doSub = 0`. -/
theorem compareLessToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk r0 r1 bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hless : (compareTWord mem aw tOff).toNat <
      (compareNWord mem aw tOff nOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tP :: comparePrev nOff :: tP :: bytes :: ⟨0⟩ ::
        r0 :: r1 :: bytes :: tail)
      mem (compareAw aw tOff nOff) rdata acc (k + 47)
      (compareLoadGasAfter C aw tOff nOff + 101) := by
  have rd4278 := GeneratedTraces.trace_4255_body
    (tail := ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd4279 := rd4278.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd4284 := GeneratedTraces.trace_4279_body
    (by simp only [List.length_cons]; omega) rd4279
  have rd4294 := rd4284.jumpiT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, ult_one hless]
      native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd4254 := GeneratedTraces.trace_4294_body (by omega) rd4294
  have htPZero : tP.gt tP = ⟨0⟩ := ugt_zero (by omega)
  have hguard : (tP.gt tP).isZero ≠ ⟨0⟩ := by
    rw [htPZero]
    native_decide
  have rd4165 := rd4254.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated] at rd4165
  have normalized := rd4165.withIndices
    (k' := k + 47) (C' := compareLoadGasAfter C aw tOff nOff + 101)
    (by ring) (by simp [compareLoadGasAfter]; ring)
  simpa [comparePrev] using normalized

/-- Equal current limbs advance both descending pointers and execute the next loop guard. -/
theorem compareEqualContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk r0 r1 bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : compareTWord mem aw tOff = compareNWord mem aw tOff nOff)
    (hcontinue : tP.toNat < (comparePrev tOff).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4255⟩
      (comparePrev tOff :: comparePrev nOff :: tP :: bytes ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareAw aw tOff nOff) rdata acc (k + 39)
      (compareLoadGasAfter C aw tOff nOff + 77) := by
  have rd4278 := GeneratedTraces.trace_4255_body
    (tail := ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd4279 := rd4278.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd4284 := GeneratedTraces.trace_4279_body
    (by simp only [List.length_cons]; omega) rd4279
  have rd4285 := rd4284.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ult_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd4254 := GeneratedTraces.trace_4285_body (by omega) rd4285
  have hgt : (comparePrev tOff).gt tP = ⟨1⟩ := ugt_one hcontinue
  have hguard : (((⟨31⟩ : UInt256).lnot + tOff).gt tP).isZero = ⟨0⟩ := by
    rw [comparePrev_generated, hgt]
    native_decide
  have rd4255 := rd4254.jumpiNT (by native_decide) hguard
    (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated,
    comparePrev_generated] at rd4255
  have normalized := rd4255.withIndices
    (k' := k + 39) (C' := compareLoadGasAfter C aw tOff nOff + 77)
    (by ring) (by simp [compareLoadGasAfter]; ring)
  exact normalized

/-- Equal limbs at the final descending position leave the default `doSub = 1`, covering exact
equality of the complete vectors. -/
theorem compareEqualExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff tP junk r0 r1 bytes : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hequal : compareTWord mem aw tOff = compareNWord mem aw tOff nOff)
    (hexit : (comparePrev tOff).toNat ≤ tP.toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (comparePrev tOff :: comparePrev nOff :: tP :: bytes ::
        ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
      mem (compareAw aw tOff nOff) rdata acc (k + 39)
      (compareLoadGasAfter C aw tOff nOff + 77) := by
  have rd4278 := GeneratedTraces.trace_4255_body
    (tail := ⟨1⟩ :: r0 :: r1 :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd4279 := rd4278.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ugt_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd4284 := GeneratedTraces.trace_4279_body
    (by simp only [List.length_cons]; omega) rd4279
  have rd4285 := rd4284.jumpiNT (by native_decide) (by
      rw [← compareTWord_generated, ← compareNWord_generated, hequal]
      exact ult_zero (by omega))
    (by simp only [List.length_cons]; omega)
  have rd4254 := GeneratedTraces.trace_4285_body (by omega) rd4285
  have hgt : (comparePrev tOff).gt tP = ⟨0⟩ := ugt_zero hexit
  have hguard : (((⟨31⟩ : UInt256).lnot + tOff).gt tP).isZero ≠ ⟨0⟩ := by
    rw [comparePrev_generated, hgt]
    native_decide
  have rd4165 := rd4254.jumpiT (by native_decide) hguard
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← compareAw_generated, ← compareAw1_generated,
    comparePrev_generated] at rd4165
  have normalized := rd4165.withIndices
    (k' := k + 39) (C' := compareLoadGasAfter C aw tOff nOff + 77)
    (by ring) (by simp [compareLoadGasAfter]; ring)
  exact normalized

end Modexp.MultiLimbMontgomeryCompareTrace
