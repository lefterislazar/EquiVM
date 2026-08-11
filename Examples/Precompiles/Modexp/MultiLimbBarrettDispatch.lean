import Examples.Precompiles.Modexp.BarrettWordCaller
import Examples.Precompiles.Modexp.GeneratedTraces

/-!
# Direct multi-limb Barrett dispatch

The generic leading-zero scanner in `BarrettWordCaller` reaches PC 1646 for both word-sized and
multi-limb moduli.  This file adds the missing multi-limb successor: for an untrimmed modulus
longer than 32 bytes, the deployed code computes `k = (m + 31) / 32`, rejects `k = 1`, and reaches
the Barrett limb-conversion body at PC 1675.

This split is needed because the existing caller proof followed only the one-word successor at
PC 1665.  Keeping the dispatch as a separate exact theorem lets the generated PC-local traces
determine the concrete stack, step count, and gas without folding the much larger Barrett body
into the scanner proof.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettDispatch

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The byte tested by the direct Barrett scan is the trusted one-byte padded source read. -/
theorem scanByteAt_toNat_eq_model
    {mem : ByteArray} {aw : UInt256} {cur : Nat}
    (hcur256 : cur < UInt256.size) (hcur64 : cur < 2 ^ 64)
    (haw : ¬ UInt256.ofNat cur ≥ aw * ⟨32⟩) :
    (barrettScanByteAt mem aw cur).toNat =
      Model.bytesToNatPadded mem cur 1 := by
  have hload : wideLoadWord mem aw (UInt256.ofNat cur) =
      uInt256OfByteArray (mem.readBytes cur 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    rw [UInt256.toNat_ofNat_of_lt hcur256,
      readWithPadding_eq_model_readPadded mem cur 32 hcur64 (by decide),
      readBytes_eq_model_readPadded mem cur 32 hcur64 (by decide)]
  unfold barrettScanByteAt
  rw [hload]
  exact calldataByte0_toNat_eq_model mem cur hcur64

/-- The scan's nonzero first byte gives the radix lower bound for the selected modulus width. -/
theorem modulusLower_of_firstByte
    (mem : ByteArray) (aw : UInt256) (p modulusSize : Nat)
    (hmodulusPos : 0 < modulusSize)
    (hp256 : p + 32 < UInt256.size) (hp64 : p + 32 < 2 ^ 64)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩) :
    256 ^ (modulusSize - 1) ≤
      Model.bytesToNatPadded mem (p + 32) modulusSize := by
  have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hfrontier : ¬ UInt256.ofNat (p + 32) ≥ aw * ⟨32⟩ := by
    intro hge
    have hgeNat : (aw * ⟨32⟩).toNat ≤ (UInt256.ofNat (p + 32)).toNat := hge
    rw [hawMul, UInt256.toNat_ofNat_of_lt hp256] at hgeNat
    omega
  have hbyte := scanByteAt_toNat_eq_model
    (mem := mem) (aw := aw) (cur := p + 32) hp256 hp64 hfrontier
  have hbytePos : 0 < (barrettScanByteAt mem aw (p + 32)).toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hfirst
    apply u256_inj
    simpa [barrettScanByteAt] using hz
  apply model_bytesToNatPadded_lower_of_first mem (p + 32) modulusSize hmodulusPos
  rwa [← hbyte]

def limbCount (m : Nat) : Nat := (m + 31) / 32

/-- The same scan fact reaches the top-limb radix weight of the selected limb count. -/
theorem modulusLimbLower_of_firstByte
    (mem : ByteArray) (aw : UInt256) (p modulusSize : Nat)
    (hmodulusLarge : 32 < modulusSize)
    (hp256 : p + 32 < UInt256.size) (hp64 : p + 32 < 2 ^ 64)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩) :
    UInt256.size ^ (limbCount modulusSize - 1) ≤
      Model.bytesToNatPadded mem (p + 32) modulusSize := by
  have hlower := modulusLower_of_firstByte mem aw p modulusSize (by omega)
    hp256 hp64 hactive hawFit hfirst
  have hexponent : 32 * (limbCount modulusSize - 1) ≤ modulusSize - 1 := by
    unfold limbCount
    omega
  have hpow : 256 ^ (32 * (limbCount modulusSize - 1)) ≤
      256 ^ (modulusSize - 1) := Nat.pow_le_pow_right (by omega) hexponent
  calc
    UInt256.size ^ (limbCount modulusSize - 1) =
        256 ^ (32 * (limbCount modulusSize - 1)) := by
          rw [show UInt256.size = 256 ^ 32 by native_decide, pow_mul]
    _ ≤ 256 ^ (modulusSize - 1) := hpow
    _ ≤ Model.bytesToNatPadded mem (p + 32) modulusSize := hlower

/-- The direct scanner outcome for a modulus longer than one word enters the multi-limb Barrett
body with the exact deployed limb count. -/
theorem directToBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {p m retBar result exp base ret : Nat}
    (hmLarge : 32 < m) (hm : m ≤ 1024)
    (htail : tail.length ≤ 1006)
    (h : RDx runtimeBytecode ee g s0 ⟨1646⟩
      (⟨0⟩ :: ⟨32⟩ :: UInt256.ofNat exp :: UInt256.ofNat p ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1675⟩
      (UInt256.ofNat p :: UInt256.ofNat exp :: UInt256.ofNat (limbCount m) ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc (steps + 30) (gasUsed + 111) := by
  have hmWord : m < UInt256.size := lt_of_le_of_lt hm (by native_decide)
  have hsumBound : m + 31 < UInt256.size := by
    apply lt_of_le_of_lt (show m + 31 ≤ 1055 by omega) (by native_decide)
  have hsum : UInt256.ofNat m + (⟨31⟩ : UInt256) =
      UInt256.ofNat (m + 31) := by
    simpa using ofNat_add_bounded hsumBound
  have hgt : UInt256.gt (UInt256.ofNat m)
      (UInt256.ofNat m + ⟨31⟩) = ⟨0⟩ := by
    rw [hsum]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hmWord,
      UInt256.toNat_ofNat_of_lt hsumBound]
    omega
  have rd1322 := GeneratedTraces.trace_1646_notTaken
    (tail := UInt256.ofNat retBar :: UInt256.ofNat result ::
      UInt256.ofNat base :: UInt256.ofNat ret :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hgt
  have rd1659 := GeneratedTraces.trace_1322_jump
    (by simp only [List.length_cons]; omega) rd1322 (by native_decide) (by native_decide)
  have rd1665 := GeneratedTraces.trace_1659_jump
    (by simp only [List.length_cons]; omega) rd1659 (by native_decide) (by native_decide)
  have hkWord : limbCount m < UInt256.size := by
    apply lt_of_le_of_lt (show limbCount m ≤ 32 by
      unfold limbCount
      omega) (by native_decide)
  have hshift : UInt256.shiftRight (UInt256.ofNat (m + 31)) ⟨5⟩ =
      UInt256.ofNat (limbCount m) := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt hsumBound]
    rw [show (⟨5⟩ : UInt256).toNat = 5 by decide]
    rw [UInt256.toNat_ofNat_of_lt hkWord]
    simp [limbCount]
  rw [hsum, hshift] at rd1665
  have hkLarge : 1 < limbCount m := by
    unfold limbCount
    omega
  have hneq : UInt256.eq (UInt256.ofNat (limbCount m)) ⟨1⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro hone
    have heq := uInt256_eq_one_eq hone
    have hnat := congrArg UInt256.toNat heq
    rw [UInt256.toNat_ofNat_of_lt hkWord,
      show (⟨1⟩ : UInt256).toNat = 1 by decide] at hnat
    omega
  have rd1675 := GeneratedTraces.trace_1665_notTaken
    (by simp only [List.length_cons]; omega) rd1665 (by native_decide) hneq
  simpa [limbCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1675

/-- Compose the generic direct scan exit with `directToBody`.  The selector premise is the
deployed condition: the first payload byte is nonzero (the `m = 1` alternative is impossible for
a multi-limb modulus).  From PC 1592 the complete scan-and-dispatch prefix costs exactly 239 gas. -/
theorem scanDirectToBody
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p m retBar result exp base ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {steps gasUsed : Nat}
    (hmLarge : 32 < m) (hm : m ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hpend : p + m + 31 < UInt256.size)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩)
    (htail : tail.length ≤ 1006)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    ∃ steps', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1675⟩
      (UInt256.ofNat p :: UInt256.ofNat exp :: UInt256.ofNat (limbCount m) ::
        UInt256.ofNat m :: UInt256.ofNat retBar :: UInt256.ofNat result ::
        UInt256.ofNat base :: UInt256.ofNat ret :: tail)
      mem aw rdata acc steps' (gasUsed + 239) := by
  obtain ⟨steps1646, rd1646⟩ := Modexp.reachBarrettScanDirect
    (p := p) (m := m) (retBar := retBar) (result := result)
    (exp := exp) (base := base) (ret := ret)
    hp32 hpend hactive (Or.inr hfirst) htail h
  refine ⟨steps1646 + 30, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    directToBody hmLarge hm htail rd1646

/-- The first multi-limb Barrett block sets up its modulus `bytesToLimbs` call.  This is the exact
stack observed independently with `symcheck run --pc 1675 --target-pc 2836`. -/
theorem bodyToFirstConversionCall
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {p m retBar result exp base ret words : UInt256}
    (hdepth : tail.length + 8 ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨1675⟩
      (p :: exp :: words :: m :: retBar :: result :: base :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨2836⟩
      (p :: words :: ⟨1700⟩ :: words :: ⟨1707⟩ :: base :: exp :: words ::
        ⟨1745⟩ :: result :: m :: ⟨805⟩ :: retBar :: result :: ret :: tail)
      mem aw rdata acc (steps + 15) (gasUsed + 50) := by
  have rd := evm_run h with [
    swap2,
    pushCanonical 2 .PUSH2 ⟨1745⟩ (by decide),
    swap2,
    dup7,
    swap8,
    pushCanonical 2 .PUSH2 ⟨1707⟩ (by decide),
    dup4,
    pushCanonical 2 .PUSH2 ⟨1700⟩ (by decide),
    dup2,
    pushCanonical 2 .PUSH2 ⟨805⟩ (by decide),
    swap11,
    swap12Canonical,
    swap9,
    pushCanonical 2 .PUSH2 ⟨2836⟩ (by decide),
    jump (by native_decide)]
  exact (rd.withPC (pc' := ⟨2836⟩) (by native_decide)).withIndices (by omega) (by omega)

/-- Generic entry of `bytesToLimbs`: request a `words`-element array from the shared allocator and
return to PC 2847.  Only the first three stack words belong to the helper; the caller continuation
is intentionally arbitrary. -/
theorem conversionToAllocator
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {dataPtr words innerRet : UInt256}
    (hdepth : tail.length + 3 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨2836⟩
      (dataPtr :: words :: innerRet :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (words :: ⟨2847⟩ :: innerRet :: dataPtr :: tail)
      mem aw rdata acc (steps + 7) (gasUsed + 24) := by
  have rd := evm_run h with [
    jumpdest,
    swap2,
    swap1,
    pushCanonical 2 .PUSH2 ⟨2847⟩ (by decide),
    swap1,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)]
  exact (rd.withPC (pc' := ⟨1487⟩) (by native_decide)).withIndices (by omega) (by omega)

end Modexp.MultiLimbBarrettDispatch
