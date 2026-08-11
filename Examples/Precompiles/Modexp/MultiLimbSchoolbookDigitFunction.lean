import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionContract

/-!
# Complete accepted Knuth quotient digit

Starting at the common multiply-subtract cursor, these contracts execute all divisor limbs, the
top subtraction, the optional full add-back computation, and the concrete quotient store.  The
two theorems are selected by the negative flag computed by `topSubtractStep`; neither path assumes
the accepted digit or updated memory as an execution callback.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDigitFunction

open MultiLimbSchoolbookNormalization MultiLimbSchoolbookDivision

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

variable {normalizationMarker : UInt256}

def multiplyInitial (mem : ByteArray) (aw : UInt256) : MultiplySubtractState :=
  ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, mem, aw⟩

def multiplyFinal (mem : ByteArray) (aw v u current qHat : UInt256)
    (kEff : Nat) : MultiplySubtractState :=
  multiplySubtractIterate v u current qHat kEff (multiplyInitial mem aw)

def topResult (mem : ByteArray) (aw v u current qHat : UInt256)
    (kEff : Nat) : TopSubtractResult :=
  let final := multiplyFinal mem aw v u current qHat kEff
  topSubtractStep final.memory final.activeWords u current (UInt256.ofNat kEff)
    final.carry final.borrow

def directMemory (mem : ByteArray) (aw v u current qHat quotient : UInt256)
    (kEff jj : Nat) : ByteArray :=
  MultiLimbSchoolbookSingle.storeQuotient
    (topResult mem aw v u current qHat kEff).memory quotient jj qHat

def directGas (mem : ByteArray) (aw v u current qHat : UInt256) (kEff : Nat) : Nat :=
  let initial := multiplyInitial mem aw
  let final := multiplyFinal mem aw v u current qHat kEff
  multiplySubtractLoopGas v u current qHat kEff initial +
    topSubtractGas final.activeWords u current (UInt256.ofNat kEff) + 131

/-- Complete one accepted digit when top subtraction is nonnegative. -/
theorem directExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff jj quotientCount : Nat} {tail : List UInt256}
    {v u current qHat shift ret rem quotient vTop : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hnonnegative : (topResult mem aw v u current qHat kEff).negative = ⟨0⟩)
    (hjj : jj < quotientCount) (hjjWord : jj < UInt256.size)
    (hquotientCountWord : quotientCount < UInt256.size)
    (hquotHeader : arrayHeader (topResult mem aw v u current qHat kEff).memory
      (topResult mem aw v u current qHat kEff).activeWords quotient =
        UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader
      (topResult mem aw v u current qHat kEff).activeWords quotient =
        (topResult mem aw v u current qHat kEff).activeWords)
    (hquotElementAw : arrayAfterWord
      (topResult mem aw v u current qHat kEff).activeWords quotient jj =
        (topResult mem aw v u current qHat kEff).activeWords)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: current :: qHat :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat jj).isZero :: UInt256.ofNat jj :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      (directMemory mem aw v u current qHat quotient kEff jj)
      (topResult mem aw v u current qHat kEff).activeWords rdata acc
      (k + 78 * kEff + 67) (C + directGas mem aw v u current qHat kEff) := by
  have rd5564 := multiplySubtractAllExact hkEffWord (by omega) h
  have rd5600 := topSubtractExact (by omega) rd5564
  simp only [topResult, multiplyFinal, multiplyInitial] at hnonnegative
  dsimp only at rd5600
  rw [hnonnegative] at rd5600
  have rd5601 := skipAddBackExact (by omega) rd5600
  have rd5457 := storeQuotientAndGuardExact hjj hjjWord hquotientCountWord
    hquotHeader hquotHeaderAw hquotElementAw (by omega) rd5601
  have normalized := rd5457.withIndices
    (k' := k + 78 * kEff + 67) (C' := C + directGas mem aw v u current qHat kEff)
    (by omega) (by simp [directGas, topResult, multiplyFinal, multiplyInitial]; omega)
  simpa only [directMemory, topResult, multiplyFinal, multiplyInitial] using normalized

def addBackInitial (mem : ByteArray) (aw : UInt256) : AddBackState :=
  ⟨⟨0⟩, ⟨0⟩, mem, aw⟩

def addBackFinal (mem : ByteArray) (aw v u current qHat : UInt256)
    (kEff : Nat) : AddBackState :=
  let top := topResult mem aw v u current qHat kEff
  addBackIterate v u current kEff (addBackInitial top.memory top.activeWords)

def correctionTop (mem : ByteArray) (aw v u current qHat : UInt256)
    (kEff : Nat) : TopAddResult :=
  let top := topResult mem aw v u current qHat kEff
  let final := addBackFinal mem aw v u current qHat kEff
  topAddStep final.memory final.activeWords top.address final.carry

def correctedQHat (qHat : UInt256) : UInt256 := qHat + (⟨0⟩ : UInt256).lnot

def correctedMemory (mem : ByteArray) (aw v u current qHat quotient : UInt256)
    (kEff jj : Nat) : ByteArray :=
  MultiLimbSchoolbookSingle.storeQuotient
    (correctionTop mem aw v u current qHat kEff).memory quotient jj (correctedQHat qHat)

def correctedGas (mem : ByteArray) (aw v u current qHat : UInt256)
    (kEff : Nat) : Nat :=
  let initial := multiplyInitial mem aw
  let multiplied := multiplyFinal mem aw v u current qHat kEff
  let top := topResult mem aw v u current qHat kEff
  let addInitial := addBackInitial top.memory top.activeWords
  let added := addBackFinal mem aw v u current qHat kEff
  multiplySubtractLoopGas v u current qHat kEff initial +
    topSubtractGas multiplied.activeWords u current (UInt256.ofNat kEff) +
    addBackLoopGas v u current kEff addInitial +
    topAddGas added.activeWords top.address + 234

/-- Complete one accepted digit when top subtraction requires Knuth add-back correction. -/
theorem correctedExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff jj quotientCount : Nat} {tail : List UInt256}
    {v u current qHat shift ret rem quotient vTop : UInt256}
    (hkEffWord : kEff < UInt256.size)
    (hnegative : (topResult mem aw v u current qHat kEff).negative ≠ ⟨0⟩)
    (hqHat : qHat ≠ ⟨0⟩)
    (hjj : jj < quotientCount) (hjjWord : jj < UInt256.size)
    (hquotientCountWord : quotientCount < UInt256.size)
    (hquotHeader : arrayHeader (correctionTop mem aw v u current qHat kEff).memory
      (correctionTop mem aw v u current qHat kEff).activeWords quotient =
        UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader
      (correctionTop mem aw v u current qHat kEff).activeWords quotient =
        (correctionTop mem aw v u current qHat kEff).activeWords)
    (hquotElementAw : arrayAfterWord
      (correctionTop mem aw v u current qHat kEff).activeWords quotient jj =
        (correctionTop mem aw v u current qHat kEff).activeWords)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: current :: qHat :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat jj).isZero :: UInt256.ofNat jj :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      (correctedMemory mem aw v u current qHat quotient kEff jj)
      (correctionTop mem aw v u current qHat kEff).activeWords rdata acc
      (k + 134 * kEff + 109) (C + correctedGas mem aw v u current qHat kEff) := by
  have rd5564 := multiplySubtractAllExact hkEffWord (by omega) h
  have rd5600 := topSubtractExact (by omega) rd5564
  have rd5644 := enterAddBackExact hnegative hqHat (by omega) rd5600
  have rd5645 := addBackAllExact hkEffWord (by omega) rd5644
  have rd5601 := topAddExact (by omega) rd5645
  have rd5457 := storeQuotientAndGuardExact hjj hjjWord hquotientCountWord
    hquotHeader hquotHeaderAw hquotElementAw (by omega) rd5601
  have normalized := rd5457.withIndices
    (k' := k + 134 * kEff + 109)
    (C' := C + correctedGas mem aw v u current qHat kEff)
    (by omega)
    (by
      simp [correctedGas, topResult, multiplyFinal, multiplyInitial, addBackFinal,
        addBackInitial, correctionTop]
      omega)
  simpa only [correctedMemory, correctedQHat, correctionTop, addBackFinal,
    addBackInitial, topResult, multiplyFinal, multiplyInitial] using normalized

end Modexp.MultiLimbSchoolbookDigitFunction
