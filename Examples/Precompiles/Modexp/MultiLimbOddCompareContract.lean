import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeLinks

/-!
# Exact descending-limb comparison used by the odd backend

This module packages the generated `_limbsLt` segments at PCs 3707--3784.  The source scans
equal-length little-endian arrays from their most significant limb downwards.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbOddCompare

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def previousIndex (index : UInt256) : UInt256 :=
  UInt256.lnot ⟨0⟩ + index

def elementPtr (array index : UInt256) : UInt256 :=
  index.shiftLeft ⟨5⟩ + array + ⟨32⟩

def headerWord (mem : ByteArray) (aw array : UInt256) : UInt256 :=
  readWord mem aw array

def afterHeader (aw array : UInt256) : UInt256 :=
  readWords1 aw array

def elementWord (mem : ByteArray) (aw array index : UInt256) : UInt256 :=
  readWord mem (afterHeader aw array) (elementPtr array index)

def afterElement (aw array index : UInt256) : UInt256 :=
  readWords1 (afterHeader aw array) (elementPtr array index)

theorem previousIndex_generated (index : UInt256) :
    UInt256.lnot ⟨0⟩ + index = previousIndex index := by
  rfl

theorem headerWord_generated (mem : ByteArray) (aw array : UInt256) :
    headerWord mem aw array =
      if array.toNat ≥ mem.size ∨ array ≥ aw * ⟨32⟩ then
        ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding array.toNat 32)) := by
  rfl

theorem afterHeader_generated (aw array : UInt256) :
    afterHeader aw array =
      UInt256.ofNat (MachineState.M aw.toNat array.toNat 32) := by
  rfl

theorem firstElementAddress
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index array : UInt256}
    (hdepth : tail.length + 2 ≤ 1019)
    (hbound : (previousIndex index).toNat < (headerWord mem aw array).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: array :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3720⟩
      (elementPtr array (previousIndex index) :: previousIndex index :: array :: tail)
      mem (afterHeader aw array) rdata acc (k + 25)
      (C + 87 + (Cₘ (afterHeader aw array) - Cₘ aw)) := by
  have rd1538 := GeneratedTraces.trace_3707_body hdepth h
  have hguard :
      ((previousIndex index).lt (headerWord mem aw array)).isZero = ⟨0⟩ := by
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      ((UInt256.lnot ⟨0⟩ + index).lt
        (if array.toNat ≥ mem.size ∨ array ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding array.toNat 32)))).isZero = ⟨0⟩ := by
    rw [previousIndex_generated, ← headerWord_generated]
    exact hguard
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd1548 := GeneratedTraces.trace_1539_body (by
    simp only [List.length_cons]
    omega) rd1539
  have rd3720 := rd1548.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rd3720
  have normalized := rd3720.withIndices
    (k' := k + 25)
    (C' := C + 87 + (Cₘ (afterHeader aw array) - Cₘ aw))
    (by omega) (by omega)
  simpa only [previousIndex, elementPtr] using normalized

def loadedWord (mem : ByteArray) (aw address : UInt256) : UInt256 :=
  headerWord mem aw address

def afterLoad (aw address : UInt256) : UInt256 :=
  afterHeader aw address

def secondHeaderWord (mem : ByteArray) (aw address array : UInt256) : UInt256 :=
  headerWord mem (afterLoad aw address) array

def afterSecondHeader (aw address array : UInt256) : UInt256 :=
  afterHeader (afterLoad aw address) array

def secondElementGas (aw address array : UInt256) : Nat :=
  82 + (Cₘ (afterLoad aw address) - Cₘ aw) +
    (Cₘ (afterSecondHeader aw address array) - Cₘ (afterLoad aw address))

theorem secondElementAddress
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address index first second : UInt256}
    (hdepth : tail.length + 4 ≤ 1019)
    (hbound : index.toNat < (secondHeaderWord mem aw address second).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3720⟩
      (address :: index :: first :: second :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3731⟩
      (elementPtr second index :: loadedWord mem aw address ::
        index :: first :: second :: tail)
      mem (afterSecondHeader aw address second) rdata acc (k + 23)
      (C + secondElementGas aw address second) := by
  have rd1538 := GeneratedTraces.trace_3720_body hdepth h
  have hguard :
      (index.lt (secondHeaderWord mem aw address second)).isZero = ⟨0⟩ := by
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      (index.lt
        (if second.toNat ≥ mem.size ∨
            second ≥ UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding second.toNat 32)))).isZero = ⟨0⟩ := by
    rw [show UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) =
        afterLoad aw address by rfl,
      ← headerWord_generated]
    exact hguard
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd1548 := GeneratedTraces.trace_1539_body (by
    simp only [List.length_cons]
    omega) rd1539
  have rd3731 := rd1548.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hafter :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat (MachineState.M aw.toNat address.toNat 32)).toNat
            second.toNat 32) =
        afterSecondHeader aw address second := by
    rfl
  have hload :
      UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) =
        afterLoad aw address := by
    rfl
  rw [hafter, hload] at rd3731
  have normalized := rd3731.withIndices
    (k' := k + 23)
    (C' := C + secondElementGas aw address second)
    (by omega) (by simp only [secondElementGas]; omega)
  simpa only [elementPtr, loadedWord, readWord]
    using normalized

theorem lessReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address value index first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1024)
    (hlt : value.toNat < (loadedWord mem aw address).toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3731⟩
      (address :: value :: index :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨1⟩ :: tail)
      mem (afterLoad aw address) rdata acc (k + 12)
      (C + 41 + (Cₘ (afterLoad aw address) - Cₘ aw)) := by
  have rd3737 := GeneratedTraces.trace_3731_body
    (by simp only [List.length_cons]; omega) h
  have hcondition : value.lt (loadedWord mem aw address) ≠ ⟨0⟩ := by
    rw [ult_one hlt]
    native_decide
  have hconditionRaw :
      value.lt
        (if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding address.toNat 32))) ≠ ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hcondition
  have rd3777 := rd3737.jumpiT (by native_decide) hconditionRaw
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3784 := GeneratedTraces.trace_3777_body
    (by omega) rd3777
  have rdret := rd3784.jump (by native_decide) hret
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rdret
  have normalized := rdret.withIndices
    (k' := k + 12)
    (C' := C + 41 + (Cₘ (afterLoad aw address) - Cₘ aw))
    (by omega) (by simp only [afterLoad]; omega)
  simpa only [afterLoad] using normalized

theorem notLessToRepeat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address value index first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1024)
    (hnlt : (loadedWord mem aw address).toNat ≤ value.toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3731⟩
      (address :: value :: index :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3738⟩
      (index :: first :: second :: ret :: tail)
      mem (afterLoad aw address) rdata acc (k + 5)
      (C + 20 + (Cₘ (afterLoad aw address) - Cₘ aw)) := by
  have rd3737 := GeneratedTraces.trace_3731_body
    (by simp only [List.length_cons]; omega) h
  have hcondition : value.lt (loadedWord mem aw address) = ⟨0⟩ :=
    ult_zero hnlt
  have hconditionRaw :
      value.lt
        (if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding address.toNat 32))) = ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hcondition
  have rd3738 := rd3737.jumpiNT (by native_decide) hconditionRaw
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rd3738
  have normalized := rd3738.withIndices
    (k' := k + 5)
    (C' := C + 20 + (Cₘ (afterLoad aw address) - Cₘ aw))
    (by omega) (by simp only [afterLoad]; omega)
  simpa only [afterLoad] using normalized

theorem repeatedFirstElementAddress
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index array : UInt256}
    (hdepth : tail.length + 2 ≤ 1019)
    (hbound : index.toNat < (headerWord mem aw array).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3738⟩
      (index :: array :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3747⟩
      (elementPtr array index :: index :: array :: tail)
      mem (afterHeader aw array) rdata acc (k + 21)
      (C + 78 + (Cₘ (afterHeader aw array) - Cₘ aw)) := by
  have rd1538 := GeneratedTraces.trace_3738_body hdepth h
  have hguard : (index.lt (headerWord mem aw array)).isZero = ⟨0⟩ := by
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      (index.lt
        (if array.toNat ≥ mem.size ∨ array ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding array.toNat 32)))).isZero = ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hguard
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd1548 := GeneratedTraces.trace_1539_body
    (by simp only [List.length_cons]; omega) rd1539
  have rd3747 := rd1548.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rd3747
  have normalized := rd3747.withIndices
    (k' := k + 21)
    (C' := C + 78 + (Cₘ (afterHeader aw array) - Cₘ aw))
    (by omega) (by omega)
  simpa only [elementPtr] using normalized

theorem repeatedSecondElementAddress
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address index first second : UInt256}
    (hdepth : tail.length + 4 ≤ 1019)
    (hbound : index.toNat < (secondHeaderWord mem aw address second).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3747⟩
      (address :: index :: first :: second :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3758⟩
      (elementPtr second index :: loadedWord mem aw address ::
        index :: first :: second :: tail)
      mem (afterSecondHeader aw address second) rdata acc (k + 23)
      (C + secondElementGas aw address second) := by
  have rd1538 := GeneratedTraces.trace_3747_body hdepth h
  have hguard :
      (index.lt (secondHeaderWord mem aw address second)).isZero = ⟨0⟩ := by
    rw [ult_one hbound]
    native_decide
  have hguardRaw :
      (index.lt
        (if second.toNat ≥ mem.size ∨
            second ≥ UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding second.toNat 32)))).isZero = ⟨0⟩ := by
    rw [show UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) =
        afterLoad aw address by rfl,
      ← headerWord_generated]
    exact hguard
  have rd1539 := rd1538.jumpiNT (by native_decide) hguardRaw
    (by simp only [List.length_cons]; omega)
  have rd1548 := GeneratedTraces.trace_1539_body
    (by simp only [List.length_cons]; omega) rd1539
  have rd3758 := rd1548.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hafter :
      UInt256.ofNat
          (MachineState.M
            (UInt256.ofNat (MachineState.M aw.toNat address.toNat 32)).toNat
            second.toNat 32) =
        afterSecondHeader aw address second := by
    rfl
  have hload : UInt256.ofNat (MachineState.M aw.toNat address.toNat 32) =
      afterLoad aw address := by
    rfl
  rw [hafter, hload] at rd3758
  have normalized := rd3758.withIndices
    (k' := k + 23) (C' := C + secondElementGas aw address second)
    (by omega) (by simp only [secondElementGas]; omega)
  simpa only [elementPtr, loadedWord, readWord] using normalized

theorem greaterReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address value index first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1024)
    (hgt : (loadedWord mem aw address).toNat < value.toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3758⟩
      (address :: value :: index :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨0⟩ :: tail)
      mem (afterLoad aw address) rdata acc (k + 12)
      (C + 40 + (Cₘ (afterLoad aw address) - Cₘ aw)) := by
  have rd3764 := GeneratedTraces.trace_3758_body
    (by simp only [List.length_cons]; omega) h
  have hcondition : (loadedWord mem aw address).lt value ≠ ⟨0⟩ := by
    rw [ult_one hgt]
    native_decide
  have hconditionRaw :
      (if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding address.toNat 32))).lt value ≠ ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hcondition
  have rd3770 := rd3764.jumpiT (by native_decide) hconditionRaw
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd3776 := GeneratedTraces.trace_3770_body (by omega) rd3770
  have rdret := rd3776.jump (by native_decide) hret
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rdret
  have normalized := rdret.withIndices
    (k' := k + 12)
    (C' := C + 40 + (Cₘ (afterLoad aw address) - Cₘ aw))
    (by omega) (by simp only [afterLoad]; omega)
  simpa only [afterLoad] using normalized

theorem equalContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address value index first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hequal : loadedWord mem aw address = value)
    (hindex : index ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3758⟩
      (address :: value :: index :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail)
      mem (afterLoad aw address) rdata acc (k + 11)
      (C + 48 + (Cₘ (afterLoad aw address) - Cₘ aw)) := by
  have rd3764 := GeneratedTraces.trace_3758_body
    (by simp only [List.length_cons]; omega) h
  have hcondition : (loadedWord mem aw address).lt value = ⟨0⟩ := by
    rw [hequal]
    exact ult_zero (by omega)
  have hconditionRaw :
      (if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding address.toNat 32))).lt value = ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hcondition
  have rd3765 := rd3764.jumpiNT (by native_decide) hconditionRaw
    (by simp only [List.length_cons]; omega)
  have rd3700 := GeneratedTraces.trace_3765_body
    (by simp only [List.length_cons]; omega) rd3765
  have rd3707 := rd3700.jumpiT (by native_decide) hindex
    (by native_decide) (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rd3707
  have normalized := rd3707.withIndices
    (k' := k + 11)
    (C' := C + 48 + (Cₘ (afterLoad aw address) - Cₘ aw))
    (by omega) (by simp only [afterLoad]; omega)
  simpa only [afterLoad] using normalized

theorem equalEnd
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {address value first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1024)
    (hequal : loadedWord mem aw address = value)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3758⟩
      (address :: value :: ⟨0⟩ :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨0⟩ :: tail)
      mem (afterLoad aw address) rdata acc (k + 17)
      (C + 67 + (Cₘ (afterLoad aw address) - Cₘ aw)) := by
  have rd3764 := GeneratedTraces.trace_3758_body
    (by simp only [List.length_cons]; omega) h
  have hcondition : (loadedWord mem aw address).lt value = ⟨0⟩ := by
    rw [hequal]
    exact ult_zero (by omega)
  have hconditionRaw :
      (if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding address.toNat 32))).lt value = ⟨0⟩ := by
    rw [← headerWord_generated]
    exact hcondition
  have rd3765 := rd3764.jumpiNT (by native_decide) hconditionRaw
    (by simp only [List.length_cons]; omega)
  have rd3700 := GeneratedTraces.trace_3765_body
    (by simp only [List.length_cons]; omega) rd3765
  have rd3701 := rd3700.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  have rd3706 := GeneratedTraces.trace_3701_body (by omega) rd3701
  have rdret := rd3706.jump (by native_decide) hret
    (by simp only [List.length_cons]; omega)
  rw [← afterHeader_generated] at rdret
  have normalized := rdret.withIndices
    (k' := k + 17)
    (C' := C + 67 + (Cₘ (afterLoad aw address) - Cₘ aw))
    (by omega) (by simp only [afterLoad]; omega)
  simpa only [afterLoad] using normalized

def scanIndex (index : UInt256) : UInt256 := previousIndex index

def firstAddress (first index : UInt256) : UInt256 :=
  elementPtr first (scanIndex index)

def secondAddress (second index : UInt256) : UInt256 :=
  elementPtr second (scanIndex index)

def firstValue (mem : ByteArray) (aw first index : UInt256) : UInt256 :=
  loadedWord mem aw (firstAddress first index)

def secondValue (mem : ByteArray) (aw second index : UInt256) : UInt256 :=
  loadedWord mem aw (secondAddress second index)

structure IterationCoverage (mem : ByteArray) (aw first second index : UInt256) : Prop where
  firstBound : (scanIndex index).toNat < (headerWord mem aw first).toNat
  secondBound : (scanIndex index).toNat < (headerWord mem aw second).toNat
  firstHeader : afterHeader aw first = aw
  firstElement : afterLoad aw (firstAddress first index) = aw
  secondHeader : afterHeader aw second = aw
  secondElement : afterLoad aw (secondAddress second index) = aw

theorem iterationLess
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index first second ret : UInt256}
    (hdepth : tail.length + 5 ≤ 1019)
    (coverage : IterationCoverage mem aw first second index)
    (hlt : (firstValue mem aw first index).toNat <
      (secondValue mem aw second index).toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨1⟩ :: tail)
      mem aw rdata acc (k + 60) (C + 210) := by
  have rd3720 := firstElementAddress
    (tail := second :: ret :: tail) (by
      simp only [List.length_cons]
      omega) coverage.firstBound h
  rw [coverage.firstHeader] at rd3720
  have hsecondBound :
      (scanIndex index).toNat <
        (secondHeaderWord mem aw (firstAddress first index) second).toNat := by
    simpa only [secondHeaderWord, coverage.firstElement] using coverage.secondBound
  have rd3731 := secondElementAddress
    (tail := ret :: tail) (by simp only [List.length_cons]; omega)
    hsecondBound rd3720
  have hafterSecond :
      afterSecondHeader aw (firstAddress first index) second = aw := by
    simp only [afterSecondHeader, coverage.firstElement, coverage.secondHeader]
  rw [hafterSecond] at rd3731
  have rdret := lessReturn (by omega) hlt hret rd3731
  rw [coverage.secondElement] at rdret
  have normalized := rdret.withIndices
    (k' := k + 60) (C' := C + 210) (by omega) (by
      simp only [secondElementGas, afterSecondHeader,
        coverage.firstElement, coverage.secondHeader]
      omega)
  simpa only [scanIndex, firstAddress, secondAddress, firstValue, secondValue]
    using normalized

theorem iterationNotLessToRepeat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index first second ret : UInt256}
    (hdepth : tail.length + 5 ≤ 1019)
    (coverage : IterationCoverage mem aw first second index)
    (hnlt : (secondValue mem aw second index).toNat ≤
      (firstValue mem aw first index).toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3738⟩
      (scanIndex index :: first :: second :: ret :: tail)
      mem aw rdata acc (k + 53) (C + 189) := by
  have rd3720 := firstElementAddress
    (tail := second :: ret :: tail) (by
      simp only [List.length_cons]
      omega) coverage.firstBound h
  rw [coverage.firstHeader] at rd3720
  have hsecondBound :
      (scanIndex index).toNat <
        (secondHeaderWord mem aw (firstAddress first index) second).toNat := by
    simpa only [secondHeaderWord, coverage.firstElement] using coverage.secondBound
  have rd3731 := secondElementAddress
    (tail := ret :: tail) (by simp only [List.length_cons]; omega)
    hsecondBound rd3720
  have hafterSecond :
      afterSecondHeader aw (firstAddress first index) second = aw := by
    simp only [afterSecondHeader, coverage.firstElement, coverage.secondHeader]
  rw [hafterSecond] at rd3731
  have rd3738 := notLessToRepeat (by omega) hnlt rd3731
  rw [coverage.secondElement] at rd3738
  have normalized := rd3738.withIndices
    (k' := k + 53) (C' := C + 189) (by omega) (by
      simp only [secondElementGas, afterSecondHeader,
        coverage.firstElement, coverage.secondHeader]
      omega)
  simpa only [scanIndex, firstAddress, secondAddress, firstValue, secondValue]
    using normalized

theorem iterationGreater
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index first second ret : UInt256}
    (hdepth : tail.length + 5 ≤ 1019)
    (coverage : IterationCoverage mem aw first second index)
    (hgt : (secondValue mem aw second index).toNat <
      (firstValue mem aw first index).toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨0⟩ :: tail)
      mem aw rdata acc (k + 109) (C + 389) := by
  have rd3738 := iterationNotLessToRepeat hdepth coverage (Nat.le_of_lt hgt) h
  have rd3747 := repeatedFirstElementAddress
    (tail := second :: ret :: tail) (by simp only [List.length_cons]; omega)
    coverage.firstBound rd3738
  rw [coverage.firstHeader] at rd3747
  have hsecondBound :
      (scanIndex index).toNat <
        (secondHeaderWord mem aw (firstAddress first index) second).toNat := by
    simpa only [secondHeaderWord, coverage.firstElement] using coverage.secondBound
  have rd3758 := repeatedSecondElementAddress
    (tail := ret :: tail) (by simp only [List.length_cons]; omega)
    hsecondBound rd3747
  have hafterSecond :
      afterSecondHeader aw (firstAddress first index) second = aw := by
    simp only [afterSecondHeader, coverage.firstElement, coverage.secondHeader]
  rw [hafterSecond] at rd3758
  have rdret := greaterReturn (by omega) hgt hret rd3758
  rw [coverage.secondElement] at rdret
  have normalized := rdret.withIndices
    (k' := k + 109) (C' := C + 389) (by omega) (by
      simp only [secondElementGas, afterSecondHeader,
        coverage.firstElement, coverage.secondHeader]
      omega)
  simpa only [scanIndex, firstAddress, secondAddress, firstValue, secondValue]
    using normalized

theorem iterationEqualContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (coverage : IterationCoverage mem aw first second index)
    (hequal : firstValue mem aw first index = secondValue mem aw second index)
    (hindex : scanIndex index ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3707⟩
      (scanIndex index :: first :: second :: ret :: tail)
      mem aw rdata acc (k + 108) (C + 397) := by
  have hnlt : (secondValue mem aw second index).toNat ≤
      (firstValue mem aw first index).toNat := by
    rw [hequal]
  have rd3738 := iterationNotLessToRepeat (by omega) coverage hnlt h
  have rd3747 := repeatedFirstElementAddress
    (tail := second :: ret :: tail) (by simp only [List.length_cons]; omega)
    coverage.firstBound rd3738
  rw [coverage.firstHeader] at rd3747
  have hsecondBound :
      (scanIndex index).toNat <
        (secondHeaderWord mem aw (firstAddress first index) second).toNat := by
    simpa only [secondHeaderWord, coverage.firstElement] using coverage.secondBound
  have rd3758 := repeatedSecondElementAddress
    (tail := ret :: tail) (by simp only [List.length_cons]; omega)
    hsecondBound rd3747
  have hafterSecond :
      afterSecondHeader aw (firstAddress first index) second = aw := by
    simp only [afterSecondHeader, coverage.firstElement, coverage.secondHeader]
  rw [hafterSecond] at rd3758
  have rd3707 := equalContinue (by omega) hequal.symm hindex rd3758
  rw [coverage.secondElement] at rd3707
  have normalized := rd3707.withIndices
    (k' := k + 108) (C' := C + 397) (by omega) (by
      simp only [secondElementGas, afterSecondHeader,
        coverage.firstElement, coverage.secondHeader]
      omega)
  simpa only [scanIndex, firstAddress, secondAddress, firstValue, secondValue]
    using normalized

theorem iterationEqualEnd
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index first second ret : UInt256}
    (hdepth : tail.length + 5 ≤ 1019)
    (coverage : IterationCoverage mem aw first second index)
    (hequal : firstValue mem aw first index = secondValue mem aw second index)
    (hindex : scanIndex index = ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (index :: first :: second :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (⟨0⟩ :: tail)
      mem aw rdata acc (k + 114) (C + 416) := by
  have hnlt : (secondValue mem aw second index).toNat ≤
      (firstValue mem aw first index).toNat := by
    rw [hequal]
  have rd3738 := iterationNotLessToRepeat hdepth coverage hnlt h
  have rd3747 := repeatedFirstElementAddress
    (tail := second :: ret :: tail) (by simp only [List.length_cons]; omega)
    coverage.firstBound rd3738
  rw [coverage.firstHeader] at rd3747
  have hsecondBound :
      (scanIndex index).toNat <
        (secondHeaderWord mem aw (firstAddress first index) second).toNat := by
    simpa only [secondHeaderWord, coverage.firstElement] using coverage.secondBound
  have rd3758 := repeatedSecondElementAddress
    (tail := ret :: tail) (by simp only [List.length_cons]; omega)
    hsecondBound rd3747
  have hafterSecond :
      afterSecondHeader aw (firstAddress first index) second = aw := by
    simp only [afterSecondHeader, coverage.firstElement, coverage.secondHeader]
  rw [hafterSecond] at rd3758
  rw [hindex] at rd3758
  have hequalEnd :
      loadedWord mem aw (elementPtr second ⟨0⟩) =
        loadedWord mem aw (firstAddress first index) := by
    simpa only [secondValue, secondAddress, hindex] using hequal.symm
  have rdret := equalEnd (tail := tail) (first := first) (second := second)
    (ret := ret) (address := elementPtr second ⟨0⟩)
    (value := loadedWord mem aw (firstAddress first index))
    (by omega) hequalEnd hret rd3758
  have hsecondElementEnd :
      afterLoad aw (elementPtr second ⟨0⟩) = aw := by
    simpa only [secondAddress, hindex] using coverage.secondElement
  rw [hsecondElementEnd] at rdret
  have normalized := rdret.withIndices
    (k' := k + 114) (C' := C + 416) (by omega) (by
      simp only [secondElementGas, afterSecondHeader,
        coverage.firstElement, coverage.secondHeader]
      omega)
  simpa only [scanIndex, firstAddress, secondAddress, firstValue, secondValue]
    using normalized

theorem scanIndex_ofNat_succ (n : Nat) (hfit : n + 1 < UInt256.size) :
    scanIndex (UInt256.ofNat (n + 1)) = UInt256.ofNat n := by
  apply u256_inj
  simp only [scanIndex, previousIndex, uadd_toNat]
  rw [UInt256.toNat_ofNat_of_lt hfit,
    UInt256.toNat_ofNat_of_lt (by omega : n < UInt256.size)]
  have hnot : (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
    native_decide
  rw [hnot]
  have hsum : UInt256.size - 1 + (n + 1) = n + UInt256.size := by
    omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n < UInt256.size)]

/-- A word load wholly inside the current active-memory extent does not expand memory. -/
theorem afterHeader_eq_of_access (aw ptr : UInt256)
    (haccess : ptr.toNat + 32 ≤ 32 * aw.toNat) :
    afterHeader aw ptr = aw := by
  unfold afterHeader readWords1
  rw [machineM_eq_of_access haccess, u256_ofNat_toNat]

/-- The payload address of element `i` has the usual Solidity-array layout when its arithmetic
does not wrap. -/
theorem elementPtr_ofNat_toNat_of_fit (array : UInt256) (i : Nat)
    (hfit : array.toNat + 32 * (i + 1) < UInt256.size) :
    (elementPtr array (UInt256.ofNat i)).toNat =
      array.toNat + 32 * (i + 1) := by
  have hsize : UInt256.size = 32 * 2 ^ 251 := by native_decide
  have hshift :
      (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩).toNat = 32 * i :=
    ushl5_ofNat_toNat i (by rw [hsize] at hfit; omega)
  have hinner : 32 * i + array.toNat < UInt256.size := by omega
  unfold elementPtr
  rw [uadd_toNat, uadd_toNat, hshift,
    Nat.mod_eq_of_lt hinner,
    show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt]
  · omega
  · omega

/-- Backwards-compatible bounded interface used by the 32-limb comparison loop. -/
theorem elementPtr_ofNat_toNat (array : UInt256) (i : Nat)
    (_hi : i ≤ 32)
    (hfit : array.toNat + 32 * (i + 1) < UInt256.size) :
    (elementPtr array (UInt256.ofNat i)).toNat =
      array.toNat + 32 * (i + 1) := by
  exact elementPtr_ofNat_toNat_of_fit array i hfit

/-- Ordinary Solidity-array geometry supplies all per-iteration coverage facts required by the
descending comparison loop. -/
theorem iterationCoverage_of_array_geometry
    (mem : ByteArray) (aw first second : UInt256) (count : Nat)
    (hcount : count ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstHeader : headerWord mem aw first = UInt256.ofNat count)
    (hsecondHeader : headerWord mem aw second = UInt256.ofNat count)
    (hfirstRange : first.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hsecondRange : second.toNat + 32 * (count + 1) ≤ 32 * aw.toNat) :
    ∀ i, i < count →
      IterationCoverage mem aw first second (UInt256.ofNat (i + 1)) := by
  intro i hi
  have hsmall : 32 < UInt256.size := by decide
  have hcountFit : count < UInt256.size := by omega
  have hindexFit : i + 1 < UInt256.size := by omega
  have hscan := scanIndex_ofNat_succ i hindexFit
  have hfirstFit : first.toNat + 32 * (i + 1) < UInt256.size := by
    nlinarith
  have hsecondFit : second.toNat + 32 * (i + 1) < UInt256.size := by
    nlinarith
  have hfirstAddress :
      (firstAddress first (UInt256.ofNat (i + 1))).toNat =
        first.toNat + 32 * (i + 1) := by
    simp only [firstAddress, hscan]
    exact elementPtr_ofNat_toNat first i (by omega) hfirstFit
  have hsecondAddress :
      (secondAddress second (UInt256.ofNat (i + 1))).toNat =
        second.toNat + 32 * (i + 1) := by
    simp only [secondAddress, hscan]
    exact elementPtr_ofNat_toNat second i (by omega) hsecondFit
  have hfirstAccess : first.toNat + 32 ≤ 32 * aw.toNat := by
    nlinarith
  have hsecondAccess : second.toNat + 32 ≤ 32 * aw.toNat := by
    nlinarith
  have hfirstElementAccess :
      (firstAddress first (UInt256.ofNat (i + 1))).toNat + 32 ≤
        32 * aw.toNat := by
    rw [hfirstAddress]
    nlinarith
  have hsecondElementAccess :
      (secondAddress second (UInt256.ofNat (i + 1))).toNat + 32 ≤
        32 * aw.toNat := by
    rw [hsecondAddress]
    nlinarith
  constructor
  · rw [hscan, hfirstHeader,
      UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size),
      UInt256.toNat_ofNat_of_lt hcountFit]
    exact hi
  · rw [hscan, hsecondHeader,
      UInt256.toNat_ofNat_of_lt (by omega : i < UInt256.size),
      UInt256.toNat_ofNat_of_lt hcountFit]
    exact hi
  · exact afterHeader_eq_of_access aw first hfirstAccess
  · exact afterHeader_eq_of_access aw
      (firstAddress first (UInt256.ofNat (i + 1))) hfirstElementAccess
  · exact afterHeader_eq_of_access aw second hsecondAccess
  · exact afterHeader_eq_of_access aw
      (secondAddress second (UInt256.ofNat (i + 1))) hsecondElementAccess

def boolWord (value : Bool) : UInt256 :=
  if value then ⟨1⟩ else ⟨0⟩

def compareMemory (mem : ByteArray) (aw first second : UInt256) : Nat → Bool
  | 0 => false
  | n + 1 =>
      let left := firstValue mem aw first (UInt256.ofNat (n + 1))
      let right := secondValue mem aw second (UInt256.ofNat (n + 1))
      if left.toNat < right.toNat then true
      else if right.toNat < left.toNat then false
      else compareMemory mem aw first second n

def compareSteps (mem : ByteArray) (aw first second : UInt256) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let left := firstValue mem aw first (UInt256.ofNat (n + 1))
      let right := secondValue mem aw second (UInt256.ofNat (n + 1))
      if left.toNat < right.toNat then 60
      else if right.toNat < left.toNat then 109
      else if n = 0 then 114
      else 108 + compareSteps mem aw first second n

def compareGas (mem : ByteArray) (aw first second : UInt256) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let left := firstValue mem aw first (UInt256.ofNat (n + 1))
      let right := secondValue mem aw second (UInt256.ofNat (n + 1))
      if left.toNat < right.toNat then 210
      else if right.toNat < left.toNat then 389
      else if n = 0 then 416
      else 397 + compareGas mem aw first second n

/-- Exact arbitrary-length execution of `_limbsLt` after its positive loop guard. The gas and
step functions distinguish the first unequal limb and the all-equal path exactly. -/
theorem compareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {first second ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (hcount : 0 < count)
    (hfit : count < UInt256.size)
    (hcoverage : ∀ i, i < count →
      IterationCoverage mem aw first second (UInt256.ofNat (i + 1)))
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3707⟩
      (UInt256.ofNat count :: first :: second :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret
      (boolWord (compareMemory mem aw first second count) :: tail)
      mem aw rdata acc (k + compareSteps mem aw first second count)
      (C + compareGas mem aw first second count) := by
  induction count using Nat.strong_induction_on generalizing k C with
  | h count ih =>
      cases count with
      | zero => omega
      | succ n =>
          let index := UInt256.ofNat (n + 1)
          let left := firstValue mem aw first index
          let right := secondValue mem aw second index
          have hcurrent : IterationCoverage mem aw first second index := by
            simpa only [index] using hcoverage n (by omega)
          by_cases hless : left.toNat < right.toNat
          · have rd := iterationLess (by omega) hcurrent hless hret h
            simpa only [compareMemory, compareSteps, compareGas, left, right,
              index, if_pos hless, boolWord] using rd
          · by_cases hgreater : right.toNat < left.toNat
            · have rd := iterationGreater (by omega) hcurrent hgreater hret h
              simpa only [compareMemory, compareSteps, compareGas, left, right,
                index, if_neg hless, if_pos hgreater, boolWord] using rd
            · have hequalNat : left.toNat = right.toNat := by omega
              have hequal : left = right := by
                apply u256_inj
                exact hequalNat
              cases n with
              | zero =>
                  have hindex : scanIndex index = ⟨0⟩ := by
                    simpa only [index] using scanIndex_ofNat_succ 0 (by omega)
                  have rd := iterationEqualEnd (by omega) hcurrent hequal hindex hret h
                  simpa only [compareMemory, compareSteps, compareGas, left, right,
                    index, if_neg hless, if_neg hgreater, boolWord] using rd
              | succ n =>
                  have hscan : scanIndex index = UInt256.ofNat (n + 1) := by
                    simpa only [index] using scanIndex_ofNat_succ (n + 1) (by omega)
                  have hnonzero : scanIndex index ≠ ⟨0⟩ := by
                    rw [hscan]
                    intro hzero
                    have hnats := congrArg UInt256.toNat hzero
                    rw [UInt256.toNat_ofNat_of_lt (by omega : n + 1 < UInt256.size)] at hnats
                    norm_num at hnats
                  have rdNext := iterationEqualContinue
                    (by omega) hcurrent hequal hnonzero h
                  rw [hscan] at rdNext
                  have hcoverageNext : ∀ i, i < n + 1 →
                      IterationCoverage mem aw first second (UInt256.ofNat (i + 1)) := by
                    intro i hi
                    exact hcoverage i (by omega)
                  have rdFinal := ih (n + 1) (by omega)
                    (k := k + 108) (C := C + 397)
                    (by omega) (by omega) hcoverageNext rdNext
                  have normalized := rdFinal.withIndices
                    (k' := k + compareSteps mem aw first second (n + 2))
                    (C' := C + compareGas mem aw first second (n + 2))
                    (by
                      conv_rhs => rw [compareSteps]
                      rw [if_neg hless, if_neg hgreater,
                        if_neg (by omega : n + 1 ≠ 0)]
                      omega)
                    (by
                      conv_rhs => rw [compareGas]
                      rw [if_neg hless, if_neg hgreater,
                        if_neg (by omega : n + 1 ≠ 0)]
                      omega)
                  simpa only [compareMemory, left, right, index,
                    if_neg hless, if_neg hgreater] using normalized

def comparisonWords (mem : ByteArray) (aw ptr : UInt256) : Nat → List UInt256
  | 0 => []
  | n + 1 =>
      comparisonWords mem aw ptr n ++
        [firstValue mem aw ptr (UInt256.ofNat (n + 1))]

@[simp] theorem comparisonWords_length
    (mem : ByteArray) (aw ptr : UInt256) (count : Nat) :
    (comparisonWords mem aw ptr count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [comparisonWords, List.length_append,
      List.length_singleton, ih]

/-- The execution-oriented recursive comparison is exactly the existing descending-limb pure
predicate over the words read from the two Solidity arrays. -/
theorem compareMemory_eq_true_iff
    (mem : ByteArray) (aw first second : UInt256) (count : Nat) :
    compareMemory mem aw first second count = true ↔
      limbsLtMSB (comparisonWords mem aw first count)
        (comparisonWords mem aw second count) := by
  induction count with
  | zero => simp [compareMemory, comparisonWords, limbsLtMSB]
  | succ count ih =>
      let left := firstValue mem aw first (UInt256.ofNat (count + 1))
      let right := secondValue mem aw second (UInt256.ofNat (count + 1))
      have hlength :
          (comparisonWords mem aw first count).length =
            (comparisonWords mem aw second count).length := by
        simp only [comparisonWords_length]
      by_cases hless : left.toNat < right.toNat
      · have hne : Modexp.wordLimbsToNat [left] ≠
            Modexp.wordLimbsToNat [right] := by
          simp only [Modexp.wordLimbsToNat]
          omega
        have hsuffix := limbsLtMSB_append_of_suffix_ne
          (comparisonWords mem aw first count)
          (comparisonWords mem aw second count) [left] [right]
          hlength (by simp) hne
        change (if left.toNat < right.toNat then true
            else if right.toNat < left.toNat then false
            else compareMemory mem aw first second count) = true ↔
          limbsLtMSB
            (comparisonWords mem aw first count ++ [left])
            (comparisonWords mem aw second count ++ [right])
        rw [if_pos hless, hsuffix, limbsLtMSB_singleton_iff]
        simp only [hless]
      · by_cases hgreater : right.toNat < left.toNat
        · have hne : Modexp.wordLimbsToNat [left] ≠
              Modexp.wordLimbsToNat [right] := by
            simp only [Modexp.wordLimbsToNat]
            omega
          have hsuffix := limbsLtMSB_append_of_suffix_ne
            (comparisonWords mem aw first count)
            (comparisonWords mem aw second count) [left] [right]
            hlength (by simp) hne
          change (if left.toNat < right.toNat then true
              else if right.toNat < left.toNat then false
              else compareMemory mem aw first second count) = true ↔
            limbsLtMSB
              (comparisonWords mem aw first count ++ [left])
              (comparisonWords mem aw second count ++ [right])
          rw [if_neg hless, if_pos hgreater, hsuffix,
            limbsLtMSB_singleton_iff]
          simp only [Bool.false_eq_true, false_iff, not_lt]
          omega
        · have hequalNat : left.toNat = right.toNat := by omega
          have hequal : left = right := by
            apply u256_inj
            exact hequalNat
          change (if left.toNat < right.toNat then true
              else if right.toNat < left.toNat then false
              else compareMemory mem aw first second count) = true ↔
            limbsLtMSB
              (comparisonWords mem aw first count ++ [left])
              (comparisonWords mem aw second count ++ [right])
          rw [if_neg hless, if_neg hgreater, hequal,
            limbsLtMSB_append_equal _ _ right hlength]
          exact ih

theorem compareMemory_iff_value_lt
    (mem : ByteArray) (aw first second : UInt256) (count : Nat) :
    compareMemory mem aw first second count = true ↔
      Modexp.wordLimbsToNat (comparisonWords mem aw first count) <
        Modexp.wordLimbsToNat (comparisonWords mem aw second count) := by
  rw [compareMemory_eq_true_iff,
    limbsLtMSB_iff _ _ (by simp only [comparisonWords_length])]

theorem compareMemory_eq_false_iff_value_ge
    (mem : ByteArray) (aw first second : UInt256) (count : Nat) :
    compareMemory mem aw first second count = false ↔
      Modexp.wordLimbsToNat (comparisonWords mem aw second count) ≤
        Modexp.wordLimbsToNat (comparisonWords mem aw first count) := by
  constructor
  · intro hfalse
    have hnlt : ¬ Modexp.wordLimbsToNat (comparisonWords mem aw first count) <
        Modexp.wordLimbsToNat (comparisonWords mem aw second count) := by
      intro hlt
      have htrue := (compareMemory_iff_value_lt mem aw first second count).2 hlt
      rw [hfalse] at htrue
      contradiction
    omega
  · intro hge
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have hlt := (compareMemory_iff_value_lt mem aw first second count).1 htrue
    omega

/-- Caller-facing `_limbsLt` contract, including the generated function setup at PC 2038 and
return to PC 2051. -/
theorem fromCallerEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {first second : UInt256}
    (hdepth : tail.length + 11 ≤ 1019)
    (hcount : 0 < count)
    (hfit : count < UInt256.size)
    (hcoverage : ∀ i, i < count →
      IterationCoverage mem aw first second (UInt256.ofNat (i + 1)))
    (h : RDx runtimeBytecode ee g s0 ⟨2038⟩
      (first :: second :: UInt256.ofNat count :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2051⟩
      (boolWord (compareMemory mem aw first second count) :: second ::
        UInt256.ofNat count :: first :: second :: UInt256.ofNat count :: tail)
      mem aw rdata acc
      (k + 16 + compareSteps mem aw first second count)
      (C + 54 + compareGas mem aw first second count) := by
  have rd3700 := GeneratedTraces.trace_2038_body
    (by omega) h
  have hcondition : UInt256.ofNat count ≠ ⟨0⟩ := by
    intro hzero
    have hnats := congrArg UInt256.toNat hzero
    rw [UInt256.toNat_ofNat_of_lt hfit] at hnats
    norm_num at hnats
    omega
  have rd3707 := rd3700.jumpiT (by native_decide) hcondition
    (by native_decide) (by simp only [List.length_cons]; omega)
  have hret : (D_J runtimeBytecode 0).contains ⟨2051⟩ = true := by
    native_decide
  have rd2051 := compareExact
    (tail := second :: UInt256.ofNat count :: first :: second ::
      UInt256.ofNat count :: tail)
    (by simp only [List.length_cons]; omega) hcount hfit hcoverage hret rd3707
  have normalized := rd2051.withIndices
    (k' := k + 16 + compareSteps mem aw first second count)
    (C' := C + 54 + compareGas mem aw first second count)
    (by omega) (by omega)
  exact normalized

/-- Caller-facing comparison contract with its loop coverage discharged by concrete Solidity-array
layout facts. -/
theorem fromCallerEntryExactOfArrayGeometry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {first second : UInt256}
    (hdepth : tail.length + 11 ≤ 1019)
    (hcountPositive : 0 < count)
    (hcount : count ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstHeader : headerWord mem aw first = UInt256.ofNat count)
    (hsecondHeader : headerWord mem aw second = UInt256.ofNat count)
    (hfirstRange : first.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hsecondRange : second.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (h : RDx runtimeBytecode ee g s0 ⟨2038⟩
      (first :: second :: UInt256.ofNat count :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2051⟩
      (boolWord (compareMemory mem aw first second count) :: second ::
        UInt256.ofNat count :: first :: second :: UInt256.ofNat count :: tail)
      mem aw rdata acc
      (k + 16 + compareSteps mem aw first second count)
      (C + 54 + compareGas mem aw first second count) := by
  have hfit : count < UInt256.size := by
    have hsmall : 32 < UInt256.size := by decide
    omega
  exact fromCallerEntryExact hdepth hcountPositive hfit
    (iterationCoverage_of_array_geometry mem aw first second count hcount
      hawFit hfirstHeader hsecondHeader hfirstRange hsecondRange) h

end Modexp.MultiLimbOddCompare
