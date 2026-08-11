import Examples.Precompiles.Modexp.MultiLimbSchoolbookZeroShiftRemainderContract
import Examples.Precompiles.Modexp.MultiLimbSchoolbookDenormalizationSemantic

/-!
# Concrete semantics of the zero-shift remainder copy

When Knuth normalization selects shift zero, the deployed branch copies the terminal `u` words
directly into `rem`. This file proves the final concrete destination slice equals the initial
source slice while retaining the separate exact execution theorem and gas recurrence.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookZeroShiftRemainderSemantic

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic
open MultiLimbSchoolbookDenormalization
open MultiLimbSchoolbookDenormalizationSemantic
open MultiLimbSchoolbookZeroShiftRemainder

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Later direct-copy stores preserve a wholly lower prior destination word. -/
theorem copyRange_preserves_arrayWord_below
    (aw readArray u rem : UInt256) (sourceIndex index count : Nat)
    (mem : ByteArray)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count ->
      (arrayAddress readArray sourceIndex).toNat + 32 ≤
        (arrayAddress rem (index + j)).toNat) :
    arrayWord (copyRange aw u rem index count mem).memory aw readArray sourceIndex =
      arrayWord mem aw readArray sourceIndex := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have hhead := arrayWord_storeRemainder_below mem aw readArray rem word sourceIndex
        index hheadWrite (by simpa using hbelow 0 (by omega))
      have htail := ih (index + 1) nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))
      change arrayWord (copyRange aw u rem (index + 1) count nextMem).memory aw
        readArray sourceIndex = _
      exact htail.trans hhead

/-- Direct-copy stores preserve every source word wholly above the destination range. -/
theorem copyRange_preserves_arrayWord_above
    (aw readArray u rem : UInt256) (sourceIndex index count : Nat)
    (mem : ByteArray)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤
        (arrayAddress readArray sourceIndex).toNat) :
    arrayWord (copyRange aw u rem index count mem).memory aw readArray sourceIndex =
      arrayWord mem aw readArray sourceIndex := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have hhead := arrayWord_storeRemainder_above mem aw readArray rem word sourceIndex
        index hheadWrite (by simpa using habove 0 (by omega))
      have htail := ih (index + 1) nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))
      change arrayWord (copyRange aw u rem (index + 1) count nextMem).memory aw
        readArray sourceIndex = _
      exact htail.trans hhead

/-- Direct-copy stores preserve a complete raw word below the destination range. -/
theorem copyRange_preserves_read_below
    (aw u rem : UInt256) (read index count : Nat) (mem : ByteArray)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count ->
      read + 32 ≤ (arrayAddress rem (index + j)).toNat) :
    (copyRange aw u rem index count mem).memory.readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have hhead : nextMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
        dsimp only [nextMem]
        unfold storeRemainderWord
        exact write32_read_below word.toByteArray mem (arrayAddress rem index).toNat read
          (by rw [toByteArray_size]) (by omega) (by simpa using hbelow 0 (by omega))
      have htail := ih (index + 1) nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))
      change (copyRange aw u rem (index + 1) count nextMem).memory.readWithPadding
        read 32 = _
      exact htail.trans hhead

/-- Direct-copy stores preserve a padded raw word wholly above the destination range. -/
theorem copyRange_preserves_read_above
    (aw u rem : UInt256) (read index count : Nat) (mem : ByteArray)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ read) :
    (copyRange aw u rem index count mem).memory.readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have hhead : nextMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
        dsimp only [nextMem]
        unfold storeRemainderWord
        exact write32_read_above_padded word.toByteArray mem (arrayAddress rem index).toNat
          read (by rw [toByteArray_size]) hheadWrite (by simpa using habove 0 (by omega))
      have htail := ih (index + 1) nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))
      change (copyRange aw u rem (index + 1) count nextMem).memory.readWithPadding
        read 32 = _
      exact htail.trans hhead

/-- In-bounds direct-copy stores preserve the concrete byte-array extent. -/
theorem copyRange_size_eq
    (aw u rem : UInt256) (index count : Nat) (mem : ByteArray)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size) :
    (copyRange aw u rem index count mem).memory.size = mem.size := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have htail := ih (index + 1) nextMem (by
        intro j hj
        rw [hnextSize]
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
      exact htail.trans hnextSize

/-- The complete operational direct-copy recurrence leaves the original `u` slice in `rem`. -/
theorem copyRange_finalSlice
    (aw u rem : UInt256) (index count : Nat) (mem : ByteArray)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hremBelowSource : ∀ i j, i < count -> j < count ->
      (arrayAddress rem (index + i)).toNat + 32 ≤
        (arrayAddress u (index + j)).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress rem (index + i)).toNat + 32 ≤
        (arrayAddress rem (index + j)).toNat) :
    arrayReadWords (copyRange aw u rem index count mem).memory aw rem index count =
      arrayReadWords mem aw u index count := by
  induction count generalizing index mem with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw u index
      let nextMem := storeRemainderWord mem rem index word
      have hheadWrite : (arrayAddress rem index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hheadActive : (arrayAddress rem index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeRemainderWord_size_eq mem rem word index hheadWrite
      have hself : arrayWord nextMem aw rem index = word :=
        arrayWord_storeRemainder_self mem aw rem word index hawFit hheadWrite hheadActive
      have hheadPreserved := copyRange_preserves_arrayWord_below aw rem u rem index
        (index + 1) count nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hordered 0 (j + 1) (by omega) (by omega))
      have hsourceFrame :
          arrayReadWords nextMem aw u (index + 1) count =
            arrayReadWords mem aw u (index + 1) count := by
        simpa only [nextMem, storeRemainderWord,
          MultiLimbSchoolbookSingle.storeQuotient] using
          arrayReadWords_storeValue_above mem aw u rem word (index + 1) count index
            hheadWrite (by
              intro j hj
              simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
                hremBelowSource 0 (j + 1) (by omega) (by omega))
      have htail := ih (index + 1) nextMem
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega))
        (by
          intro i j hi hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hremBelowSource (i + 1) (j + 1) (by omega) (by omega))
        (by
          intro i j hij hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hordered (i + 1) (j + 1) (by omega) (by omega))
      rw [hsourceFrame] at htail
      simp only [copyRange, arrayReadWords]
      rw [hheadPreserved, hself, htail]

/-- Natural-value form of the direct-copy theorem. -/
theorem copyRange_finalSlice_toNat
    (aw u rem : UInt256) (index count : Nat) (mem : ByteArray)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress rem (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hremBelowSource : ∀ i j, i < count -> j < count ->
      (arrayAddress rem (index + i)).toNat + 32 ≤
        (arrayAddress u (index + j)).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress rem (index + i)).toNat + 32 ≤
        (arrayAddress rem (index + j)).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords (copyRange aw u rem index count mem).memory aw rem index count) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw u index count) := by
  rw [copyRange_finalSlice aw u rem index count mem hawFit hwrite hactive
    hremBelowSource hordered]

end Modexp.MultiLimbSchoolbookZeroShiftRemainderSemantic
