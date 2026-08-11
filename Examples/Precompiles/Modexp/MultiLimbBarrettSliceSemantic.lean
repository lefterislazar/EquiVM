import Examples.Precompiles.Modexp.MultiLimbBarrettMulContract
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeLinks

/-!
# Barrett high-limb slice semantics

This module identifies the q1 and q3 `MCOPY` operations with concrete contiguous source-limb
windows.  The deployed pointer expressions include checked predecessors and word-to-byte shifts,
so their nonwrapping arithmetic is proved explicitly.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettSliceSemantic

open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbMontgomeryCIOSSemantic

/-- A consecutive memory-word range splits into adjacent low and high ranges. -/
theorem memoryWordsFrom_split (mem : ByteArray) (ptr left right : Nat) :
    memoryWordsFrom mem ptr (left + right) =
      memoryWordsFrom mem ptr left ++ memoryWordsFrom mem (ptr + 32 * left) right := by
  induction left generalizing ptr with
  | zero => simp [memoryWordsFrom]
  | succ left ih =>
      rw [show left + 1 + right = (left + right) + 1 by omega]
      simp only [memoryWordsFrom, List.cons_append]
      rw [ih]
      rw [show ptr + 32 + 32 * left = ptr + 32 * (left + 1) by omega]

/-- Dropping a low-limb prefix is ordinary division by its radix power. -/
theorem wordLimbsToNat_append_div_pow (low high : List UInt256) :
    Modexp.wordLimbsToNat (low ++ high) / UInt256.size ^ low.length =
      Modexp.wordLimbsToNat high := by
  rw [Modexp.wordLimbsToNat_append,
    Nat.add_mul_div_left _ _ (pow_pos (by decide : 0 < UInt256.size) _),
    Nat.div_eq_of_lt (Modexp.wordLimbsToNat_lt_pow low), Nat.zero_add]

/-- Keeping a low-limb prefix is ordinary reduction modulo its radix power. -/
theorem wordLimbsToNat_append_mod_pow (low high : List UInt256) :
    Modexp.wordLimbsToNat (low ++ high) % UInt256.size ^ low.length =
      Modexp.wordLimbsToNat low := by
  rw [Modexp.wordLimbsToNat_append]
  have hlow := Modexp.wordLimbsToNat_lt_pow low
  simp [Nat.mod_eq_of_lt hlow]

/-- A concrete low memory window is the full adjacent window reduced modulo its width. -/
theorem memoryWordsFrom_low_value
    (mem : ByteArray) (ptr low high fullValue : Nat)
    (hfull : Modexp.wordLimbsToNat (memoryWordsFrom mem ptr (low + high)) = fullValue) :
    Modexp.wordLimbsToNat (memoryWordsFrom mem ptr low) =
      fullValue % UInt256.size ^ low := by
  have hsplit := memoryWordsFrom_split mem ptr low high
  rw [← hfull]
  rw [hsplit]
  simpa only [memoryWordsFrom_length] using
    (wordLimbsToNat_append_mod_pow
      (memoryWordsFrom mem ptr low)
      (memoryWordsFrom mem (ptr + 32 * low) high)).symm

/-- Complete words read from an `MCOPY` placed at the concrete end of memory equal the
corresponding padded source words, even when the source suffix is only implicit zero memory. -/
theorem memoryWordsFrom_writeAtEnd_window
    (source base : ByteArray) (src totalWords offset words : Nat)
    (hbase64 : base.size + 32 * totalWords < 2 ^ 64)
    (hsource64 : src + 32 * totalWords < 2 ^ 64)
    (hwindow : offset + words ≤ totalWords) :
    memoryWordsFrom
        (source.write src base base.size (32 * totalWords))
        (base.size + 32 * offset) words =
      memoryWordsFrom source (src + 32 * offset) words := by
  induction words generalizing offset with
  | zero => rfl
  | succ words ih =>
      have hoffset : offset < totalWords := by omega
      have hread := writeAtEnd_readWithPadding_window source base src
        (32 * totalWords) (32 * offset) 32 hbase64 (by norm_num) (by omega)
      have hsourceRead :
          source.readWithPadding (src + 32 * offset) 32 =
            Model.readPadded source (src + 32 * offset) 32 :=
        readWithPadding_eq_model_readPadded source (src + 32 * offset) 32
          (by omega) (by norm_num)
      rw [← hsourceRead] at hread
      have htail := ih (offset + 1) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [show base.size + 32 * offset + 32 =
          base.size + 32 * (offset + 1) by ring,
        show src + 32 * offset + 32 = src + 32 * (offset + 1) by ring,
        hread, htail]

theorem q1CopyLengthWord_toNat (kWords : Nat) (hkShift : kWords + 1 < 2 ^ 251) :
    (q1CopyLengthWord kWords).toNat = 32 * (kWords + 1) := by
  exact ushl5_ofNat_toNat (kWords + 1) hkShift

theorem q1CopyDestinationWord_toNat (q1 : UInt256)
    (hfit : q1.toNat + 32 < UInt256.size) :
    (q1CopyDestinationWord q1).toNat = q1.toNat + 32 := by
  unfold q1CopyDestinationWord
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt hfit]

theorem q1CopySourceWord_toNat (product : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords - 1 < 2 ^ 251)
    (hfit : product.toNat + 32 * kWords < UInt256.size) :
    (q1CopySourceWord product kWords).toNat = product.toNat + 32 * kWords := by
  have hprev : UInt256.ofNat kWords + (⟨0⟩ : UInt256).lnot =
      UInt256.ofNat (kWords - 1) := by
    rw [show kWords = (kWords - 1) + 1 by omega, u256_add_comm]
    change Modexp.MultiLimbOddCompare.scanIndex
        (UInt256.ofNat ((kWords - 1) + 1)) = UInt256.ofNat (kWords - 1)
    exact Modexp.MultiLimbOddCompare.scanIndex_ofNat_succ (kWords - 1) (by omega)
  have hshift : ((UInt256.ofNat (kWords - 1)).shiftLeft ⟨5⟩).toNat =
      32 * (kWords - 1) := ushl5_ofNat_toNat (kWords - 1) hkShift
  have hfirst :
      (product + (UInt256.ofNat (kWords - 1)).shiftLeft ⟨5⟩).toNat =
        product.toNat + 32 * (kWords - 1) := by
    rw [uadd_toNat, hshift, Nat.mod_eq_of_lt (by omega)]
  unfold q1CopySourceWord
  rw [hprev, uadd_toNat, hfirst, show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The deployed q1 slice is the `k+1`-word product window beginning at limb `k-1`. -/
theorem q1CopiedMemory_words
    (mem : ByteArray) (q1 product : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hq1Fit : q1.toNat + 32 < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ mem.size)
    (hdest : q1.toNat + 32 ≤ mem.size) :
    memoryWordsFrom (q1CopiedMemory mem q1 product kWords)
        (q1.toNat + 32) (kWords + 1) =
      memoryWordsFrom mem (product.toNat + 32 * kWords) (kWords + 1) := by
  have hlength := q1CopyLengthWord_toNat kWords hkShift
  have hsrc := q1CopySourceWord_toNat product kWords hkPos hkWord
    (by omega) hproductFit
  have hdst := q1CopyDestinationWord_toNat q1 hq1Fit
  unfold q1CopiedMemory
  rw [hsrc, hdst, hlength]
  simpa only [Nat.zero_add, Nat.mul_zero] using
    memoryWordsFrom_write_copy_window mem mem (product.toNat + 32 * kWords)
      (q1.toNat + 32) (kWords + 1) 0 (kWords + 1) (by omega)
      (by omega) hdest (by omega)

/-- The q1 slice theorem with the actual schoolbook-product representation: the copy starts at
the concrete memory end and may consume implicit zero high limbs. -/
theorem q1CopiedMemory_words_padded
    (mem : ByteArray) (q1 product : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hq1Fit : q1.toNat + 32 < UInt256.size)
    (hdestEnd : q1.toNat + 32 = mem.size)
    (hsource64 : product.toNat + 32 * (2 * kWords + 1) < 2 ^ 64)
    (hdest64 : q1.toNat + 32 + 32 * (kWords + 1) < 2 ^ 64) :
    memoryWordsFrom (q1CopiedMemory mem q1 product kWords)
        (q1.toNat + 32) (kWords + 1) =
      memoryWordsFrom mem (product.toNat + 32 * kWords) (kWords + 1) := by
  have hlength := q1CopyLengthWord_toNat kWords hkShift
  have hsrc := q1CopySourceWord_toNat product kWords hkPos hkWord
    (by omega) hproductFit
  have hdst := q1CopyDestinationWord_toNat q1 hq1Fit
  unfold q1CopiedMemory
  rw [hsrc, hdst, hlength, hdestEnd]
  exact memoryWordsFrom_writeAtEnd_window mem mem
    (product.toNat + 32 * kWords) (kWords + 1) 0 (kWords + 1)
    (by simpa [hdestEnd] using hdest64) (by omega) (by omega)

/-- Numerically, the concrete q1 copy is division of the full `2*k`-word product by
`B^(k-1)`. -/
theorem q1CopiedMemory_value
    (mem : ByteArray) (q1 product : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hq1Fit : q1.toNat + 32 < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ mem.size)
    (hdest : q1.toNat + 32 ≤ mem.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q1CopiedMemory mem q1 product kWords)
          (q1.toNat + 32) (kWords + 1)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem (product.toNat + 32) (2 * kWords)) /
        UInt256.size ^ (kWords - 1) := by
  rw [q1CopiedMemory_words mem q1 product kWords hkPos hkWord hkShift
    hproductFit hq1Fit hsource hdest]
  have hsplit := memoryWordsFrom_split mem (product.toNat + 32)
    (kWords - 1) (kWords + 1)
  have hcount : kWords - 1 + (kWords + 1) = 2 * kWords := by omega
  rw [hcount] at hsplit
  have hoff : product.toNat + 32 + 32 * (kWords - 1) =
      product.toNat + 32 * kWords := by omega
  rw [hoff] at hsplit
  rw [hsplit]
  simpa only [memoryWordsFrom_length] using
    (wordLimbsToNat_append_div_pow
      (memoryWordsFrom mem (product.toNat + 32) (kWords - 1))
      (memoryWordsFrom mem (product.toNat + 32 * kWords) (kWords + 1))).symm

/-- Numeric q1 semantics for a product whose skipped zero rows remain implicit memory. -/
theorem q1CopiedMemory_value_padded
    (mem : ByteArray) (q1 product : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hq1Fit : q1.toNat + 32 < UInt256.size)
    (hdestEnd : q1.toNat + 32 = mem.size)
    (hsource64 : product.toNat + 32 * (2 * kWords + 1) < 2 ^ 64)
    (hdest64 : q1.toNat + 32 + 32 * (kWords + 1) < 2 ^ 64) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q1CopiedMemory mem q1 product kWords)
          (q1.toNat + 32) (kWords + 1)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem (product.toNat + 32) (2 * kWords)) /
        UInt256.size ^ (kWords - 1) := by
  rw [q1CopiedMemory_words_padded mem q1 product kWords hkPos hkWord hkShift
    hproductFit hq1Fit hdestEnd hsource64 hdest64]
  have hsplit := memoryWordsFrom_split mem (product.toNat + 32)
    (kWords - 1) (kWords + 1)
  have hcount : kWords - 1 + (kWords + 1) = 2 * kWords := by omega
  rw [hcount] at hsplit
  have hoff : product.toNat + 32 + 32 * (kWords - 1) =
      product.toNat + 32 * kWords := by omega
  rw [hoff] at hsplit
  rw [hsplit]
  simpa only [memoryWordsFrom_length] using
    (wordLimbsToNat_append_div_pow
      (memoryWordsFrom mem (product.toNat + 32) (kWords - 1))
      (memoryWordsFrom mem (product.toNat + 32 * kWords) (kWords + 1))).symm

theorem q3CopyLengthWord_toNat (kWords : Nat) (hkShift : kWords + 3 < 2 ^ 251) :
    (q3CopyLengthWord kWords).toNat = 32 * (kWords + 3) := by
  exact ushl5_ofNat_toNat (kWords + 3) hkShift

theorem q3CopyDestinationWord_toNat (q3 : UInt256)
    (hfit : q3.toNat + 32 < UInt256.size) :
    (q3CopyDestinationWord q3).toNat = q3.toNat + 32 := by
  unfold q3CopyDestinationWord
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt hfit]

theorem q3CopySourceWord_toNat (q2 : UInt256) (kWords : Nat)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hfit : q2.toNat + 32 * (kWords + 2) < UInt256.size) :
    (q3CopySourceWord q2 kWords).toNat = q2.toNat + 32 * (kWords + 2) := by
  have hshift : ((UInt256.ofNat kWords + ⟨1⟩).shiftLeft ⟨5⟩).toNat =
      32 * (kWords + 1) := by
    have hadd : UInt256.ofNat kWords + ⟨1⟩ = UInt256.ofNat (kWords + 1) := by
      apply u256_inj
      rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size),
        show (⟨1⟩ : UInt256).toNat = 1 by decide,
        UInt256.toNat_ofNat_of_lt (by omega : kWords + 1 < UInt256.size),
        Nat.mod_eq_of_lt (by omega : kWords + 1 < UInt256.size)]
    rw [hadd]
    exact ushl5_ofNat_toNat (kWords + 1) hkShift
  have hfirst :
      ((UInt256.ofNat kWords + ⟨1⟩).shiftLeft ⟨5⟩ + q2).toNat =
        32 * (kWords + 1) + q2.toNat := by
    rw [uadd_toNat, hshift, Nat.mod_eq_of_lt (by omega)]
  unfold q3CopySourceWord
  rw [uadd_toNat, hfirst, show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The deployed q3 slice is the `k+3`-word q2 window beginning at limb `k+1`. -/
theorem q3CopiedMemory_words
    (mem : ByteArray) (q3 q2 : UInt256) (kWords : Nat)
    (hkShift : kWords + 3 < 2 ^ 251)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hq3Fit : q3.toNat + 32 < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ mem.size)
    (hdest : q3.toNat + 32 ≤ mem.size) :
    memoryWordsFrom (q3CopiedMemory mem q3 q2 kWords)
        (q3.toNat + 32) (kWords + 3) =
      memoryWordsFrom mem (q2.toNat + 32 * (kWords + 2)) (kWords + 3) := by
  have hlength := q3CopyLengthWord_toNat kWords hkShift
  have hsrc := q3CopySourceWord_toNat q2 kWords (by omega) hq2Fit
  have hdst := q3CopyDestinationWord_toNat q3 hq3Fit
  unfold q3CopiedMemory
  rw [hsrc, hdst, hlength]
  simpa only [Nat.zero_add, Nat.mul_zero] using
    memoryWordsFrom_write_copy_window mem mem (q2.toNat + 32 * (kWords + 2))
      (q3.toNat + 32) (kWords + 3) 0 (kWords + 3) (by omega)
      (by omega) hdest (by omega)

/-- Numerically, the concrete q3 copy is division of the full q2 product by `B^(k+1)`. -/
theorem q3CopiedMemory_value
    (mem : ByteArray) (q3 q2 : UInt256) (kWords : Nat)
    (hkShift : kWords + 3 < 2 ^ 251)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hq3Fit : q3.toNat + 32 < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ mem.size)
    (hdest : q3.toNat + 32 ≤ mem.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q3CopiedMemory mem q3 q2 kWords)
          (q3.toNat + 32) (kWords + 3)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem (q2.toNat + 32) (2 * kWords + 4)) /
        UInt256.size ^ (kWords + 1) := by
  rw [q3CopiedMemory_words mem q3 q2 kWords hkShift hq2Fit hq3Fit hsource hdest]
  have hsplit := memoryWordsFrom_split mem (q2.toNat + 32)
    (kWords + 1) (kWords + 3)
  have hcount : kWords + 1 + (kWords + 3) = 2 * kWords + 4 := by omega
  rw [hcount] at hsplit
  have hoff : q2.toNat + 32 + 32 * (kWords + 1) =
      q2.toNat + 32 * (kWords + 2) := by omega
  rw [hoff] at hsplit
  rw [hsplit]
  simpa only [memoryWordsFrom_length] using
    (wordLimbsToNat_append_div_pow
      (memoryWordsFrom mem (q2.toNat + 32) (kWords + 1))
      (memoryWordsFrom mem (q2.toNat + 32 * (kWords + 2)) (kWords + 3))).symm

end Modexp.MultiLimbBarrettSliceSemantic
