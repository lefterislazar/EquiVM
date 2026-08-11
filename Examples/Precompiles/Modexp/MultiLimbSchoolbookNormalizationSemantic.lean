import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionSemantic
import Examples.Precompiles.Modexp.MultiLimbClzSemantic

/-!
# Pure semantics of Knuth normalization

The generated normalization loops shift little-endian limbs from low to high while carrying the
discarded high bits into the next word. This file proves that recurrence is ordinary unbounded
multiplication by the normalization factor. The concrete-memory observation layer below this
arithmetic result keeps the proof tied to the words read and written by the deployed loop.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookNormalizationSemantic

open MultiLimbSchoolbookNormalization

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem wordBase_eq_pow : UInt256.size = 2 ^ 256 := by
  norm_num [UInt256.size]

theorem shiftedCarry_toNat (word : UInt256) (shift : Nat)
    (hshiftPos : 0 < shift) (hshift : shift < 256) :
    (shiftedCarry word shift).toNat = word.toNat / 2 ^ (256 - shift) := by
  have hcomplement : 256 - shift < 256 := by omega
  have hcomplementWord : 256 - shift < UInt256.size :=
    lt_trans hcomplement (by decide)
  have hcomplementToNat : (UInt256.ofNat (256 - shift)).toNat = 256 - shift :=
    UInt256.toNat_ofNat_of_lt hcomplementWord
  unfold shiftedCarry
  rw [shiftRight_toNat_of_lt256 _ _ (by simpa only [hcomplementToNat] using hcomplement),
    hcomplementToNat]

private theorem shiftedLeft_toNat (word : UInt256) (shift : Nat)
    (hshift : shift < 256) :
    (word.shiftLeft (UInt256.ofNat shift)).toNat =
      (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift := by
  have hshiftWord : shift < UInt256.size := lt_trans hshift (by decide)
  rw [ushl_ofNat_toNat word shift hshift, Nat.shiftLeft_eq]
  rw [wordBase_eq_pow]
  have hfactor : 2 ^ 256 = 2 ^ (256 - shift) * 2 ^ shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hfactor, Nat.mul_mod_mul_right]

theorem shiftedCarry_lt (word : UInt256) (shift : Nat)
    (hshiftPos : 0 < shift) (hshift : shift < 256) :
    (shiftedCarry word shift).toNat < 2 ^ shift := by
  rw [shiftedCarry_toNat word shift hshiftPos hshift]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc
    word.toNat < UInt256.size := word.val.isLt
    _ = 2 ^ shift * 2 ^ (256 - shift) := by
      rw [wordBase_eq_pow, ← Nat.pow_add]
      congr 1
      omega
    _ = 2 ^ shift * 2 ^ (256 - shift) := rfl

/-- A positive CLZ-selected shift cannot produce a carry above the original top word. -/
theorem shiftedCarry_clzResult_eq_zero
    (top : UInt256) (hshiftPos : 0 < (MultiLimbClz.clzResult top).n) :
    shiftedCarry top (MultiLimbClz.clzResult top).n = ⟨0⟩ := by
  let shift := (MultiLimbClz.clzResult top).n
  have hshiftLe : shift ≤ 255 := MultiLimbClz.clzResult_n_le top
  have hshift : shift < 256 := by omega
  have hmul : top.toNat * 2 ^ shift < 2 ^ 256 := by
    rw [← MultiLimbClz.normalizedTop_relation]
    exact MultiLimbClz.normalizedTop_upper top
  have hfactor : 2 ^ 256 = 2 ^ (256 - shift) * 2 ^ shift := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega : shift ≤ 256)]
  have htop : top.toNat < 2 ^ (256 - shift) := by
    apply Nat.lt_of_mul_lt_mul_right
    rw [← hfactor]
    exact hmul
  apply u256_inj
  rw [shiftedCarry_toNat top shift hshiftPos hshift]
  norm_num [Nat.div_eq_of_lt htop]

/-- One generated normalization update recomposes to the shifted source word plus its incoming
carry, with no modular loss once the outgoing carry is retained. -/
theorem shiftedWord_recompose
    (word carry : UInt256) (shift : Nat)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hcarry : carry.toNat < 2 ^ shift) :
    (shiftedWord word carry shift).toNat +
        UInt256.size * (shiftedCarry word shift).toNat =
      word.toNat * 2 ^ shift + carry.toNat := by
  have hleft := shiftedLeft_toNat word shift hshift
  have hcarryOut := shiftedCarry_toNat word shift hshiftPos hshift
  have hrem : word.toNat % 2 ^ (256 - shift) < 2 ^ (256 - shift) :=
    Nat.mod_lt _ (by positivity)
  have hbase : UInt256.size = 2 ^ (256 - shift) * 2 ^ shift := by
    rw [wordBase_eq_pow, ← Nat.pow_add]
    congr 1
    omega
  have hshiftedBound :
      (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift < UInt256.size := by
    rw [hbase]
    exact Nat.mul_lt_mul_of_pos_right hrem (by positivity)
  have hor :
      Nat.lor carry.toNat ((word.toNat % 2 ^ (256 - shift)) * 2 ^ shift) =
        carry.toNat + (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift := by
    exact nat_lor_shift_add carry.toNat (word.toNat % 2 ^ (256 - shift)) shift hcarry
  have horRev :
      Nat.lor ((word.toNat % 2 ^ (256 - shift)) * 2 ^ shift) carry.toNat =
        carry.toNat + (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift := by
    have hcomm := Nat.or_comm
      ((word.toNat % 2 ^ (256 - shift)) * 2 ^ shift) carry.toNat
    change Nat.lor ((word.toNat % 2 ^ (256 - shift)) * 2 ^ shift) carry.toNat =
      Nat.lor carry.toNat ((word.toNat % 2 ^ (256 - shift)) * 2 ^ shift) at hcomm
    rw [hcomm]
    exact hor
  have horBound :
      carry.toNat + (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift < UInt256.size := by
    rw [hbase]
    calc
      carry.toNat + (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift <
          2 ^ shift + (word.toNat % 2 ^ (256 - shift)) * 2 ^ shift :=
        Nat.add_lt_add_right hcarry _
      _ = (word.toNat % 2 ^ (256 - shift) + 1) * 2 ^ shift := by ring
      _ ≤ 2 ^ (256 - shift) * 2 ^ shift :=
        Nat.mul_le_mul_right _ (by omega)
  have hsplit := Nat.mod_add_div word.toNat (2 ^ (256 - shift))
  unfold shiftedWord
  rw [u256_lor_toNat, hleft, horRev,
    Nat.mod_eq_of_lt horBound, hcarryOut]
  rw [wordBase_eq_pow, show 2 ^ 256 = 2 ^ shift * 2 ^ (256 - shift) by
    rw [← Nat.pow_add]; congr 1; omega]
  nlinarith

/-- Pure low-to-high normalization recurrence, returning all stored words and the final carry. -/
def normalizeWords (shift : Nat) : UInt256 -> List UInt256 -> List UInt256 × UInt256
  | carry, [] => ([], carry)
  | carry, word :: words =>
      let rest := normalizeWords shift (shiftedCarry word shift) words
      (shiftedWord word carry shift :: rest.1, rest.2)

@[simp] theorem normalizeWords_length
    (shift : Nat) (carry : UInt256) (words : List UInt256) :
    (normalizeWords shift carry words).1.length = words.length := by
  induction words generalizing carry with
  | nil => rfl
  | cons word words ih =>
      simp [normalizeWords, ih]

/-- The arbitrary pure recurrence is exact multiplication by `2^shift`, including an arbitrary
bounded incoming carry and the final carry limb. -/
theorem normalizeWords_recompose
    (shift : Nat) (carry : UInt256) (words : List UInt256)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hcarry : carry.toNat < 2 ^ shift) :
    Modexp.wordLimbsToNat (normalizeWords shift carry words).1 +
        UInt256.size ^ words.length * (normalizeWords shift carry words).2.toNat =
      Modexp.wordLimbsToNat words * 2 ^ shift + carry.toNat := by
  induction words generalizing carry with
  | nil => simp [normalizeWords, Modexp.wordLimbsToNat]
  | cons word words ih =>
      have hstep := shiftedWord_recompose word carry shift hshiftPos hshift hcarry
      have hrest := ih (shiftedCarry word shift)
        (shiftedCarry_lt word shift hshiftPos hshift)
      simp only [normalizeWords, Modexp.wordLimbsToNat, List.length_cons]
      let rest := normalizeWords shift (shiftedCarry word shift) words
      change
        (shiftedWord word carry shift).toNat +
            UInt256.size * Modexp.wordLimbsToNat rest.1 +
            UInt256.size ^ (words.length + 1) * rest.2.toNat =
          (word.toNat + UInt256.size * Modexp.wordLimbsToNat words) * 2 ^ shift +
            carry.toNat
      change Modexp.wordLimbsToNat rest.1 +
          UInt256.size ^ words.length * rest.2.toNat =
        Modexp.wordLimbsToNat words * 2 ^ shift +
          (shiftedCarry word shift).toNat at hrest
      calc
        _ = (shiftedWord word carry shift).toNat + UInt256.size *
              (Modexp.wordLimbsToNat rest.1 +
                UInt256.size ^ words.length * rest.2.toNat) := by
              rw [pow_succ]
              ring
        _ = (shiftedWord word carry shift).toNat + UInt256.size *
              (Modexp.wordLimbsToNat words * 2 ^ shift +
                (shiftedCarry word shift).toNat) := by rw [hrest]
        _ = _ := by nlinarith

/-- Appending the final carry word yields exactly the shifted input value from the zero-carry
entry used by both deployed normalization loops. -/
theorem normalizeWords_zero_toNat
    (shift : Nat) (words : List UInt256)
    (hshiftPos : 0 < shift) (hshift : shift < 256) :
    Modexp.wordLimbsToNat
        ((normalizeWords shift ⟨0⟩ words).1 ++ [(normalizeWords shift ⟨0⟩ words).2]) =
      Modexp.wordLimbsToNat words * 2 ^ shift := by
  have hrecompose := normalizeWords_recompose shift ⟨0⟩ words hshiftPos hshift (by
    norm_num)
  rw [Modexp.wordLimbsToNat_append]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero, normalizeWords_length]
  simpa using hrecompose

/-- Words read from the concrete evolving memory by `shiftDivisor`. -/
def shiftDivisorInputWords
    (aw divisor v : UInt256) (shift : Nat) :
    Nat -> Nat -> ByteArray -> UInt256 -> List UInt256
  | _, 0, _, _ => []
  | index, count + 1, mem, carry =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      word :: shiftDivisorInputWords aw divisor v shift (index + 1) count nextMem
        (shiftedCarry word shift)

/-- Words written by the same concrete recurrence, in ascending destination order. -/
def shiftDivisorOutputWords
    (aw divisor v : UInt256) (shift : Nat) :
    Nat -> Nat -> ByteArray -> UInt256 -> List UInt256
  | _, 0, _, _ => []
  | index, count + 1, mem, carry =>
      let word := arrayWord mem aw divisor index
      let output := shiftedWord word carry shift
      let nextMem := storeShiftedWord mem v index shift word carry
      output :: shiftDivisorOutputWords aw divisor v shift (index + 1) count nextMem
        (shiftedCarry word shift)

@[simp] theorem shiftDivisorInputWords_length
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256) :
    (shiftDivisorInputWords aw divisor v shift index count mem carry).length = count := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih => simp [shiftDivisorInputWords, ih]

@[simp] theorem shiftDivisorOutputWords_length
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256) :
    (shiftDivisorOutputWords aw divisor v shift index count mem carry).length = count := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih => simp [shiftDivisorOutputWords, ih]

/-- The operational recurrence used by the exact normalization trace is multiplication by
`2^shift` over the precise words it reads and writes. -/
theorem shiftDivisorCollectors_recompose
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hcarry : carry.toNat < 2 ^ shift) :
    Modexp.wordLimbsToNat
        (shiftDivisorOutputWords aw divisor v shift index count mem carry) +
        UInt256.size ^ count *
          (shiftDivisor aw divisor v shift index count mem carry).carry.toNat =
      Modexp.wordLimbsToNat
          (shiftDivisorInputWords aw divisor v shift index count mem carry) * 2 ^ shift +
        carry.toNat := by
  induction count generalizing index mem carry with
  | zero => simp [shiftDivisorInputWords, shiftDivisorOutputWords, shiftDivisor,
      Modexp.wordLimbsToNat]
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let output := shiftedWord word carry shift
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hstep := shiftedWord_recompose word carry shift hshiftPos hshift hcarry
      have hrest := ih (index + 1) nextMem nextCarry
        (shiftedCarry_lt word shift hshiftPos hshift)
      simp only [shiftDivisorInputWords, shiftDivisorOutputWords, shiftDivisor,
        Modexp.wordLimbsToNat]
      change
        output.toNat + UInt256.size *
            Modexp.wordLimbsToNat
              (shiftDivisorOutputWords aw divisor v shift (index + 1) count
                nextMem nextCarry) +
            UInt256.size ^ (count + 1) *
              (shiftDivisor aw divisor v shift (index + 1) count
                nextMem nextCarry).carry.toNat =
          (word.toNat + UInt256.size *
            Modexp.wordLimbsToNat
              (shiftDivisorInputWords aw divisor v shift (index + 1) count
                nextMem nextCarry)) * 2 ^ shift + carry.toNat
      calc
        _ = output.toNat + UInt256.size *
              (Modexp.wordLimbsToNat
                  (shiftDivisorOutputWords aw divisor v shift (index + 1) count
                    nextMem nextCarry) +
                UInt256.size ^ count *
                  (shiftDivisor aw divisor v shift (index + 1) count
                    nextMem nextCarry).carry.toNat) := by
              rw [pow_succ]
              ring
        _ = output.toNat + UInt256.size *
              (Modexp.wordLimbsToNat
                  (shiftDivisorInputWords aw divisor v shift (index + 1) count
                    nextMem nextCarry) * 2 ^ shift + nextCarry.toNat) := by
              rw [hrest]
        _ = _ := by
              dsimp only [output, nextCarry] at hstep ⊢
              nlinarith

/-- Zero-carry concrete normalization, with its returned carry appended as the next limb, is
exact multiplication of the observed input words by the normalization factor. -/
theorem shiftDivisorCollectors_zero_toNat
    (aw divisor v : UInt256) (shift index count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256) :
    Modexp.wordLimbsToNat
        (shiftDivisorOutputWords aw divisor v shift index count mem ⟨0⟩ ++
          [(shiftDivisor aw divisor v shift index count mem ⟨0⟩).carry]) =
      Modexp.wordLimbsToNat
          (shiftDivisorInputWords aw divisor v shift index count mem ⟨0⟩) * 2 ^ shift := by
  have hrecompose := shiftDivisorCollectors_recompose aw divisor v shift index count mem ⟨0⟩
    hshiftPos hshift (by norm_num)
  rw [Modexp.wordLimbsToNat_append]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero,
    shiftDivisorOutputWords_length]
  simpa using hrecompose

/-- Consecutive guarded array words in ascending little-endian order. -/
def arrayReadWords
    (mem : ByteArray) (aw array : UInt256) : Nat -> Nat -> List UInt256
  | _, 0 => []
  | index, count + 1 =>
      arrayWord mem aw array index :: arrayReadWords mem aw array (index + 1) count

@[simp] theorem arrayReadWords_length
    (mem : ByteArray) (aw array : UInt256) (index count : Nat) :
    (arrayReadWords mem aw array index count).length = count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih => simp [arrayReadWords, ih]

theorem arrayReadWords_succ_append
    (mem : ByteArray) (aw array : UInt256) (index count : Nat) :
    arrayReadWords mem aw array index (count + 1) =
      arrayReadWords mem aw array index count ++ [arrayWord mem aw array (index + count)] := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      change arrayWord mem aw array index ::
          arrayReadWords mem aw array (index + 1) (count + 1) =
        arrayWord mem aw array index ::
          (arrayReadWords mem aw array (index + 1) count ++
            [arrayWord mem aw array (index + (count + 1))])
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using ih (index + 1)

theorem arrayWord_storeShifted_self
    (mem : ByteArray) (aw v word carry : UInt256) (index shift : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : (arrayAddress v index).toNat + 32 ≤ mem.size)
    (hactive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat) :
    arrayWord (storeShiftedWord mem v index shift word carry) aw v index =
      shiftedWord word carry shift := by
  simpa only [storeShiftedWord, MultiLimbSchoolbookSingle.storeQuotient,
    arrayWord, arrayAddress] using
    MultiLimbSchoolbookSingle.arrayWord_storeQuotient_self mem aw v
      (shiftedWord word carry shift) index hawFit hwrite hactive

theorem arrayWord_storeShifted_below
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex storeIndex shift : Nat)
    (hwrite : (arrayAddress v storeIndex).toNat + 32 ≤ mem.size)
    (hbelow : (arrayAddress source sourceIndex).toNat + 32 ≤
      (arrayAddress v storeIndex).toNat) :
    arrayWord (storeShiftedWord mem v storeIndex shift word carry) aw source sourceIndex =
      arrayWord mem aw source sourceIndex := by
  simpa only [storeShiftedWord, MultiLimbSchoolbookSingle.storeQuotient,
    arrayWord, arrayAddress] using
    MultiLimbSchoolbookSingle.arrayWord_storeQuotient_eq mem aw source v sourceIndex
      storeIndex (shiftedWord word carry shift) hwrite hbelow

theorem arrayWord_storeShifted_above
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex storeIndex shift : Nat)
    (hwrite : (arrayAddress v storeIndex).toNat + 32 ≤ mem.size)
    (habove : (arrayAddress v storeIndex).toNat + 32 ≤
      (arrayAddress source sourceIndex).toNat) :
    arrayWord (storeShiftedWord mem v storeIndex shift word carry) aw source sourceIndex =
      arrayWord mem aw source sourceIndex := by
  unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
  simpa only [storeShiftedWord, MultiLimbSchoolbookSingle.storeQuotient,
    arrayAddress] using
    MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq_above mem aw v
      (MultiLimbSchoolbookSingle.arrayAddress source sourceIndex) storeIndex
      (shiftedWord word carry shift) hwrite habove

theorem storeShiftedWord_size_eq
    (mem : ByteArray) (v word carry : UInt256) (index shift : Nat)
    (hwrite : (arrayAddress v index).toNat + 32 ≤ mem.size) :
    (storeShiftedWord mem v index shift word carry).size = mem.size := by
  simpa only [storeShiftedWord, MultiLimbSchoolbookSingle.storeQuotient,
    arrayAddress] using
    MultiLimbSchoolbookSingle.storeQuotient_size_eq mem v index
      (shiftedWord word carry shift) hwrite

/-- A fresh normalized-array payload store at the concrete memory frontier extends the backing
byte array by exactly one word. -/
theorem storeShiftedWord_size_frontier
    (mem : ByteArray) (v word carry : UInt256) (index shift : Nat)
    (hfrontier : (arrayAddress v index).toNat = mem.size) :
    (storeShiftedWord mem v index shift word carry).size = mem.size + 32 := by
  have hgap : (arrayAddress v index).toNat - mem.size < USize.size := by
    rw [hfrontier]
    have husize : 0 < USize.size := by native_decide
    omega
  unfold storeShiftedWord
  rw [MultiLimbMontgomeryCIOSSemantic.toByteArray_write_size_eq_max _ _ _ hgap,
    hfrontier]
  simp

/-- A shifted word written at the concrete frontier is available through the deployed guarded
array load when the allocator's active-word count covers it. -/
theorem arrayWord_storeShifted_self_frontier
    (mem : ByteArray) (aw v word carry : UInt256) (index shift : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : (arrayAddress v index).toNat = mem.size)
    (hactive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat) :
    arrayWord (storeShiftedWord mem v index shift word carry) aw v index =
      shiftedWord word carry shift := by
  let output := shiftedWord word carry shift
  let nextMem := storeShiftedWord mem v index shift word carry
  have hsize : nextMem.size = (arrayAddress v index).toNat + 32 := by
    dsimp only [nextMem]
    rw [storeShiftedWord_size_frontier mem v word carry index shift hfrontier,
      ← hfrontier]
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered nextMem aw := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    exact hactive
  have hword : (arrayAddress v index).toNat + 32 ≤ nextMem.size := by omega
  have hactiveGuard := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
    nextMem aw (arrayAddress v index) hcovered hawFit hword
  have hgap : (arrayAddress v index).toNat - mem.size < USize.size := by
    rw [hfrontier]
    have husize : 0 < USize.size := by native_decide
    omega
  have hread : nextMem.readWithPadding (arrayAddress v index).toNat 32 =
      UInt256.toByteArray output := by
    dsimp only [nextMem, output]
    unfold storeShiftedWord
    exact toByteArray_write_read_back_of_gap _ _ _ hgap
  have hmemGuard' :
      ¬ (MultiLimbSchoolbookShort.arrayAddress v index).toNat ≥
        (storeShiftedWord mem v index shift word carry).size := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress, nextMem] using
      (show ¬ (arrayAddress v index).toNat ≥ nextMem.size by omega)
  have hactiveGuard' :
      ¬ MultiLimbSchoolbookShort.arrayAddress v index ≥ aw * ⟨32⟩ := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hactiveGuard
  have hread' :
      (storeShiftedWord mem v index shift word carry).readWithPadding
          (MultiLimbSchoolbookShort.arrayAddress v index).toNat 32 =
        UInt256.toByteArray (shiftedWord word carry shift) := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress, nextMem, output] using hread
  unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
    MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨hmemGuard', hactiveGuard'⟩), hread',
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- A frontier-extending shifted store preserves any fully concrete, active source word below
that frontier. -/
theorem arrayWord_storeShifted_below_frontier
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex storeIndex shift : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : (arrayAddress v storeIndex).toNat = mem.size)
    (hstoreActive : (arrayAddress v storeIndex).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : (arrayAddress source sourceIndex).toNat + 32 ≤ mem.size) :
    arrayWord (storeShiftedWord mem v storeIndex shift word carry) aw source sourceIndex =
      arrayWord mem aw source sourceIndex := by
  let nextMem := storeShiftedWord mem v storeIndex shift word carry
  have hnextSize : nextMem.size = (arrayAddress v storeIndex).toNat + 32 := by
    dsimp only [nextMem]
    rw [storeShiftedWord_size_frontier mem v word carry storeIndex shift hfrontier,
      ← hfrontier]
  have holdCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [← hfrontier]
    omega
  have hnextCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered nextMem aw := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hnextSize]
    exact hstoreActive
  have holdActive := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
    mem aw (arrayAddress source sourceIndex) holdCovered hawFit hsourceMem
  have hnextMem : (arrayAddress source sourceIndex).toNat + 32 ≤ nextMem.size := by
    rw [hnextSize, hfrontier]
    omega
  have hnextActive := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
    nextMem aw (arrayAddress source sourceIndex) hnextCovered hawFit hnextMem
  have hgap : (arrayAddress v storeIndex).toNat - mem.size < USize.size := by
    rw [hfrontier]
    have husize : 0 < USize.size := by native_decide
    omega
  have hread : nextMem.readWithPadding (arrayAddress source sourceIndex).toNat 32 =
      mem.readWithPadding (arrayAddress source sourceIndex).toNat 32 := by
    dsimp only [nextMem]
    unfold storeShiftedWord
    exact toByteArray_write_read_below_of_gap _ _ _ _ hsourceMem (by
      rw [hfrontier]
      omega) hgap
  have hnextMemGuard' :
      ¬ (MultiLimbSchoolbookShort.arrayAddress source sourceIndex).toNat ≥
        (storeShiftedWord mem v storeIndex shift word carry).size := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress, nextMem] using
      (show ¬ (arrayAddress source sourceIndex).toNat ≥ nextMem.size by omega)
  have holdMemGuard' :
      ¬ (MultiLimbSchoolbookShort.arrayAddress source sourceIndex).toNat ≥ mem.size := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using
      (show ¬ (arrayAddress source sourceIndex).toNat ≥ mem.size by omega)
  have hnextActive' :
      ¬ MultiLimbSchoolbookShort.arrayAddress source sourceIndex ≥ aw * ⟨32⟩ := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hnextActive
  have holdActive' :
      ¬ MultiLimbSchoolbookShort.arrayAddress source sourceIndex ≥ aw * ⟨32⟩ := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using holdActive
  have hread' :
      (storeShiftedWord mem v storeIndex shift word carry).readWithPadding
          (MultiLimbSchoolbookShort.arrayAddress source sourceIndex).toNat 32 =
        mem.readWithPadding
          (MultiLimbSchoolbookShort.arrayAddress source sourceIndex).toNat 32 := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress, nextMem] using hread
  unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
    MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨hnextMemGuard', hnextActive'⟩),
    if_neg (not_or.mpr ⟨holdMemGuard', holdActive'⟩), hread']

/-- A frontier-extending shifted store preserves an earlier concrete source slice. -/
theorem arrayReadWords_storeShifted_below_frontier
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex count storeIndex shift : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : (arrayAddress v storeIndex).toNat = mem.size)
    (hstoreActive : (arrayAddress v storeIndex).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count ->
      (arrayAddress source (sourceIndex + j)).toNat + 32 ≤ mem.size) :
    arrayReadWords (storeShiftedWord mem v storeIndex shift word carry) aw source
        sourceIndex count = arrayReadWords mem aw source sourceIndex count := by
  induction count generalizing sourceIndex with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      rw [arrayWord_storeShifted_below_frontier mem aw source v word carry sourceIndex
        storeIndex shift hawFit hfrontier hstoreActive (by simpa using hsourceMem 0 (by omega))]
      rw [ih (sourceIndex + 1) (by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hsourceMem (j + 1) (by omega))]

theorem arrayReadWords_storeShifted_above
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex count storeIndex shift : Nat)
    (hwrite : (arrayAddress v storeIndex).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress v storeIndex).toNat + 32 ≤
        (arrayAddress source (sourceIndex + j)).toNat) :
    arrayReadWords (storeShiftedWord mem v storeIndex shift word carry) aw source
        sourceIndex count =
      arrayReadWords mem aw source sourceIndex count := by
  induction count generalizing sourceIndex with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      rw [arrayWord_storeShifted_above mem aw source v word carry sourceIndex storeIndex
        shift hwrite (by simpa using habove 0 (by omega))]
      rw [ih (sourceIndex + 1) (by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))]

theorem arrayReadWords_storeShifted_below
    (mem : ByteArray) (aw source v word carry : UInt256)
    (sourceIndex count storeIndex shift : Nat)
    (hwrite : (arrayAddress v storeIndex).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count ->
      (arrayAddress source (sourceIndex + j)).toNat + 32 ≤
        (arrayAddress v storeIndex).toNat) :
    arrayReadWords (storeShiftedWord mem v storeIndex shift word carry) aw source
        sourceIndex count =
      arrayReadWords mem aw source sourceIndex count := by
  induction count generalizing sourceIndex with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      rw [arrayWord_storeShifted_below mem aw source v word carry sourceIndex storeIndex
        shift hwrite (by simpa using hbelow 0 (by omega))]
      rw [ih (sourceIndex + 1) (by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))]

theorem arrayReadWords_storeValue_below
    (mem : ByteArray) (aw source destination value : UInt256)
    (sourceIndex count storeIndex : Nat)
    (hwrite : (arrayAddress destination storeIndex).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count ->
      (arrayAddress source (sourceIndex + j)).toNat + 32 ≤
        (arrayAddress destination storeIndex).toNat) :
    arrayReadWords (MultiLimbSchoolbookSingle.storeQuotient mem destination storeIndex value)
        aw source sourceIndex count =
      arrayReadWords mem aw source sourceIndex count := by
  induction count generalizing sourceIndex with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      have hhead :
          arrayWord (MultiLimbSchoolbookSingle.storeQuotient mem destination storeIndex value)
              aw source sourceIndex =
            arrayWord mem aw source sourceIndex := by
        simpa only [arrayWord, arrayAddress] using
          MultiLimbSchoolbookSingle.arrayWord_storeQuotient_eq mem aw source destination
            sourceIndex storeIndex value hwrite (by simpa using hbelow 0 (by omega))
      rw [hhead]
      rw [ih (sourceIndex + 1) (by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))]

theorem arrayReadWords_storeValue_above
    (mem : ByteArray) (aw source destination value : UInt256)
    (sourceIndex count storeIndex : Nat)
    (hwrite : (arrayAddress destination storeIndex).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress destination storeIndex).toNat + 32 ≤
        (arrayAddress source (sourceIndex + j)).toNat) :
    arrayReadWords (MultiLimbSchoolbookSingle.storeQuotient mem destination storeIndex value)
        aw source sourceIndex count =
      arrayReadWords mem aw source sourceIndex count := by
  induction count generalizing sourceIndex with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      have hhead :
          arrayWord (MultiLimbSchoolbookSingle.storeQuotient mem destination storeIndex value)
              aw source sourceIndex =
            arrayWord mem aw source sourceIndex := by
        unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
          MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
        simpa only [arrayAddress] using
          MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq_above mem aw destination
            (MultiLimbSchoolbookSingle.arrayAddress source sourceIndex) storeIndex value hwrite
            (by simpa using habove 0 (by omega))
      rw [hhead]
      rw [ih (sourceIndex + 1) (by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))]

/-- Ascending normalization writes leave every future source word unchanged, so the operational
input collector is the initial source slice. This covers both separated arrays and the in-place
dividend pass. -/
theorem shiftDivisorInputWords_eq_arrayReadWords
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hsourceAbove : ∀ i j, i < j -> j < count ->
      (arrayAddress v (index + i)).toNat + 32 ≤
        (arrayAddress divisor (index + j)).toNat) :
    shiftDivisorInputWords aw divisor v shift index count mem carry =
      arrayReadWords mem aw divisor index count := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro i j hij hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hsourceAbove (i + 1) (j + 1) (by omega) (by omega))
      have hframe := arrayReadWords_storeShifted_above mem aw divisor v word carry
        (index + 1) count index shift hheadWrite (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hsourceAbove 0 (j + 1) (by omega) (by omega))
      simp only [shiftDivisorInputWords, arrayReadWords]
      exact congrArg (List.cons word) (htail.trans hframe)

/-- Separated-array counterpart where every untouched source word lies below the newly allocated
destination write. -/
theorem shiftDivisorInputWords_eq_arrayReadWords_sourceBelow
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i j, i < j -> j < count ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤
        (arrayAddress v (index + i)).toNat) :
    shiftDivisorInputWords aw divisor v shift index count mem carry =
      arrayReadWords mem aw divisor index count := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro i j hij hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hsourceBelow (i + 1) (j + 1) (by omega) (by omega))
      have hframe := arrayReadWords_storeShifted_below mem aw divisor v word carry
        (index + 1) count index shift hheadWrite (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hsourceBelow 0 (j + 1) (by omega) (by omega))
      simp only [shiftDivisorInputWords, arrayReadWords]
      exact congrArg (List.cons word) (htail.trans hframe)

theorem shiftDivisor_preserves_arrayWord_below
    (aw readArray divisor v : UInt256) (shift sourceIndex index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count ->
      (arrayAddress readArray sourceIndex).toNat + 32 ≤
        (arrayAddress v (index + j)).toNat) :
    arrayWord (shiftDivisor aw divisor v shift index count mem carry).memory aw
        readArray sourceIndex =
      arrayWord mem aw readArray sourceIndex := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have hhead := arrayWord_storeShifted_below mem aw readArray v word carry sourceIndex
        index shift hheadWrite (by simpa using hbelow 0 (by omega))
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))
      change arrayWord
        (shiftDivisor aw divisor v shift (index + 1) count nextMem nextCarry).memory aw
          readArray sourceIndex = _
      exact htail.trans hhead

/-- A source word above every in-bounds low-to-high normalization store is preserved. -/
theorem shiftDivisor_preserves_arrayWord_above
    (aw readArray divisor v : UInt256) (shift sourceIndex index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤
        (arrayAddress readArray sourceIndex).toNat) :
    arrayWord (shiftDivisor aw divisor v shift index count mem carry).memory aw
        readArray sourceIndex =
      arrayWord mem aw readArray sourceIndex := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have hhead := arrayWord_storeShifted_above mem aw readArray v word carry sourceIndex
        index shift hheadWrite (by simpa using habove 0 (by omega))
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))
      change arrayWord
        (shiftDivisor aw divisor v shift (index + 1) count nextMem nextCarry).memory aw
          readArray sourceIndex = _
      exact htail.trans hhead

/-- Every operational output word is present in the final destination slice after all later
ascending stores. -/
theorem shiftDivisorOutputWords_eq_finalSlice
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress v (index + i)).toNat + 32 ≤
        (arrayAddress v (index + j)).toNat) :
    arrayReadWords (shiftDivisor aw divisor v shift index count mem carry).memory aw v
        index count =
      shiftDivisorOutputWords aw divisor v shift index count mem carry := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let output := shiftedWord word carry shift
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hheadActive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have hself : arrayWord nextMem aw v index = output :=
        arrayWord_storeShifted_self mem aw v word carry index shift hawFit hheadWrite
          hheadActive
      have hheadPreserved := shiftDivisor_preserves_arrayWord_below aw v divisor v shift index
        (index + 1) count nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            hordered 0 (j + 1) (by omega) (by omega))
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega))
        (by
          intro i j hij hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hordered (i + 1) (j + 1) (by omega) (by omega))
      simp only [arrayReadWords, shiftDivisorOutputWords, shiftDivisor]
      rw [hheadPreserved, hself, htail]

/-- A source word already below a fresh destination frontier survives every low-to-high appended
normalization store. -/
theorem shiftDivisor_preserves_arrayWord_below_frontier
    (aw readArray divisor v : UInt256) (shift sourceIndex index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hreadMem : (arrayAddress readArray sourceIndex).toNat + 32 ≤ mem.size) :
    arrayWord (shiftDivisor aw divisor v shift index count mem carry).memory aw
        readArray sourceIndex = arrayWord mem aw readArray sourceIndex := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hheadActive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 := by
        exact storeShiftedWord_size_frontier mem v word carry index shift hheadFrontier
      have hhead := arrayWord_storeShifted_below_frontier mem aw readArray v word carry
        sourceIndex index shift hawFit hheadFrontier hheadActive hreadMem
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          have hf := hfrontier (j + 1) (by omega)
          simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
          omega)
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega))
        (by rw [hnextSize]; omega)
      change arrayWord
        (shiftDivisor aw divisor v shift (index + 1) count nextMem nextCarry).memory aw
          readArray sourceIndex = _
      exact htail.trans hhead

/-- A complete fresh-destination normalization pass extends concrete memory by one word per
iteration. -/
theorem shiftDivisor_size_frontier
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j) :
    (shiftDivisor aw divisor v shift index count mem carry).memory.size =
      mem.size + 32 * count := by
  induction count generalizing index mem carry with
  | zero => simp [shiftDivisor]
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 :=
        storeShiftedWord_size_frontier mem v word carry index shift hheadFrontier
      have htailFrontier : ∀ j, j ≤ count ->
          (arrayAddress v (index + 1 + j)).toNat = nextMem.size + 32 * j := by
        intro j hj
        rw [hnextSize]
        have hf := hfrontier (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
        omega
      have htail := ih (index + 1) nextMem nextCarry htailFrontier
      change
        (shiftDivisor aw divisor v shift (index + 1) count nextMem nextCarry).memory.size = _
      rw [htail, hnextSize]
      omega

/-- If every destination word is already concrete, a complete in-place normalization pass keeps
the byte-array size unchanged. -/
theorem shiftDivisor_size_eq_of_inBounds
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size) :
    (shiftDivisor aw divisor v shift index count mem carry).memory.size = mem.size := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have htail := ih (index + 1) nextMem nextCarry (by
        intro j hj
        rw [hnextSize]
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
      change
        (shiftDivisor aw divisor v shift (index + 1) count nextMem nextCarry).memory.size = _
      exact htail.trans hnextSize

/-- When a fresh destination payload is materialized one word at a time, the operational source
collector still equals the original concrete source slice. -/
theorem shiftDivisorInputWords_eq_arrayReadWords_frontier
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤ mem.size) :
    shiftDivisorInputWords aw divisor v shift index count mem carry =
      arrayReadWords mem aw divisor index count := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hheadActive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 := by
        exact storeShiftedWord_size_frontier mem v word carry index shift hheadFrontier
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          have hf := hfrontier (j + 1) (by omega)
          simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
          omega)
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega))
        (by
          intro j hj
          rw [hnextSize]
          have hs := hsourceMem (j + 1) (by omega)
          simp only [Nat.add_assoc, Nat.add_comm 1 j] at hs ⊢
          omega)
      have hframe := arrayReadWords_storeShifted_below_frontier mem aw divisor v word carry
        (index + 1) count index shift hawFit hheadFrontier hheadActive (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hsourceMem (j + 1) (by omega))
      simp only [shiftDivisorInputWords, arrayReadWords]
      exact congrArg (List.cons word) (htail.trans hframe)

/-- Every output word appended to a fresh destination remains in the final concrete slice. -/
theorem shiftDivisorOutputWords_eq_finalSlice_frontier
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat) :
    arrayReadWords (shiftDivisor aw divisor v shift index count mem carry).memory aw v
        index count = shiftDivisorOutputWords aw divisor v shift index count mem carry := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let output := shiftedWord word carry shift
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hheadActive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 := by
        exact storeShiftedWord_size_frontier mem v word carry index shift hheadFrontier
      have hself : arrayWord nextMem aw v index = output :=
        arrayWord_storeShifted_self_frontier mem aw v word carry index shift hawFit
          hheadFrontier hheadActive
      have htailFrontier : ∀ j, j ≤ count ->
          (arrayAddress v (index + 1 + j)).toNat = nextMem.size + 32 * j := by
        intro j hj
        rw [hnextSize]
        have hf := hfrontier (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
        omega
      have htailActive : ∀ j, j < count ->
          (arrayAddress v (index + 1 + j)).toNat + 32 ≤ 32 * aw.toNat := by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega)
      have hheadPreserved := shiftDivisor_preserves_arrayWord_below_frontier
        aw v divisor v shift index (index + 1) count nextMem nextCarry hawFit
        htailFrontier htailActive (by
          rw [hnextSize, hheadFrontier])
      have htail := ih (index + 1) nextMem nextCarry htailFrontier htailActive
      simp only [arrayReadWords, shiftDivisorOutputWords, shiftDivisor]
      rw [hheadPreserved, hself, htail]

/-- Append-at-frontier normalization has the same exact natural-number semantics as the pure
carry recurrence. -/
theorem shiftDivisor_finalSlice_toNat_frontier
    (aw divisor v : UInt256) (shift index count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤ mem.size) :
    let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
    Modexp.wordLimbsToNat
        (arrayReadWords result.memory aw v index count ++ [result.carry]) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw divisor index count) * 2 ^ shift := by
  let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
  have hinputs := shiftDivisorInputWords_eq_arrayReadWords_frontier aw divisor v shift
    index count mem ⟨0⟩ hawFit hfrontier hactive hsourceMem
  have houtputs := shiftDivisorOutputWords_eq_finalSlice_frontier aw divisor v shift
    index count mem ⟨0⟩ hawFit hfrontier hactive
  have harithmetic := shiftDivisorCollectors_zero_toNat aw divisor v shift index count mem
    hshiftPos hshift
  rw [hinputs] at harithmetic
  rw [← houtputs] at harithmetic
  exact harithmetic

/-- The final concrete destination slice and returned carry represent the initial concrete source
slice multiplied by the normalization factor. All list identifications are derived from the
evolving-memory recurrence and ascending-write geometry. -/
theorem shiftDivisor_finalSlice_toNat
    (aw divisor v : UInt256) (shift index count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceAbove : ∀ i j, i < j -> j < count ->
      (arrayAddress v (index + i)).toNat + 32 ≤
        (arrayAddress divisor (index + j)).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress v (index + i)).toNat + 32 ≤
        (arrayAddress v (index + j)).toNat) :
    let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
    Modexp.wordLimbsToNat
        (arrayReadWords result.memory aw v index count ++ [result.carry]) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw divisor index count) * 2 ^ shift := by
  let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
  have hinputs := shiftDivisorInputWords_eq_arrayReadWords aw divisor v shift index count
    mem ⟨0⟩ hwrite hsourceAbove
  have houtputs := shiftDivisorOutputWords_eq_finalSlice aw divisor v shift index count mem
    ⟨0⟩ hawFit hwrite hactive hordered
  have harithmetic := shiftDivisorCollectors_zero_toNat aw divisor v shift index count mem
    hshiftPos hshift
  rw [hinputs] at harithmetic
  rw [← houtputs] at harithmetic
  exact harithmetic

/-- The same final-memory theorem for the separated divisor/`v` ordering, where original divisor
words lie below every destination write. -/
theorem shiftDivisor_finalSlice_toNat_sourceBelow
    (aw divisor v : UInt256) (shift index count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceBelow : ∀ i j, i < j -> j < count ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤
        (arrayAddress v (index + i)).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress v (index + i)).toNat + 32 ≤
        (arrayAddress v (index + j)).toNat) :
    let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
    Modexp.wordLimbsToNat
        (arrayReadWords result.memory aw v index count ++ [result.carry]) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw divisor index count) * 2 ^ shift := by
  let result := shiftDivisor aw divisor v shift index count mem ⟨0⟩
  have hinputs := shiftDivisorInputWords_eq_arrayReadWords_sourceBelow aw divisor v shift
    index count mem ⟨0⟩ hwrite hsourceBelow
  have houtputs := shiftDivisorOutputWords_eq_finalSlice aw divisor v shift index count mem
    ⟨0⟩ hawFit hwrite hactive hordered
  have harithmetic := shiftDivisorCollectors_zero_toNat aw divisor v shift index count mem
    hshiftPos hshift
  rw [hinputs] at harithmetic
  rw [← houtputs] at harithmetic
  exact harithmetic

/-- The deployed final dividend-carry store makes the proof-level appended carry an actual final
array word while preserving every lower normalized word. -/
theorem storeDividendTopCarry_slice
    (mem : ByteArray) (aw u carry : UInt256) (m : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : (arrayAddress u m).toNat + 32 ≤ mem.size)
    (hactive : (arrayAddress u m).toNat + 32 ≤ 32 * aw.toNat)
    (hlower : ∀ j, j < m ->
      (arrayAddress u j).toNat + 32 ≤ (arrayAddress u m).toNat) :
    arrayReadWords (storeDividendTopCarry mem u m carry) aw u 0 (m + 1) =
      arrayReadWords mem aw u 0 m ++ [carry] := by
  rw [arrayReadWords_succ_append]
  have hlowerFrame :
      arrayReadWords (storeDividendTopCarry mem u m carry) aw u 0 m =
        arrayReadWords mem aw u 0 m := by
    simpa only [storeDividendTopCarry, MultiLimbSchoolbookSingle.storeQuotient,
      Nat.zero_add] using
      arrayReadWords_storeValue_below mem aw u u carry 0 m m hwrite (by
        intro j hj
        simpa only [Nat.zero_add] using hlower j hj)
  rw [hlowerFrame]
  have htop : arrayWord (storeDividendTopCarry mem u m carry) aw u m = carry := by
    simpa only [storeDividendTopCarry, MultiLimbSchoolbookSingle.storeQuotient,
      arrayWord, arrayAddress] using
      MultiLimbSchoolbookSingle.arrayWord_storeQuotient_self mem aw u carry m hawFit hwrite
        hactive
  rw [Nat.zero_add, htop]

/-- Complete in-place dividend normalization, including the deployed final carry store, is exact
left multiplication of the original concrete dividend array. -/
theorem normalizedDividendArray_toNat
    (aw u : UInt256) (shift count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress u j).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress u j).toNat + 32 ≤ 32 * aw.toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress u i).toNat + 32 ≤ (arrayAddress u j).toNat)
    (htopWrite :
      let result := shiftDivisor aw u u shift 0 count mem ⟨0⟩
      (arrayAddress u count).toNat + 32 ≤ result.memory.size)
    (htopActive : (arrayAddress u count).toNat + 32 ≤ 32 * aw.toNat)
    (htopOrdered : ∀ j, j < count ->
      (arrayAddress u j).toNat + 32 ≤ (arrayAddress u count).toNat) :
    let result := shiftDivisor aw u u shift 0 count mem ⟨0⟩
    let finalMem := storeDividendTopCarry result.memory u count result.carry
    Modexp.wordLimbsToNat (arrayReadWords finalMem aw u 0 (count + 1)) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 count) * 2 ^ shift := by
  let result := shiftDivisor aw u u shift 0 count mem ⟨0⟩
  let finalMem := storeDividendTopCarry result.memory u count result.carry
  have hnormalized := shiftDivisor_finalSlice_toNat aw u u shift 0 count mem hshiftPos
    hshift hawFit (by simpa using hwrite) (by simpa using hactive)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hordered i j hij hj)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hordered i j hij hj)
  have hstored := storeDividendTopCarry_slice result.memory aw u result.carry count hawFit
    htopWrite htopActive htopOrdered
  dsimp only [result, finalMem] at hstored hnormalized ⊢
  rw [hstored]
  exact hnormalized

/-- For a nonempty separated divisor pass, the recurrence's returned carry is the shift carry of
the original highest source word. -/
theorem shiftDivisor_finalCarry_eq_sourceTop_sourceBelow
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count + 1 ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i j, i < j -> j < count + 1 ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤
        (arrayAddress v (index + i)).toNat) :
    (shiftDivisor aw divisor v shift index (count + 1) mem carry).carry =
      shiftedCarry (arrayWord mem aw divisor (index + count)) shift := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        storeShiftedWord_size_eq mem v word carry index shift hheadWrite
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro i j hij hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm 1 j] using
            hsourceBelow (i + 1) (j + 1) (by omega) (by omega))
      have htopFrame := arrayWord_storeShifted_below mem aw divisor v word carry
        (index + (count + 1)) index shift hheadWrite
        (by simpa using hsourceBelow 0 (count + 1) (by omega) (by omega))
      have hindex : index + 1 + count = index + (count + 1) := by omega
      rw [hindex] at htail
      rw [htopFrame] at htail
      exact htail

/-- Frontier-appending counterpart: the returned carry is still determined by the original top
source word. -/
theorem shiftDivisor_finalCarry_eq_sourceTop_frontier
    (aw divisor v : UInt256) (shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count + 1 ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count + 1 ->
      (arrayAddress v (index + j)).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count + 1 ->
      (arrayAddress divisor (index + j)).toNat + 32 ≤ mem.size) :
    (shiftDivisor aw divisor v shift index (count + 1) mem carry).carry =
      shiftedCarry (arrayWord mem aw divisor (index + count)) shift := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hheadActive : (arrayAddress v index).toNat + 32 ≤ 32 * aw.toNat := by
        simpa using hactive 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 :=
        storeShiftedWord_size_frontier mem v word carry index shift hheadFrontier
      have htailFrontier : ∀ j, j ≤ count + 1 ->
          (arrayAddress v (index + 1 + j)).toNat = nextMem.size + 32 * j := by
        intro j hj
        rw [hnextSize]
        have hf := hfrontier (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
        omega
      have htailActive : ∀ j, j < count + 1 ->
          (arrayAddress v (index + 1 + j)).toNat + 32 ≤ 32 * aw.toNat := by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hactive (j + 1) (by omega)
      have htailSource : ∀ j, j < count + 1 ->
          (arrayAddress divisor (index + 1 + j)).toNat + 32 ≤ nextMem.size := by
        intro j hj
        rw [hnextSize]
        have hs := hsourceMem (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hs ⊢
        omega
      have htail := ih (index + 1) nextMem nextCarry htailFrontier
        htailActive htailSource
      have htopFrame := arrayWord_storeShifted_below_frontier mem aw divisor v word carry
        (index + (count + 1)) index shift hawFit hheadFrontier hheadActive (by
          simpa using hsourceMem (count + 1) (by omega))
      have hindex : index + 1 + count = index + (count + 1) := by omega
      rw [hindex] at htail
      rw [htopFrame] at htail
      exact htail

/-- A CLZ-selected append-at-frontier divisor shift has zero outgoing top carry. -/
theorem shiftDivisor_clz_finalCarry_eq_zero_frontier
    (aw divisor v top : UInt256) (count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count + 1 ->
      (arrayAddress v j).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count + 1 ->
      (arrayAddress v j).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count + 1 ->
      (arrayAddress divisor j).toNat + 32 ≤ mem.size)
    (htop : arrayWord mem aw divisor count = top) :
    (shiftDivisor aw divisor v (MultiLimbClz.clzResult top).n 0 (count + 1)
      mem ⟨0⟩).carry = ⟨0⟩ := by
  have hcarry := shiftDivisor_finalCarry_eq_sourceTop_frontier aw divisor v
    (MultiLimbClz.clzResult top).n 0 count mem ⟨0⟩ hawFit
    (by simpa only [Nat.zero_add] using hfrontier)
    (by simpa only [Nat.zero_add] using hactive)
    (by simpa only [Nat.zero_add] using hsourceMem)
  rw [Nat.zero_add, htop, shiftedCarry_clzResult_eq_zero top hshiftPos] at hcarry
  exact hcarry

/-- With zero outgoing carry, the fixed-length appended destination slice itself is the shifted
source value. -/
theorem normalizedDivisorArray_toNat_frontier
    (aw divisor v : UInt256) (shift count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v j).toNat = mem.size + 32 * j)
    (hactive : ∀ j, j < count ->
      (arrayAddress v j).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceMem : ∀ j, j < count ->
      (arrayAddress divisor j).toNat + 32 ≤ mem.size)
    (hcarry : (shiftDivisor aw divisor v shift 0 count mem ⟨0⟩).carry = ⟨0⟩) :
    Modexp.wordLimbsToNat
        (arrayReadWords (shiftDivisor aw divisor v shift 0 count mem ⟨0⟩).memory aw v
          0 count) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw divisor 0 count) * 2 ^ shift := by
  have hnormalized := shiftDivisor_finalSlice_toNat_frontier aw divisor v shift 0 count
    mem hshiftPos hshift hawFit
    (by simpa only [Nat.zero_add] using hfrontier)
    (by simpa only [Nat.zero_add] using hactive)
    (by simpa only [Nat.zero_add] using hsourceMem)
  dsimp only at hnormalized
  rw [hcarry] at hnormalized
  rw [Modexp.wordLimbsToNat_append] at hnormalized
  simpa only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero] using hnormalized

/-- The final carry of a separated divisor pass is zero when its highest source word supplied the
positive CLZ normalization shift. -/
theorem shiftDivisor_clz_finalCarry_eq_zero
    (aw divisor v top : UInt256) (count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n)
    (hwrite : ∀ j, j < count + 1 ->
      (arrayAddress v j).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i j, i < j -> j < count + 1 ->
      (arrayAddress divisor j).toNat + 32 ≤ (arrayAddress v i).toNat)
    (htop : arrayWord mem aw divisor count = top) :
    (shiftDivisor aw divisor v (MultiLimbClz.clzResult top).n 0 (count + 1) mem ⟨0⟩).carry =
      ⟨0⟩ := by
  have hcarry := shiftDivisor_finalCarry_eq_sourceTop_sourceBelow aw divisor v
    (MultiLimbClz.clzResult top).n 0 count mem ⟨0⟩
    (by simpa only [Nat.zero_add] using hwrite)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hsourceBelow i j hij hj)
  rw [Nat.zero_add, htop, shiftedCarry_clzResult_eq_zero top hshiftPos] at hcarry
  exact hcarry

/-- When the CLZ-selected divisor shift has zero outgoing top carry, the actual fixed-length `v`
slice itself, without a proof-only extra limb, is the shifted original divisor. -/
theorem normalizedDivisorArray_toNat
    (aw divisor v : UInt256) (shift count : Nat) (mem : ByteArray)
    (hshiftPos : 0 < shift) (hshift : shift < 256)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v j).toNat + 32 ≤ mem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress v j).toNat + 32 ≤ 32 * aw.toNat)
    (hsourceBelow : ∀ i j, i < j -> j < count ->
      (arrayAddress divisor j).toNat + 32 ≤ (arrayAddress v i).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress v i).toNat + 32 ≤ (arrayAddress v j).toNat)
    (hcarry : (shiftDivisor aw divisor v shift 0 count mem ⟨0⟩).carry = ⟨0⟩) :
    Modexp.wordLimbsToNat
        (arrayReadWords (shiftDivisor aw divisor v shift 0 count mem ⟨0⟩).memory aw v
          0 count) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw divisor 0 count) * 2 ^ shift := by
  have hnormalized := shiftDivisor_finalSlice_toNat_sourceBelow aw divisor v shift 0 count
    mem hshiftPos hshift hawFit (by simpa using hwrite) (by simpa using hactive)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hsourceBelow i j hij hj)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hordered i j hij hj)
  dsimp only at hnormalized
  rw [hcarry] at hnormalized
  rw [Modexp.wordLimbsToNat_append] at hnormalized
  simpa only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero] using hnormalized


end Modexp.MultiLimbSchoolbookNormalizationSemantic
