import Examples.Precompiles.Modexp.MultiLimbBarrettTruncatedMulContract
import Examples.Precompiles.Modexp.MultiLimbBarrettSliceSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulFunctionSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupSemantic

/-! # Barrett truncated-product semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettTruncatedMulSemantic

open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettSliceSemantic
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbSchoolbookMulTrace

/-- q3 words observed by the exact truncated outer-row selector. -/
def truncatedSourceWords (q3 n r2 : UInt256) (kWords : Nat) :
    Nat → TruncatedOuterState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      q3Word state.memory state.activeWords q3 (UInt256.ofNat state.i) ::
        truncatedSourceWords q3 n r2 kWords count
          (truncatedRowAdvance q3 n r2 kWords state)

@[simp] theorem truncatedSourceWords_length
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState) :
    (truncatedSourceWords q3 n r2 kWords count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [truncatedSourceWords, ih]

/-- The q3 source collector can expose its final observed row. -/
theorem truncatedSourceWords_succ_last
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState) :
    truncatedSourceWords q3 n r2 kWords (count + 1) state =
      truncatedSourceWords q3 n r2 kWords count state ++
        [q3Word
          (truncatedRowsIterate q3 n r2 kWords count state).memory
          (truncatedRowsIterate q3 n r2 kWords count state).activeWords q3
          (UInt256.ofNat
            (truncatedRowsIterate q3 n r2 kWords count state).i)] := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := truncatedRowAdvance q3 n r2 kWords state
      change q3Word state.memory state.activeWords q3 (UInt256.ofNat state.i) ::
          truncatedSourceWords q3 n r2 kWords (count + 1) next =
        q3Word state.memory state.activeWords q3 (UInt256.ofNat state.i) ::
          (truncatedSourceWords q3 n r2 kWords count next ++
            [q3Word
              (truncatedRowsIterate q3 n r2 kWords (count + 1) state).memory
              (truncatedRowsIterate q3 n r2 kWords (count + 1) state).activeWords q3
              (UInt256.ofNat
                (truncatedRowsIterate q3 n r2 kWords (count + 1) state).i)])
      congr 1
      rw [ih]
      simp only [next, truncatedRowsIterate_advance]

/-- Updating a suffix by one exact schoolbook row has the expected value modulo the full result
width.  The omitted carry is multiplied by the truncation radix and therefore disappears. -/
theorem windowUpdate_mod
    (a : UInt256) (operandWords pre priorWords outputWords : List UInt256)
    (carry : UInt256) (shift width total : Nat)
    (hpre : pre.length = shift)
    (htotal : shift + width = total)
    (hrecompose :
      Modexp.wordLimbsToNat outputWords + UInt256.size ^ width * carry.toNat =
        Modexp.wordLimbsToNat priorWords +
          a.toNat * Modexp.wordLimbsToNat operandWords) :
    Modexp.wordLimbsToNat (pre ++ outputWords) % UInt256.size ^ total =
      (Modexp.wordLimbsToNat (pre ++ priorWords) +
        UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat operandWords)) %
          UInt256.size ^ total := by
  have hscaled := congrArg (fun value => UInt256.size ^ shift * value) hrecompose
  have heq :
      Modexp.wordLimbsToNat (pre ++ outputWords) +
          UInt256.size ^ total * carry.toNat =
        Modexp.wordLimbsToNat (pre ++ priorWords) +
          UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat operandWords) := by
    rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append, hpre]
    rw [← htotal, pow_add]
    ring_nf at hscaled ⊢
    omega
  calc
    Modexp.wordLimbsToNat (pre ++ outputWords) % UInt256.size ^ total =
        (Modexp.wordLimbsToNat (pre ++ outputWords) +
          UInt256.size ^ total * carry.toNat) % UInt256.size ^ total := by
            simp only [Nat.add_mul_mod_self_left]
    _ = (Modexp.wordLimbsToNat (pre ++ priorWords) +
          UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat operandWords)) %
            UInt256.size ^ total := by rw [heq]

/-- Once a low operand prefix is shifted to the end of the truncation range, omitted high operand
words contribute only multiples of the truncation radix. -/
theorem shiftedPrefixProduct_mod
    (a : UInt256) (low high : List UInt256) (shift total : Nat)
    (htotal : shift + low.length = total) :
    (UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat low)) %
        UInt256.size ^ total =
      (UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat (low ++ high))) %
        UInt256.size ^ total := by
  have heq : UInt256.size ^ shift *
        (a.toNat * Modexp.wordLimbsToNat (low ++ high)) =
      UInt256.size ^ shift * (a.toNat * Modexp.wordLimbsToNat low) +
        UInt256.size ^ total * (a.toNat * Modexp.wordLimbsToNat high) := by
    rw [Modexp.wordLimbsToNat_append, ← htotal, pow_add]
    ring
  rw [heq]
  simp only [Nat.add_mul_mod_self_left]

/-- Per-row truncated-product congruences compose over the exact q3 words selected by execution. -/
theorem truncatedRows_value_of_updates
    (q3 n r2 : UInt256) (kWords count total operandValue : Nat)
    (state : TruncatedOuterState)
    (hupdates : ∀ q, q < count →
      let current := truncatedRowsIterate q3 n r2 kWords q state
      let next := truncatedRowAdvance q3 n r2 kWords current
      let qi := q3Word current.memory current.activeWords q3 (UInt256.ofNat current.i)
      Modexp.wordLimbsToNat
          (memoryWordsFrom next.memory (r2.toNat + 32) total) % UInt256.size ^ total =
        (Modexp.wordLimbsToNat
            (memoryWordsFrom current.memory (r2.toNat + 32) total) +
          UInt256.size ^ q * (qi.toNat * operandValue)) % UInt256.size ^ total) :
    let final := truncatedRowsIterate q3 n r2 kWords count state
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) total) % UInt256.size ^ total =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (r2.toNat + 32) total) +
        Modexp.wordLimbsToNat (truncatedSourceWords q3 n r2 kWords count state) *
          operandValue) % UInt256.size ^ total := by
  induction count with
  | zero =>
      simp only [truncatedRowsIterate, truncatedSourceWords, Modexp.wordLimbsToNat,
        Nat.zero_mul, Nat.add_zero]
  | succ count ih =>
      let current := truncatedRowsIterate q3 n r2 kWords count state
      let qi := q3Word current.memory current.activeWords q3 (UInt256.ofNat current.i)
      have hprevious :
          Modexp.wordLimbsToNat
              (memoryWordsFrom current.memory (r2.toNat + 32) total) %
                UInt256.size ^ total =
            (Modexp.wordLimbsToNat
                (memoryWordsFrom state.memory (r2.toNat + 32) total) +
              Modexp.wordLimbsToNat
                  (truncatedSourceWords q3 n r2 kWords count state) * operandValue) %
                UInt256.size ^ total := by
        simpa only [current] using ih (by
          intro q hq
          exact hupdates q (by omega))
      have hstep := hupdates count (by omega)
      dsimp only
      rw [truncatedRowsIterate_succ_last, truncatedSourceWords_succ_last]
      rw [show q3Word current.memory current.activeWords q3 (UInt256.ofNat current.i) = qi
        by rfl]
      rw [Modexp.wordLimbsToNat_append, truncatedSourceWords_length]
      simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
      have hstep' :
          Modexp.wordLimbsToNat
              (memoryWordsFrom
                (truncatedRowAdvance q3 n r2 kWords current).memory
                (r2.toNat + 32) total) % UInt256.size ^ total =
            (Modexp.wordLimbsToNat
                (memoryWordsFrom current.memory (r2.toNat + 32) total) +
              UInt256.size ^ count * (qi.toNat * operandValue)) %
                UInt256.size ^ total := by
        simpa only [current, qi] using hstep
      rw [hstep']
      have hreplace :
          (Modexp.wordLimbsToNat
              (memoryWordsFrom current.memory (r2.toNat + 32) total) +
            UInt256.size ^ count * (qi.toNat * operandValue)) % UInt256.size ^ total =
          ((Modexp.wordLimbsToNat
                (memoryWordsFrom state.memory (r2.toNat + 32) total) +
              Modexp.wordLimbsToNat
                  (truncatedSourceWords q3 n r2 kWords count state) * operandValue) +
            UInt256.size ^ count * (qi.toNat * operandValue)) %
              UInt256.size ^ total := by
        calc
          (Modexp.wordLimbsToNat
                (memoryWordsFrom current.memory (r2.toNat + 32) total) +
              UInt256.size ^ count * (qi.toNat * operandValue)) %
                UInt256.size ^ total =
              (Modexp.wordLimbsToNat
                    (memoryWordsFrom current.memory (r2.toNat + 32) total) %
                    UInt256.size ^ total +
                (UInt256.size ^ count * (qi.toNat * operandValue)) %
                  UInt256.size ^ total) % UInt256.size ^ total := Nat.add_mod _ _ _
          _ = (((Modexp.wordLimbsToNat
                    (memoryWordsFrom state.memory (r2.toNat + 32) total) +
                  Modexp.wordLimbsToNat
                      (truncatedSourceWords q3 n r2 kWords count state) * operandValue) %
                    UInt256.size ^ total) +
                (UInt256.size ^ count * (qi.toNat * operandValue)) %
                  UInt256.size ^ total) % UInt256.size ^ total := by rw [hprevious]
          _ = ((Modexp.wordLimbsToNat
                    (memoryWordsFrom state.memory (r2.toNat + 32) total) +
                  Modexp.wordLimbsToNat
                      (truncatedSourceWords q3 n r2 kWords count state) * operandValue) +
                UInt256.size ^ count * (qi.toNat * operandValue)) %
                  UInt256.size ^ total := (Nat.add_mod _ _ _).symm
      rw [hreplace]
      congr 1
      ring

/-- A concrete inner recurrence that updates the suffix of a fixed result range performs one
truncated schoolbook row modulo the range radix. -/
theorem innerSuffix_value_mod
    (a bPtr resultPtr i : UInt256) (shift width total : Nat) (state : InnerState)
    (hcarry : state.carry = ⟨0⟩)
    (htotal : shift + width = total)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hbFits : ∀ q, q < width →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size)
    (hresultFits : ∀ q, q < width →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 3) < UInt256.size)
    (hgaps : ∀ q, q < width →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (hoperandAddress : (elementPtr bPtr state.j).toNat = bPtr.toNat + 32)
    (hresultAddress : (elementPtr resultPtr (i + state.j)).toNat =
      resultPtr.toNat + 32 + 32 * shift)
    (hoperandRange : (elementPtr bPtr state.j).toNat + 32 * width < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * width <
      UInt256.size)
    (hseparate : (elementPtr bPtr state.j).toNat + 32 * width ≤
      (elementPtr resultPtr (i + state.j)).toNat)
    (hbelow : ∀ q, q < width →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 + 32 * shift ≤
        (elementPtr resultPtr (i + current.j)).toNat) :
    let final := iterate a bPtr resultPtr i width state
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (resultPtr.toNat + 32) total) %
          UInt256.size ^ total =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (resultPtr.toNat + 32) total) +
        UInt256.size ^ shift *
          (a.toNat * Modexp.wordLimbsToNat
            (memoryWordsFrom state.memory (bPtr.toNat + 32) width))) %
        UInt256.size ^ total := by
  let final := iterate a bPtr resultPtr i width state
  let prefixWords := memoryWordsFrom state.memory (resultPtr.toNat + 32) shift
  let priorWords := memoryWordsFrom state.memory (resultPtr.toNat + 32 + 32 * shift) width
  let outputWords := memoryWordsFrom final.memory
    (resultPtr.toNat + 32 + 32 * shift) width
  let operandWords := memoryWordsFrom state.memory (bPtr.toNat + 32) width
  have hinputs := innerInputWords_eq_initialMemory_of_gap a bPtr resultPtr i width state
    hcovered hawFit hbase hbFits hresultFits hgaps hoperandRange hresultRange hseparate
  have hoperand : innerOperandWords a bPtr resultPtr i width state = operandWords := by
    simpa only [operandWords, hoperandAddress] using hinputs.1
  have hprior : innerPriorWords a bPtr resultPtr i width state = priorWords := by
    simpa only [priorWords, hresultAddress] using hinputs.2
  have houtput := innerOutputWords_eq_finalMemory_of_gap a bPtr resultPtr i width state
    (by
      intro q hq
      have h := hbFits q hq
      omega)
    (by
      intro q hq
      have h := hresultFits q hq
      omega)
    hresultRange hgaps
  have houtput' : innerOutputWords a bPtr resultPtr i width state = outputWords := by
    simpa only [outputWords, final, hresultAddress] using houtput
  have hrecompose := innerCollectors_recompose a bPtr resultPtr i width state
  rw [hoperand, hprior, houtput', hcarry] at hrecompose
  simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.add_zero] at hrecompose
  have hprefixFrame := iterate_memoryWords_below_of_gap a bPtr resultPtr i width state
    (resultPtr.toNat + 32) shift hbase hgaps hbelow
  have hbeforeSplit := memoryWordsFrom_split state.memory (resultPtr.toNat + 32) shift width
  have hafterSplit := memoryWordsFrom_split final.memory (resultPtr.toNat + 32) shift width
  have hbefore : memoryWordsFrom state.memory (resultPtr.toNat + 32) total =
      prefixWords ++ priorWords := by
    rw [← htotal]
    simpa only [prefixWords, priorWords, show resultPtr.toNat + 32 + 32 * shift =
      resultPtr.toNat + 32 + 32 * shift by rfl] using hbeforeSplit
  have hafter : memoryWordsFrom final.memory (resultPtr.toNat + 32) total =
      prefixWords ++ outputWords := by
    rw [← htotal]
    rw [hafterSplit]
    simpa only [prefixWords, outputWords, final] using congrArg
      (fun words => words ++ outputWords) hprefixFrame
  dsimp only
  rw [hbefore, hafter]
  exact windowUpdate_mod a operandWords prefixWords priorWords outputWords final.carry shift width
    total (by simp only [prefixWords, memoryWordsFrom_length]) htotal (by
      simpa only [final] using hrecompose)

/-- Every concrete later nonzero row updates the low `k+1` result limbs by its exact shifted
product, dropping only the carry beyond the truncation width. -/
theorem laterNonzeroRow_value_mod
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords : Nat)
    (hiPos : 0 < iWords) (hiLe : iWords ≤ kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered
      (truncatedInitialState mem aw q3 (UInt256.ofNat iWords)).memory
      (truncatedInitialState mem aw q3 (UInt256.ofNat iWords)).activeWords)
    (hawFit : (truncatedInitialState mem aw q3 (UInt256.ofNat iWords)).activeWords.toNat *
      32 < UInt256.size)
    (hbase : 32 ≤ mem.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hgaps : ∀ q, q < kWords + 1 - iWords →
      let initial := truncatedInitialState mem aw q3 (UInt256.ofNat iWords)
      let current := iterate (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2
        (UInt256.ofNat iWords) q initial
      (elementPtr r2 (UInt256.ofNat iWords + current.j)).toNat - current.memory.size <
        USize.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (laterNonzeroRowMemory mem aw q3 n r2 iWords kWords)
          (r2.toNat + 32) (kWords + 1)) % UInt256.size ^ (kWords + 1) =
      (Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) (kWords + 1)) +
        UInt256.size ^ iWords *
          ((q3Word mem aw q3 (UInt256.ofNat iWords)).toNat *
            Modexp.wordLimbsToNat
              (memoryWordsFrom mem (n.toNat + 32) (kWords + 1 - iWords)))) %
        UInt256.size ^ (kWords + 1) := by
  let i := UInt256.ofNat iWords
  let width := kWords + 1 - iWords
  let qi := q3Word mem aw q3 i
  let initial := truncatedInitialState mem aw q3 i
  have hiWord : iWords < UInt256.size :=
    lt_trans (by omega : iWords < 2 ^ 64) (by decide : 2 ^ 64 < UInt256.size)
  have hwidth : width ≤ kWords := by dsimp only [width]; omega
  have hjAt (q : Nat) (hq : q ≤ width) :
      (iterate qi n r2 i q initial).j.toNat = q := by
    have h := iterate_j_toNat qi n r2 i q initial (by
      simp only [initial, truncatedInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
        Nat.zero_add]
      exact lt_trans (by omega : q < 2 ^ 64) (by decide : 2 ^ 64 < UInt256.size))
    simpa only [initial, truncatedInitialState,
      show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add] using h
  have hiNat : i.toNat = iWords := by
    simpa only [i] using UInt256.toNat_ofNat_of_lt hiWord
  have hisum (q : Nat) (hq : q ≤ width) :
      (i + (iterate qi n r2 i q initial).j).toNat = iWords + q := by
    rw [uadd_toNat, hiNat, hjAt q hq, Nat.mod_eq_of_lt]
    exact lt_trans (by omega : iWords + q < 2 ^ 64)
      (by decide : 2 ^ 64 < UInt256.size)
  have hbFits : ∀ q, q < width →
      let current := iterate qi n r2 i q initial
      n.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
    intro q hq
    simpa only [hjAt q (by omega)] using (show n.toNat + 32 * (q + 3) < UInt256.size by
      omega)
  have hresultFits : ∀ q, q < width →
      let current := iterate qi n r2 i q initial
      r2.toNat + 32 * ((i + current.j).toNat + 3) < UInt256.size := by
    intro q hq
    simpa only [hisum q (by omega)] using
      (show r2.toNat + 32 * (iWords + q + 3) < UInt256.size by omega)
  have hoperandAddress : (elementPtr n initial.j).toNat = n.toNat + 32 := by
    have hjInitial : initial.j.toNat = 0 := by
      simp only [initial, truncatedInitialState]
      decide
    rw [elementPtr_toNat_of_fit n initial.j (by rw [hjInitial]; omega), hjInitial]
  have hresultAddress : (elementPtr r2 (i + initial.j)).toNat =
      r2.toNat + 32 + 32 * iWords := by
    have hisum0 := hisum 0 (by omega)
    have hisumInitial : (i + initial.j).toNat = iWords := by
      simpa only [iterate, Nat.add_zero] using hisum0
    rw [elementPtr_toNat_of_fit r2 (i + initial.j) (by rw [hisumInitial]; omega),
      hisumInitial]
    omega
  have hoperandRange : (elementPtr n initial.j).toNat + 32 * width < UInt256.size := by
    rw [hoperandAddress]
    omega
  have hresultRange : (elementPtr r2 (i + initial.j)).toNat + 32 * width <
      UInt256.size := by
    rw [hresultAddress]
    omega
  have hseparate : (elementPtr n initial.j).toNat + 32 * width ≤
      (elementPtr r2 (i + initial.j)).toNat := by
    rw [hoperandAddress, hresultAddress]
    omega
  have hbelow : ∀ q, q < width →
      let current := iterate qi n r2 i q initial
      r2.toNat + 32 + 32 * iWords ≤ (elementPtr r2 (i + current.j)).toNat := by
    intro q hq
    let current := iterate qi n r2 i q initial
    have hsum := hisum q (by omega)
    have haddress : (elementPtr r2 (i + current.j)).toNat =
        r2.toNat + 32 * (iWords + q + 1) := by
      rw [elementPtr_toNat_of_fit r2 (i + current.j) (by rw [hsum]; omega), hsum]
    dsimp only
    rw [haddress]
    omega
  have hrow := innerSuffix_value_mod qi n r2 i iWords width (kWords + 1) initial
    (by rfl) (by dsimp only [width]; omega) hcovered hawFit (by simpa only [initial,
      truncatedInitialState] using hbase) hbFits hresultFits (by
        simpa only [qi, i, initial, width] using hgaps) hoperandAddress hresultAddress
      hoperandRange hresultRange hseparate hbelow
  simpa only [laterNonzeroRowMemory, truncatedCompletedState, qi, i, width, initial,
    show iWords + (kWords + 1 - iWords) = kWords + 1 by omega] using hrow

/-- The concrete first nonzero row stores its final carry in limb `k`, so its full `k+1`-limb
value is the ordinary first schoolbook row rather than merely a congruence. -/
theorem firstNonzeroRow_value
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered
      (truncatedInitialState mem aw q3 ⟨0⟩).memory
      (truncatedInitialState mem aw q3 ⟨0⟩).activeWords)
    (hawFit : (truncatedInitialState mem aw q3 ⟨0⟩).activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ mem.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hgaps : ∀ q, q < kWords →
      let initial := truncatedInitialState mem aw q3 ⟨0⟩
      let current := iterate (q3Word mem aw q3 ⟨0⟩) n r2 ⟨0⟩ q initial
      (elementPtr r2 (⟨0⟩ + current.j)).toNat - current.memory.size < USize.size)
    (hcarryReadZero :
      let initial := truncatedInitialState mem aw q3 ⟨0⟩
      let final := iterate (q3Word mem aw q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
      Modexp.MultiLimbDivisionTrace.readWord final.memory final.activeWords
        (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)) = ⟨0⟩)
    (hcarryGap :
      let initial := truncatedInitialState mem aw q3 ⟨0⟩
      let final := iterate (q3Word mem aw q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
      (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat - final.memory.size < USize.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (firstNonzeroRowMemory mem aw q3 n r2 kWords)
          (r2.toNat + 32) (kWords + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
        (q3Word mem aw q3 ⟨0⟩).toNat *
          Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords) := by
  let qi := q3Word mem aw q3 ⟨0⟩
  let initial := truncatedInitialState mem aw q3 ⟨0⟩
  let final := iterate qi n r2 ⟨0⟩ kWords initial
  have hjAt (q : Nat) (hq : q ≤ kWords) :
      (iterate qi n r2 ⟨0⟩ q initial).j.toNat = q := by
    have h := iterate_j_toNat qi n r2 ⟨0⟩ q initial (by
      simp only [initial, truncatedInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
        Nat.zero_add]
      exact lt_trans (by omega : q < 2 ^ 64) (by decide : 2 ^ 64 < UInt256.size))
    simpa only [initial, truncatedInitialState,
      show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add] using h
  have hisum (q : Nat) (hq : q ≤ kWords) :
      ((⟨0⟩ : UInt256) + (iterate qi n r2 ⟨0⟩ q initial).j).toNat = q := by
    simpa only [u256_zero_add] using hjAt q hq
  have hbFits : ∀ q, q < kWords →
      let current := iterate qi n r2 ⟨0⟩ q initial
      n.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
    intro q hq
    simpa only [hjAt q (by omega)] using
      (show n.toNat + 32 * (q + 3) < UInt256.size by omega)
  have hresultFits : ∀ q, q < kWords →
      let current := iterate qi n r2 ⟨0⟩ q initial
      r2.toNat + 32 * (((⟨0⟩ : UInt256) + current.j).toNat + 3) <
        UInt256.size := by
    intro q hq
    simpa only [hisum q (by omega)] using
      (show r2.toNat + 32 * (q + 3) < UInt256.size by omega)
  have hoperandAddress : (elementPtr n initial.j).toNat = n.toNat + 32 := by
    have hjInitial : initial.j.toNat = 0 := by
      simp only [initial, truncatedInitialState]
      decide
    rw [elementPtr_toNat_of_fit n initial.j (by rw [hjInitial]; omega), hjInitial]
  have hresultAddress : (elementPtr r2 ((⟨0⟩ : UInt256) + initial.j)).toNat =
      r2.toNat + 32 := by
    have hsum : ((⟨0⟩ : UInt256) + initial.j).toNat = 0 := by
      simpa only [iterate, Nat.add_zero] using hisum 0 (by omega)
    rw [elementPtr_toNat_of_fit r2 ((⟨0⟩ : UInt256) + initial.j)
      (by rw [hsum]; omega), hsum]
  have hoperandRange : (elementPtr n initial.j).toNat + 32 * kWords < UInt256.size := by
    rw [hoperandAddress]
    omega
  have hresultRange : (elementPtr r2 ((⟨0⟩ : UInt256) + initial.j)).toNat +
      32 * kWords < UInt256.size := by
    rw [hresultAddress]
    omega
  have hseparate : (elementPtr n initial.j).toNat + 32 * kWords ≤
      (elementPtr r2 ((⟨0⟩ : UInt256) + initial.j)).toNat := by
    rw [hoperandAddress, hresultAddress]
    omega
  have hinputs := innerInputWords_eq_initialMemory_of_gap qi n r2 ⟨0⟩ kWords initial
    hcovered hawFit (by simpa only [initial, truncatedInitialState] using hbase) hbFits
    hresultFits (by simpa only [qi, initial] using hgaps) hoperandRange hresultRange hseparate
  let operandWords := memoryWordsFrom mem (n.toNat + 32) kWords
  let priorWords := memoryWordsFrom mem (r2.toNat + 32) kWords
  have hoperand : innerOperandWords qi n r2 ⟨0⟩ kWords initial = operandWords := by
    rw [hinputs.1, hoperandAddress]
    rfl
  have hprior : innerPriorWords qi n r2 ⟨0⟩ kWords initial = priorWords := by
    rw [hinputs.2, hresultAddress]
    rfl
  have houtput := innerOutputWords_eq_finalMemory_of_gap qi n r2 ⟨0⟩ kWords initial
    (by
      intro q hq
      have h := hbFits q hq
      omega)
    (by
      intro q hq
      have h := hresultFits q hq
      omega)
    hresultRange (by simpa only [qi, initial] using hgaps)
  have hcarryAddress : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat =
      r2.toNat + 32 + 32 * kWords := by
    unfold carryPtr
    have hkWord : kWords < UInt256.size :=
      lt_trans (by omega : kWords < 2 ^ 64) (by decide : 2 ^ 64 < UInt256.size)
    have hsum : ((⟨0⟩ : UInt256) + UInt256.ofNat kWords).toNat = kWords := by
      rw [u256_zero_add, UInt256.toNat_ofNat_of_lt hkWord]
    rw [elementPtr_toNat_of_fit r2 ((⟨0⟩ : UInt256) + UInt256.ofNat kWords)
      (by rw [hsum]; omega), hsum]
    omega
  have hfinalBase : 32 ≤ final.memory.size := by
    have hmono := iterate_memory_size_mono_of_gap qi n r2 ⟨0⟩ kWords initial
      (by simpa only [qi, initial] using hgaps)
    exact hbase.trans (by simpa only [final, initial, truncatedInitialState] using hmono)
  have hvalue := completeInnerRow_memory_value_of_gap qi n r2 ⟨0⟩ kWords initial
    operandWords priorWords (r2.toNat + 32) (by rfl)
    (by simp only [operandWords, memoryWordsFrom_length])
    (by simp only [priorWords, memoryWordsFrom_length]) hoperand hprior
    (by simpa only [final, hresultAddress] using houtput)
    hcarryAddress
    (by simpa only [qi, initial, final] using hcarryReadZero) hfinalBase
    (by simpa only [qi, initial, final] using hcarryGap)
  simpa only [firstNonzeroRowMemory, truncatedCompletedState, qi, initial, final,
    truncatedCarryMemory, carryMemory, truncatedCarryPtr, carryPtr,
    operandWords, priorWords, u256_zero_add] using hvalue

/-- The inner column index of a concrete truncated row is the ordinary natural column count. -/
theorem truncatedInner_j_toNat
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords count : Nat)
    (hcount : count < 2 ^ 64) :
    (iterate (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2
      (UInt256.ofNat iWords) count
      (truncatedInitialState mem aw q3 (UInt256.ofNat iWords))).j.toNat = count := by
  have h := iterate_j_toNat
    (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2 (UInt256.ofNat iWords) count
    (truncatedInitialState mem aw q3 (UInt256.ofNat iWords)) (by
      simp only [truncatedInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
        Nat.zero_add]
      exact hcount.trans (by decide : 2 ^ 64 < UInt256.size))
  simpa only [truncatedInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.zero_add] using h

/-- Every result address selected inside an in-range truncated row is the expected unwrapped
word-array payload address. -/
theorem truncatedInner_resultAddress
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords count : Nat)
    (hi : iWords ≤ kWords) (hcount : count ≤ kWords + 1 - iWords)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    let current := iterate (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2
      (UInt256.ofNat iWords) count
      (truncatedInitialState mem aw q3 (UInt256.ofNat iWords))
    (elementPtr r2 (UInt256.ofNat iWords + current.j)).toNat =
      r2.toNat + 32 * (iWords + count + 1) := by
  let current := iterate (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2
    (UInt256.ofNat iWords) count
    (truncatedInitialState mem aw q3 (UInt256.ofNat iWords))
  have hk64 : kWords + 1 < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
    omega
  have hi64 : iWords < 2 ^ 64 := by omega
  have hcount64 : count < 2 ^ 64 := by omega
  have hj : current.j.toNat = count := by
    simpa only [current] using
      truncatedInner_j_toNat mem aw q3 n r2 iWords count hcount64
  have hiNat : (UInt256.ofNat iWords).toNat = iWords :=
    UInt256.toNat_ofNat_of_lt (hi64.trans (by decide))
  have hsum : (UInt256.ofNat iWords + current.j).toNat = iWords + count := by
    rw [uadd_toNat, hiNat, hj, Nat.mod_eq_of_lt]
    exact (show iWords + count < 2 ^ 64 by omega).trans (by decide)
  have hfit : r2.toNat + 32 * (iWords + count + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
    exact (show r2.toNat + 32 * (iWords + count + 1) < 2 ^ 64 by omega).trans (by decide)
  dsimp only
  rw [elementPtr_toNat_of_fit r2 (UInt256.ofNat iWords + current.j) (by
    rw [hsum]
    exact hfit), hsum]

/-- The concrete 64-bit allocation bound discharges every bounded-gap destination premise in a
truncated row, independently of how many preceding zero rows left the payload implicit. -/
theorem truncatedInner_gaps
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords width : Nat)
    (hi : iWords ≤ kWords) (hwidth : width ≤ kWords + 1 - iWords)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    ∀ count, count < width →
      let current := iterate (q3Word mem aw q3 (UInt256.ofNat iWords)) n r2
        (UInt256.ofNat iWords) count
        (truncatedInitialState mem aw q3 (UInt256.ofNat iWords))
      (elementPtr r2 (UInt256.ofNat iWords + current.j)).toNat - current.memory.size <
        USize.size := by
  intro count hcount
  have haddress := truncatedInner_resultAddress mem aw q3 n r2 iWords kWords count hi
    (by omega) hr2Bound
  dsimp only at haddress ⊢
  rw [haddress, show USize.size = 2 ^ 64 by native_decide]
  apply lt_of_le_of_lt (Nat.sub_le _ _)
  unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
  omega

/-- Inner stores cannot grow concrete memory past a bound that contains every selected result
word.  This is the upper-bound counterpart to `iterate_memory_size_mono_of_gap`. -/
theorem truncatedInner_memory_size_le
    (a bPtr resultPtr i : UInt256) (count bound : Nat) (state : InnerState)
    (hsize : state.memory.size ≤ bound)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (haddresses : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ bound) :
    (iterate a bPtr resultPtr i count state).memory.size ≤ bound := by
  induction count generalizing state with
  | zero => exact hsize
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hfirstAddress : dest + 32 ≤ bound := by
        simpa only [dest, iterate] using haddresses 0 (by omega)
      have hnextSize : next.memory.size = max state.memory.size (dest + 32) := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_size_eq_max _ _ _ hfirstGap
      have hnextLe : next.memory.size ≤ bound := by
        rw [hnextSize]
        exact max_le hsize hfirstAddress
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htailAddresses : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ bound := by
        intro q hq
        simpa only [next, iterate_advance] using haddresses (q + 1) (by omega)
      have htail := ih next hnextLe htailGaps htailAddresses
      simpa only [next, iterate] using htail

/-- A complete 32-byte word below every selected result destination is unchanged by an inner
truncated row, including stores that materialize an implicit-zero gap. -/
theorem truncatedInner_read32_below
    (a bPtr resultPtr i : UInt256) (count read : Nat) (state : InnerState)
    (hread : read + 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (hbelow : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      read + 32 ≤ (elementPtr resultPtr (i + current.j)).toNat) :
    (iterate a bPtr resultPtr i count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hfirstBelow : read + 32 ≤ dest := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hhead : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_read_below_of_gap _ _ _ _ hread hfirstBelow hfirstGap
      have hnextSize : next.memory.size = max state.memory.size (dest + 32) := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_size_eq_max _ _ _ hfirstGap
      have hnextRead : read + 32 ≤ next.memory.size := by
        rw [hnextSize]
        exact hread.trans (Nat.le_max_left _ _)
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          read + 32 ≤ (elementPtr resultPtr (i + current.j)).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next hnextRead htailGaps htailBelow
      simpa only [next, iterate] using htail.trans hhead

/-- One selected outer row preserves a complete 32-byte word below the `r2` payload. -/
theorem truncatedRowAdvance_read32_below
    (q3 n r2 : UInt256) (kWords read : Nat) (state : TruncatedOuterState)
    (hi : state.i ≤ kWords) (hread : read + 32 ≤ state.memory.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hbelow : read + 32 ≤ r2.toNat + 32) :
    (truncatedRowAdvance q3 n r2 kWords state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  rcases state with ⟨iWords, memory, activeWords⟩
  let i := UInt256.ofNat iWords
  let qi := q3Word memory activeWords q3 i
  by_cases hzero : qi = ⟨0⟩
  · simp only [truncatedRowAdvance, i, qi, hzero, if_pos]
  · by_cases hiZero : iWords = 0
    · subst iWords
      let initial := truncatedInitialState memory activeWords q3 ⟨0⟩
      let final := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
        kWords initial
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 0 kWords
        kWords (by omega) (by omega) hr2Bound
      have hdestinations : ∀ count, count < kWords →
          let current := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
            count initial
          read + 32 ≤ (elementPtr r2 (⟨0⟩ + current.j)).toNat := by
        intro count hcount
        have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
          0 kWords count (by omega) (by omega) hr2Bound
        have haddress' :
            (elementPtr r2
              ((⟨0⟩ : UInt256) +
                (iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
                  count initial).j)).toNat = r2.toNat + 32 * (count + 1) := by
          simpa only [initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
            Nat.zero_add] using haddress
        dsimp only
        rw [haddress']
        omega
      have hinner := truncatedInner_read32_below
        (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords read initial
        (by simpa only [initial, truncatedInitialState] using hread)
        (by simpa only [initial] using hgaps) hdestinations
      have hfinalRead : read + 32 ≤ final.memory.size := by
        have hmono := iterate_memory_size_mono_of_gap
          (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
          (by simpa only [initial] using hgaps)
        exact hread.trans (by simpa only [final, initial, truncatedInitialState] using hmono)
      have hcarryAddress : (truncatedCarryPtr r2 (UInt256.ofNat kWords)).toNat =
          r2.toNat + 32 * (kWords + 1) := by
        have hk64 : kWords < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show kWords < 2 ^ 64 by omega).trans (by decide)
        have hfit : r2.toNat + 32 * (kWords + 1) < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show r2.toNat + 32 * (kWords + 1) < 2 ^ 64 by omega).trans (by decide)
        unfold truncatedCarryPtr
        rw [elementPtr_toNat_of_fit r2 (UInt256.ofNat kWords) (by
          rw [UInt256.toNat_ofNat_of_lt hk64]
          exact hfit), UInt256.toNat_ofNat_of_lt hk64]
      have hcarryGap : (truncatedCarryPtr r2 (UInt256.ofNat kWords)).toNat -
          final.memory.size < USize.size := by
        rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
        apply lt_of_le_of_lt (Nat.sub_le _ _)
        unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
        omega
      have hcarry :
          (truncatedCarryMemory final.memory final.activeWords r2
            (UInt256.ofNat kWords) final.carry).readWithPadding read 32 =
              final.memory.readWithPadding read 32 := by
        unfold truncatedCarryMemory
        exact toByteArray_write_read_below_of_gap _ _ _ _ hfinalRead
          (by rw [hcarryAddress]; omega) hcarryGap
      simpa only [truncatedRowAdvance, i, qi, hzero, firstNonzeroRowMemory,
        truncatedCompletedState, initial, final] using hcarry.trans hinner
    · let width := kWords + 1 - iWords
      let initial := truncatedInitialState memory activeWords q3 i
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 iWords kWords
        width hi (by omega) hr2Bound
      have hdestinations : ∀ count, count < width →
          let current := iterate qi n r2 i count initial
          read + 32 ≤ (elementPtr r2 (i + current.j)).toNat := by
        intro count hcount
        have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
          iWords kWords count hi (by dsimp only [width] at hcount; omega) hr2Bound
        dsimp only at haddress ⊢
        rw [haddress]
        omega
      have hinner := truncatedInner_read32_below qi n r2 i width read initial
        (by simpa only [initial, truncatedInitialState] using hread)
        (by simpa only [qi, i, initial] using hgaps) hdestinations
      simpa only [truncatedRowAdvance, i, qi, hzero, hiZero, if_neg,
        laterNonzeroRowMemory, truncatedCompletedState, width, initial] using hinner

/-- One selected truncated row writes only inside the allocated `r2` payload. -/
theorem truncatedRowAdvance_memory_size_le
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState)
    (hi : state.i ≤ kWords)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hsize : state.memory.size ≤ r2.toNat + wordArrayAllocationSize (kWords + 1)) :
    (truncatedRowAdvance q3 n r2 kWords state).memory.size ≤
      r2.toNat + wordArrayAllocationSize (kWords + 1) := by
  rcases state with ⟨iWords, memory, activeWords⟩
  let i := UInt256.ofNat iWords
  let qi := q3Word memory activeWords q3 i
  by_cases hzero : qi = ⟨0⟩
  · simpa only [truncatedRowAdvance, i, qi, hzero, if_pos] using hsize
  · by_cases hiZero : iWords = 0
    · subst iWords
      let initial := truncatedInitialState memory activeWords q3 ⟨0⟩
      let final := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
        kWords initial
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 0 kWords
        kWords (by omega) (by omega) hr2Bound
      have haddresses : ∀ count, count < kWords →
          let current := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
            count initial
          (elementPtr r2 (⟨0⟩ + current.j)).toNat + 32 ≤
            r2.toNat + wordArrayAllocationSize (kWords + 1) := by
        intro count hcount
        have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
          0 kWords count (by omega) (by omega) hr2Bound
        have haddress' :
            (elementPtr r2
              ((⟨0⟩ : UInt256) +
                (iterate (q3Word memory activeWords q3 ⟨0⟩) n r2
                  ⟨0⟩ count initial).j)).toNat =
              r2.toNat + 32 * (count + 1) := by
          simpa only [initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
            Nat.zero_add] using haddress
        dsimp only
        rw [haddress']
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega
      have hfinalLe : final.memory.size ≤
          r2.toNat + wordArrayAllocationSize (kWords + 1) := by
        exact truncatedInner_memory_size_le
          (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords
          (r2.toNat + wordArrayAllocationSize (kWords + 1)) initial
          (by simpa only [initial, truncatedInitialState] using hsize)
          (by simpa only [initial] using hgaps) haddresses
      have hcarryAddress : (truncatedCarryPtr r2 (UInt256.ofNat kWords)).toNat =
          r2.toNat + 32 * (kWords + 1) := by
        have hk64 : kWords < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show kWords < 2 ^ 64 by omega).trans (by decide)
        have hfit : r2.toNat + 32 * (kWords + 1) < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show r2.toNat + 32 * (kWords + 1) < 2 ^ 64 by omega).trans (by decide)
        unfold truncatedCarryPtr
        rw [elementPtr_toNat_of_fit r2 (UInt256.ofNat kWords) (by
          rw [UInt256.toNat_ofNat_of_lt hk64]
          exact hfit), UInt256.toNat_ofNat_of_lt hk64]
      have hcarryGap : (truncatedCarryPtr r2 (UInt256.ofNat kWords)).toNat -
          final.memory.size < USize.size := by
        rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
        apply lt_of_le_of_lt (Nat.sub_le _ _)
        unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
        omega
      have hcarrySize :
          (truncatedCarryMemory final.memory final.activeWords r2
            (UInt256.ofNat kWords) final.carry).size =
            max final.memory.size
              ((truncatedCarryPtr r2 (UInt256.ofNat kWords)).toNat + 32) := by
        unfold truncatedCarryMemory
        exact toByteArray_write_size_eq_max _ _ _ hcarryGap
      have hcarryLe :
          (truncatedCarryMemory final.memory final.activeWords r2
            (UInt256.ofNat kWords) final.carry).size ≤
            r2.toNat + wordArrayAllocationSize (kWords + 1) := by
        rw [hcarrySize, hcarryAddress]
        apply max_le hfinalLe
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega
      simpa only [truncatedRowAdvance, i, qi, hzero, firstNonzeroRowMemory,
        truncatedCompletedState, initial, final] using hcarryLe
    · let width := kWords + 1 - iWords
      let initial := truncatedInitialState memory activeWords q3 i
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 iWords kWords
        width hi (by omega) hr2Bound
      have haddresses : ∀ count, count < width →
          let current := iterate qi n r2 i count initial
          (elementPtr r2 (i + current.j)).toNat + 32 ≤
            r2.toNat + wordArrayAllocationSize (kWords + 1) := by
        intro count hcount
        have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
          iWords kWords count hi (by dsimp only [width] at hcount; omega) hr2Bound
        dsimp only at haddress ⊢
        rw [haddress]
        unfold wordArrayAllocationSize wordArrayPayloadSize
        dsimp only [width] at hcount
        omega
      have hfinalLe := truncatedInner_memory_size_le qi n r2 i width
        (r2.toNat + wordArrayAllocationSize (kWords + 1)) initial
        (by simpa only [initial, truncatedInitialState] using hsize)
        (by simpa only [qi, i, initial] using hgaps) haddresses
      simpa only [truncatedRowAdvance, i, qi, hzero, hiZero, if_neg,
        laterNonzeroRowMemory, truncatedCompletedState, width, initial] using hfinalLe

/-- Every selected outer prefix remains inside the concrete `r2` allocation. -/
theorem truncatedRows_memory_size_le
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState)
    (hindices : ∀ q, q < count →
      (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hsize : state.memory.size ≤ r2.toNat + wordArrayAllocationSize (kWords + 1)) :
    (truncatedRowsIterate q3 n r2 kWords count state).memory.size ≤
      r2.toNat + wordArrayAllocationSize (kWords + 1) := by
  induction count generalizing state with
  | zero => exact hsize
  | succ count ih =>
      let next := truncatedRowAdvance q3 n r2 kWords state
      have hhead := truncatedRowAdvance_memory_size_le q3 n r2 kWords state
        (by simpa only [truncatedRowsIterate] using hindices 0 (by omega)) hr2Bound hsize
      have hindices' : ∀ q, q < count →
          (truncatedRowsIterate q3 n r2 kWords q next).i ≤ kWords := by
        intro q hq
        simpa only [next, truncatedRowsIterate_advance] using hindices (q + 1) (by omega)
      have htail := ih next hindices' hhead
      simpa only [next, truncatedRowsIterate] using htail

/-- A complete selected truncated row preserves every padded word range ending at or below the
result header.  All row stores begin in the `r2` payload. -/
theorem truncatedRowAdvance_memoryWords_below
    (q3 n r2 : UInt256) (kWords ptr words : Nat) (state : TruncatedOuterState)
    (hi : state.i ≤ kWords) (hbase : 32 ≤ state.memory.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hbelow : ptr + 32 * words ≤ r2.toNat + 32) :
    memoryWordsFrom (truncatedRowAdvance q3 n r2 kWords state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  rcases state with ⟨iWords, memory, activeWords⟩
  let i := UInt256.ofNat iWords
  let qi := q3Word memory activeWords q3 i
  by_cases hzero : qi = ⟨0⟩
  · simp only [truncatedRowAdvance, i, qi, hzero, if_pos]
  · by_cases hiZero : iWords = 0
    · subst iWords
      let initial := truncatedInitialState memory activeWords q3 ⟨0⟩
      let final := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
        kWords initial
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 0 kWords
        kWords (by omega) (by omega) hr2Bound
      have hinner := iterate_memoryWords_below_of_gap
        (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
        ptr words (by simpa only [initial, truncatedInitialState] using hbase)
        (by simpa only [initial] using hgaps) (by
          intro count hcount
          have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
            0 kWords count (by omega) (by omega) hr2Bound
          have haddress' :
              (elementPtr r2
                ((⟨0⟩ : UInt256) +
                  (iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ count
                    initial).j)).toNat = r2.toNat + 32 * (count + 1) := by
            simpa only [initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
              Nat.zero_add] using haddress
          dsimp only
          rw [haddress']
          omega)
      have hfinalBase : 32 ≤ final.memory.size := by
        have hmono := iterate_memory_size_mono_of_gap
          (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
          (by simpa only [initial] using hgaps)
        exact hbase.trans (by simpa only [final, initial, truncatedInitialState] using hmono)
      have hcarryAddress : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat =
          r2.toNat + 32 * (kWords + 1) := by
        have hk64 : kWords < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show kWords < 2 ^ 64 by omega).trans (by decide)
        have hfit : r2.toNat + 32 * (kWords + 1) < UInt256.size := by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
          exact (show r2.toNat + 32 * (kWords + 1) < 2 ^ 64 by omega).trans (by decide)
        unfold carryPtr
        rw [u256_zero_add, elementPtr_toNat_of_fit r2 (UInt256.ofNat kWords) (by
          rw [UInt256.toNat_ofNat_of_lt hk64]
          exact hfit), UInt256.toNat_ofNat_of_lt hk64]
      have hcarryGap : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat -
          final.memory.size < USize.size := by
        rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
        apply lt_of_le_of_lt (Nat.sub_le _ _)
        unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
        omega
      have hcarry := carryMemory_words_below_of_gap final.memory final.activeWords r2 ⟨0⟩
        (UInt256.ofNat kWords) final.carry ptr words hfinalBase hcarryGap (by
          rw [hcarryAddress]
          omega)
      simpa [truncatedRowAdvance, i, qi, hzero, firstNonzeroRowMemory,
        truncatedCompletedState, initial, final, truncatedCarryMemory,
        truncatedCarryPtr, carryMemory, carryPtr, truncatedInitialState,
        u256_zero_add] using hcarry.trans hinner
    · have hiPos : 0 < iWords := Nat.pos_of_ne_zero hiZero
      let width := kWords + 1 - iWords
      let initial := truncatedInitialState memory activeWords q3 i
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 iWords kWords
        width hi (by omega) hr2Bound
      have hinner := iterate_memoryWords_below_of_gap qi n r2 i width initial ptr words
        (by simpa only [initial, truncatedInitialState] using hbase)
        (by simpa only [qi, i, initial] using hgaps) (by
          intro count hcount
          have haddress := truncatedInner_resultAddress memory activeWords q3 n r2
            iWords kWords count hi (by dsimp only [width] at hcount; omega) hr2Bound
          dsimp only at haddress ⊢
          rw [haddress]
          omega)
      simpa only [truncatedRowAdvance, i, qi, hzero, hiZero, if_neg,
        laterNonzeroRowMemory, truncatedCompletedState, width, initial] using hinner

/-- Any outer prefix preserves complete q3/modulus ranges below `r2`, including prefixes that
skip arbitrary zero q3 limbs. -/
theorem truncatedRows_memoryWords_below
    (q3 n r2 : UInt256) (kWords count ptr words : Nat) (state : TruncatedOuterState)
    (hindices : ∀ q, q < count →
      (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords)
    (hbases : ∀ q, q < count →
      32 ≤ (truncatedRowsIterate q3 n r2 kWords q state).memory.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hbelow : ptr + 32 * words ≤ r2.toNat + 32) :
    memoryWordsFrom
        (truncatedRowsIterate q3 n r2 kWords count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := truncatedRowAdvance q3 n r2 kWords state
      have hhead := truncatedRowAdvance_memoryWords_below q3 n r2 kWords ptr words state
        (by simpa only [truncatedRowsIterate] using hindices 0 (by omega))
        (by simpa only [truncatedRowsIterate] using hbases 0 (by omega)) hr2Bound hbelow
      have hindices' : ∀ q, q < count →
          (truncatedRowsIterate q3 n r2 kWords q next).i ≤ kWords := by
        intro q hq
        simpa only [next, truncatedRowsIterate_advance] using hindices (q + 1) (by omega)
      have hbases' : ∀ q, q < count →
          32 ≤ (truncatedRowsIterate q3 n r2 kWords q next).memory.size := by
        intro q hq
        simpa only [next, truncatedRowsIterate_advance] using hbases (q + 1) (by omega)
      have htail := ih next hindices' hbases'
      simpa only [next, truncatedRowsIterate] using htail.trans hhead

/-- One selected truncated row preserves covered, representable memory and grows the concrete
byte array monotonically. -/
theorem truncatedRowAdvance_coverage
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState)
    (hi : state.i ≤ kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    MemoryCovered (truncatedRowAdvance q3 n r2 kWords state).memory
        (truncatedRowAdvance q3 n r2 kWords state).activeWords ∧
      (truncatedRowAdvance q3 n r2 kWords state).activeWords.toNat * 32 <
        UInt256.size ∧
      state.memory.size ≤ (truncatedRowAdvance q3 n r2 kWords state).memory.size := by
  rcases state with ⟨iWords, memory, activeWords⟩
  change iWords ≤ kWords at hi
  change MemoryCovered memory activeWords at hcovered
  change activeWords.toNat * 32 < UInt256.size at hawFit
  let i := UInt256.ofNat iWords
  let qi := q3Word memory activeWords q3 i
  have hi64 : iWords < UInt256.size :=
    (show iWords < 2 ^ 64 by omega).trans (by decide)
  have hiNat : i.toNat = iWords := by
    simpa only [i] using UInt256.toNat_ofNat_of_lt hi64
  have hq3Address : (q3ElementPtr q3 i).toNat = q3.toNat + 32 * (iWords + 1) := by
    unfold q3ElementPtr
    rw [elementPtr_toNat_of_fit q3 i (by rw [hiNat]; omega), hiNat]
  have hq3Read := readWords1_coverage memory activeWords (q3ElementPtr q3 i)
    hcovered hawFit (by rw [hq3Address]; omega)
  have hinitialCovered : MemoryCovered
      (truncatedInitialState memory activeWords q3 i).memory
      (truncatedInitialState memory activeWords q3 i).activeWords := by
    simpa only [truncatedInitialState, q3Words, afterLoad] using hq3Read.1
  have hinitialFit :
      (truncatedInitialState memory activeWords q3 i).activeWords.toNat * 32 <
        UInt256.size := by
    simpa only [truncatedInitialState, q3Words, afterLoad] using hq3Read.2
  by_cases hzero : qi = ⟨0⟩
  · simpa only [truncatedRowAdvance, i, qi, hzero, if_pos] using
      And.intro hq3Read.1 (And.intro hq3Read.2 (Nat.le_refl memory.size))
  · by_cases hiZero : iWords = 0
    · have hiWordZero : i = (⟨0⟩ : UInt256) := by
        apply u256_inj
        simp only [i, hiZero, UInt256.toNat_ofNat_of_lt (by decide : 0 < UInt256.size)]
        decide
      have hzero0 : q3Word memory activeWords q3 (UInt256.ofNat 0) ≠ ⟨0⟩ := by
        simpa only [qi, i, hiZero] using hzero
      let initial := truncatedInitialState memory activeWords q3 ⟨0⟩
      let final := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
        kWords initial
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 0 kWords kWords
        (by omega) (by omega) hr2Bound
      have hsteps : ∀ count, count < kWords →
          let current := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
            count initial
          (elementPtr n current.j).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr r2 (⟨0⟩ + current.j)).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr r2 (⟨0⟩ + current.j)).toNat - current.memory.size <
              USize.size := by
        intro count hcount
        let current := iterate (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩
          count initial
        have hj : current.j.toNat = count := by
          simpa only [current, initial] using
            truncatedInner_j_toNat memory activeWords q3 n r2 0 count (by omega)
        have hnAddress : (elementPtr n current.j).toNat =
            n.toNat + 32 * (count + 1) := by
          rw [elementPtr_toNat_of_fit n current.j (by rw [hj]; omega), hj]
        have hr2Address := truncatedInner_resultAddress memory activeWords q3 n r2
          0 kWords count (by omega) (by omega) hr2Bound
        have hr2Address' : (elementPtr r2 (⟨0⟩ + current.j)).toNat =
            r2.toNat + 32 * (count + 1) := by
          simpa only [current, initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
            Nat.zero_add] using hr2Address
        refine ⟨?_, ?_, ?_⟩
        · rw [hnAddress]
          omega
        · rw [hr2Address']
          omega
        · simpa only [current, initial] using hgaps count hcount
      have hiter := iterate_coverage_of_gap
        (q3Word memory activeWords q3 ⟨0⟩) n r2 ⟨0⟩ kWords initial
        (by simpa only [initial, hiWordZero] using hinitialCovered)
        (by simpa only [initial, hiWordZero] using hinitialFit)
        hsteps
      have hcarryAddress : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat =
          r2.toNat + 32 * (kWords + 1) := by
        have hkWord : kWords < UInt256.size :=
          (show kWords < 2 ^ 64 by omega).trans (by decide)
        unfold carryPtr
        rw [u256_zero_add, elementPtr_toNat_of_fit r2 (UInt256.ofNat kWords) (by
          rw [UInt256.toNat_ofNat_of_lt hkWord]
          omega), UInt256.toNat_ofNat_of_lt hkWord]
      have hcarryGap : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat -
          final.memory.size < USize.size := by
        rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
        apply lt_of_le_of_lt (Nat.sub_le _ _)
        unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
        omega
      have hcarry := carryMemory_coverage_of_gap final.memory final.activeWords r2 ⟨0⟩
        (UInt256.ofNat kWords) final.carry (by rw [hcarryAddress]; omega) hcarryGap
        (by simpa only [final] using hiter.1)
        (by simpa only [final] using hiter.2.1)
      have hmono : memory.size ≤
          (carryMemory final.memory final.activeWords r2 ⟨0⟩
            (UInt256.ofNat kWords) final.carry).size := by
        exact (by
          have hinitial : memory.size = initial.memory.size := rfl
          rw [hinitial]
          exact hiter.2.2.trans (by rw [hcarry.2.2]; exact Nat.le_max_left _ _))
      simpa [truncatedRowAdvance, i, qi, hzero, firstNonzeroRowMemory,
        firstNonzeroRowWords, truncatedCompletedState, initial, final,
        truncatedCarryMemory, truncatedCarryWords, truncatedCarryPtr,
        carryMemory, carryWords, carryPtr, truncatedInitialState,
        u256_zero_add, hiZero, hzero0] using
          And.intro hcarry.1 (And.intro hcarry.2.1 hmono)
    · have hiPos : 0 < iWords := Nat.pos_of_ne_zero hiZero
      let width := kWords + 1 - iWords
      let initial := truncatedInitialState memory activeWords q3 i
      let final := iterate qi n r2 i width initial
      have hgaps := truncatedInner_gaps memory activeWords q3 n r2 iWords kWords width
        hi (by omega) hr2Bound
      have hsteps : ∀ count, count < width →
          let current := iterate qi n r2 i count initial
          (elementPtr n current.j).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr r2 (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr r2 (i + current.j)).toNat - current.memory.size < USize.size := by
        intro count hcount
        let current := iterate qi n r2 i count initial
        have hj : current.j.toNat = count := by
          simpa only [current, qi, i, initial] using
            truncatedInner_j_toNat memory activeWords q3 n r2 iWords count (by omega)
        have hnAddress : (elementPtr n current.j).toNat =
            n.toNat + 32 * (count + 1) := by
          rw [elementPtr_toNat_of_fit n current.j (by rw [hj]; omega), hj]
        have hr2Address := truncatedInner_resultAddress memory activeWords q3 n r2
          iWords kWords count hi (by dsimp only [width] at hcount; omega) hr2Bound
        have hr2Address' : (elementPtr r2 (i + current.j)).toNat =
            r2.toNat + 32 * (iWords + count + 1) := by
          simpa only [current, qi, i, initial] using hr2Address
        refine ⟨?_, ?_, ?_⟩
        · rw [hnAddress]
          dsimp only [width] at hcount
          omega
        · rw [hr2Address']
          omega
        · simpa only [current, qi, i, initial] using hgaps count hcount
      have hiter := iterate_coverage_of_gap qi n r2 i width initial
        (by simpa only [initial] using hinitialCovered)
        (by simpa only [initial] using hinitialFit) hsteps
      simpa only [truncatedRowAdvance, i, qi, hzero, hiZero, if_neg,
        laterNonzeroRowMemory, laterNonzeroRowWords, truncatedCompletedState,
        width, initial, final] using hiter

/-- Covered memory, representable active words, and monotone concrete memory size propagate over
every selected truncated outer prefix. -/
theorem truncatedRows_coverage
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState)
    (hk : kWords ≤ 32)
    (hindices : ∀ q, q < count →
      (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    let final := truncatedRowsIterate q3 n r2 kWords count state
    MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size ∧
      state.memory.size ≤ final.memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, le_rfl⟩
  | succ count ih =>
      let next := truncatedRowAdvance q3 n r2 kWords state
      have hhead := truncatedRowAdvance_coverage q3 n r2 kWords state
        (by simpa only [truncatedRowsIterate] using hindices 0 (by omega)) hk
        hcovered hawFit hq3Fit hnFit hr2Fit hr2Bound
      have hindices' : ∀ q, q < count →
          (truncatedRowsIterate q3 n r2 kWords q next).i ≤ kWords := by
        intro q hq
        simpa only [next, truncatedRowsIterate_advance] using hindices (q + 1) (by omega)
      have htail := ih next hindices' hhead.1 hhead.2.1
      simpa only [next, truncatedRowsIterate] using
        And.intro htail.1 (And.intro htail.2.1 (hhead.2.2.trans htail.2.2))

/-- Every selected outer prefix preserves a complete 32-byte word below the `r2` payload. -/
theorem truncatedRows_read32_below
    (q3 n r2 : UInt256) (kWords count read : Nat) (state : TruncatedOuterState)
    (hk : kWords ≤ 32)
    (hindices : ∀ q, q < count →
      (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords)
    (hread : read + 32 ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hbelow : read + 32 ≤ r2.toNat + 32) :
    (truncatedRowsIterate q3 n r2 kWords count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := truncatedRowAdvance q3 n r2 kWords state
      have hi : state.i ≤ kWords := by
        simpa only [truncatedRowsIterate] using hindices 0 (by omega)
      have hhead := truncatedRowAdvance_read32_below q3 n r2 kWords read state
        hi hread hr2Bound hbelow
      have hgeometry := truncatedRowAdvance_coverage q3 n r2 kWords state hi hk
        hcovered hawFit hq3Fit hnFit hr2Fit hr2Bound
      have hindices' : ∀ q, q < count →
          (truncatedRowsIterate q3 n r2 kWords q next).i ≤ kWords := by
        intro q hq
        simpa only [next, truncatedRowsIterate_advance] using hindices (q + 1) (by omega)
      have htail := ih next hindices'
        (hread.trans (by simpa only [next] using hgeometry.2.2))
        (by simpa only [next] using hgeometry.1)
        (by simpa only [next] using hgeometry.2.1)
      simpa only [next, truncatedRowsIterate] using htail.trans hhead

/-- The concrete `r2` allocation retains only its length header; its payload is initially
implicit zero memory. -/
theorem r2AllocatedMemory_size
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (r2AllocatedMemory mem fp kWords).size = fp + 32 := by
  unfold r2AllocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- Padded reads expose the allocator's complete logical `k+1`-word payload as zero. -/
theorem r2AllocatedMemory_payload_zero
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    memoryWordsFrom (r2AllocatedMemory mem fp kWords) (fp + 32) (kWords + 1) =
      List.replicate (kWords + 1) (⟨0⟩ : UInt256) := by
  apply memoryWordsFrom_past_end_zero
  rw [r2AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap]

/-- The exact `r2` allocator establishes covered, representable memory at the truncated outer
entry. -/
theorem r2AllocatedMemory_coverage
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    MemoryCovered (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords) ∧
      (r2AllocatedWords aw fp kWords).toNat * 32 < UInt256.size := by
  simpa only [r2AllocatedMemory, r2AllocatedWords] using
    allocatedWordArray_coverage mem aw fp (kWords + 1) hcovered hawFit hmemSize hmemLe
      hgap hbound

/-- The allocated `r2` pointer has its ordinary natural value. -/
theorem r2AllocatedPtr_toNat
    (fp kWords : Nat)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64) :
    (UInt256.ofNat fp).toNat = fp := by
  exact functionResultPtr_toNat fp (kWords + 1) hbound

/-- A complete prior word range at or above Solidity's reserved memory is unchanged by the
following `r2` allocation. -/
theorem r2AllocatedMemory_words_below
    (mem : ByteArray) (fp kWords ptr count : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptr : 96 ≤ ptr) (hbelow : ptr + 32 * count ≤ fp) :
    memoryWordsFrom (r2AllocatedMemory mem fp kWords) ptr count =
      memoryWordsFrom mem ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hhead :=
        Modexp.MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
          mem fp (kWords + 1) ptr hmemSize hgap hptr (by omega)
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (r2AllocatedMemory mem fp kWords) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr := by
        unfold r2AllocatedMemory Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hhead]
      simp only [memoryWordsFrom]
      rw [hword, ih (ptr := ptr + 32) (by omega) (by omega)]

/-- Starting from `i=0`, the selected q3 collector is exactly the immutable copied q3 payload. -/
theorem truncatedSourceWords_eq_q3Payload
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState)
    (hstateIndex : state.i = 0) (hcount : count ≤ kWords + 1) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ r2.toNat + 32) :
    truncatedSourceWords q3 n r2 kWords count state =
      memoryWordsFrom state.memory (q3.toNat + 32) count := by
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q state).i = q := by
    rw [truncatedRowsIterate_i, hstateIndex, Nat.zero_add]
  have hindices (limit : Nat) (hlimit : limit ≤ kWords + 1) :
      ∀ q, q < limit →
        (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hcoverage (q : Nat) (hq : q ≤ kWords + 1) :=
    truncatedRows_coverage q3 n r2 kWords q state hk (hindices q hq)
      hcovered hawFit hq3Fit hnFit hr2Fit hr2Bound
  have hbases (limit : Nat) (hlimit : limit ≤ kWords + 1) :
      ∀ q, q < limit →
        32 ≤ (truncatedRowsIterate q3 n r2 kWords q state).memory.size := by
    intro q hq
    have hmono := (hcoverage q (by omega)).2.2
    exact hbase.trans hmono
  induction count with
  | zero => rfl
  | succ count ih =>
      have hcount' : count ≤ kWords := by omega
      let current := truncatedRowsIterate q3 n r2 kWords count state
      have hcurrentCoverage := hcoverage count (by omega)
      have hiNat : (UInt256.ofNat current.i).toNat = count := by
        rw [hindex count]
        exact UInt256.toNat_ofNat_of_lt
          ((show count < 2 ^ 64 by omega).trans (by decide))
      have hq3Address : (q3ElementPtr q3 (UInt256.ofNat current.i)).toNat =
          q3.toNat + 32 * (count + 1) := by
        unfold q3ElementPtr
        rw [elementPtr_toNat_of_fit q3 (UInt256.ofNat current.i) (by
          rw [hiNat]
          omega), hiNat]
      have hframe := truncatedRows_memoryWords_below q3 n r2 kWords count
        (q3.toNat + 32 * (count + 1)) 1 state (hindices count (by omega))
        (hbases count (by omega)) hr2Bound (by omega)
      have hwordFrame : Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
            (q3.toNat + 32 * (count + 1)) =
          Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
            (q3.toNat + 32 * (count + 1)) := by
        exact memoryWordNat_eq_of_memoryWordsFrom_one_eq current.memory state.memory
          (q3.toNat + 32 * (count + 1)) (by simpa only [current] using hframe)
      have hread := readWord_eq_memoryWordOf_covered_padded current.memory current.activeWords
        (q3ElementPtr q3 (UInt256.ofNat current.i))
        (by simpa only [current] using hcurrentCoverage.1)
        (by simpa only [current] using hcurrentCoverage.2.1)
      have hselected : q3Word current.memory current.activeWords q3
            (UInt256.ofNat current.i) =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
            (q3.toNat + 32 * count + 32)) := by
        unfold q3Word
        rw [hread, hq3Address, hwordFrame]
        congr 2
      rw [truncatedSourceWords_succ_last]
      rw [show truncatedSourceWords q3 n r2 kWords count state =
          memoryWordsFrom state.memory (q3.toNat + 32) count by exact ih (by omega)]
      rw [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
      simp only [current, hselected]
      rw [show q3.toNat + 32 * count + 32 = q3.toNat + 32 + 32 * count by omega]

/-- For the allocator's header-only initial payload, the first nonzero row derives its fresh
top-word zero read and therefore has the exact ordinary row value. -/
theorem firstNonzeroRow_value_of_zero_top
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ mem.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (htopInitial : Modexp.MultiLimbMemoryModel.memoryWordNat mem
      (r2.toNat + 32 * (kWords + 1)) = 0) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (firstNonzeroRowMemory mem aw q3 n r2 kWords)
          (r2.toNat + 32) (kWords + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
        (q3Word mem aw q3 ⟨0⟩).toNat *
          Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords) := by
  let qi := q3Word mem aw q3 ⟨0⟩
  let initial := truncatedInitialState mem aw q3 ⟨0⟩
  let final := iterate qi n r2 ⟨0⟩ kWords initial
  have hq3Address : (q3ElementPtr q3 ⟨0⟩).toNat = q3.toNat + 32 := by
    unfold q3ElementPtr
    rw [elementPtr_toNat_of_fit q3 ⟨0⟩ (by
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega), show (⟨0⟩ : UInt256).toNat = 0 by decide]
  have hq3Read := readWords1_coverage mem aw (q3ElementPtr q3 ⟨0⟩) hcovered hawFit
    (by rw [hq3Address]; omega)
  have hinitialCovered : MemoryCovered initial.memory initial.activeWords := by
    simpa only [initial, truncatedInitialState, q3Words, afterLoad] using hq3Read.1
  have hinitialFit : initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, truncatedInitialState, q3Words, afterLoad] using hq3Read.2
  have hgaps := truncatedInner_gaps mem aw q3 n r2 0 kWords kWords
    (by omega) (by omega) hr2Bound
  have hsteps : ∀ count, count < kWords →
      let current := iterate qi n r2 ⟨0⟩ count initial
      (elementPtr n current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr r2 (⟨0⟩ + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr r2 (⟨0⟩ + current.j)).toNat - current.memory.size <
          USize.size := by
    intro count hcount
    let current := iterate qi n r2 ⟨0⟩ count initial
    have hj : current.j.toNat = count := by
      simpa only [current, qi, initial] using
        truncatedInner_j_toNat mem aw q3 n r2 0 count (by omega)
    have hnAddress : (elementPtr n current.j).toNat = n.toNat + 32 * (count + 1) := by
      rw [elementPtr_toNat_of_fit n current.j (by rw [hj]; omega), hj]
    have hr2Address := truncatedInner_resultAddress mem aw q3 n r2 0 kWords count
      (by omega) (by omega) hr2Bound
    have hr2Address' : (elementPtr r2 (⟨0⟩ + current.j)).toNat =
        r2.toNat + 32 * (count + 1) := by
      simpa only [current, qi, initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
        Nat.zero_add] using hr2Address
    refine ⟨?_, ?_, ?_⟩
    · rw [hnAddress]
      omega
    · rw [hr2Address']
      omega
    · simpa only [current, qi, initial] using hgaps count hcount
  have hiter := iterate_coverage_of_gap qi n r2 ⟨0⟩ kWords initial
    hinitialCovered hinitialFit hsteps
  have hcarryAddress : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat =
      r2.toNat + 32 * (kWords + 1) := by
    have hkWord : kWords < UInt256.size :=
      (show kWords < 2 ^ 64 by omega).trans (by decide)
    unfold carryPtr
    rw [u256_zero_add, elementPtr_toNat_of_fit r2 (UInt256.ofNat kWords) (by
      rw [UInt256.toNat_ofNat_of_lt hkWord]
      omega), UInt256.toNat_ofNat_of_lt hkWord]
  have htopFrame := iterate_memoryWords_above_of_gap qi n r2 ⟨0⟩ kWords initial
    (r2.toNat + 32 * (kWords + 1)) 1 (by simpa only [qi, initial] using hgaps) (by
      intro count hcount
      have haddress := truncatedInner_resultAddress mem aw q3 n r2 0 kWords count
        (by omega) (by omega) hr2Bound
      dsimp only at haddress ⊢
      have haddress' :
          (elementPtr r2
            ((⟨0⟩ : UInt256) +
              (iterate qi n r2 ⟨0⟩ count initial).j)).toNat =
            r2.toNat + 32 * (count + 1) := by
        simpa only [qi, initial, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl,
          Nat.zero_add] using haddress
      rw [haddress']
      omega)
  have htopFinal : Modexp.MultiLimbMemoryModel.memoryWordNat final.memory
      (r2.toNat + 32 * (kWords + 1)) = 0 := by
    have hframeWord := memoryWordNat_eq_of_memoryWordsFrom_one_eq final.memory mem
      (r2.toNat + 32 * (kWords + 1)) (by simpa only [final, initial, truncatedInitialState]
        using htopFrame)
    rw [hframeWord, htopInitial]
  have hcarryRead := readWord_eq_memoryWordOf_covered_padded final.memory final.activeWords
    (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords))
    (by simpa only [final] using hiter.1)
    (by simpa only [final] using hiter.2.1)
  have hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord final.memory final.activeWords
      (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)) = ⟨0⟩ := by
    rw [hcarryAddress, htopFinal] at hcarryRead
    simpa using hcarryRead
  have hcarryGap : (carryPtr r2 ⟨0⟩ (UInt256.ofNat kWords)).toNat -
      final.memory.size < USize.size := by
    rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
    apply lt_of_le_of_lt (Nat.sub_le _ _)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
    omega
  exact firstNonzeroRow_value mem aw q3 n r2 kWords hkPos hk
    (by simpa only [initial] using hinitialCovered)
    (by simpa only [initial] using hinitialFit) hbase hnFit hr2Fit hnBefore
    (by simpa only [qi, initial] using hgaps)
    (by simpa only [qi, initial, final] using hcarryReadZero)
    (by simpa only [qi, initial, final] using hcarryGap)

/-- Fresh allocation is one way to establish the zero top limb required by the first truncated
row. -/
theorem firstNonzeroRow_value_of_fresh_payload
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ mem.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hfresh : mem.size ≤ r2.toNat + 32 * (kWords + 1)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (firstNonzeroRowMemory mem aw q3 n r2 kWords)
          (r2.toNat + 32) (kWords + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
        (q3Word mem aw q3 ⟨0⟩).toNat *
          Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords) := by
  apply firstNonzeroRow_value_of_zero_top mem aw q3 n r2 kWords hkPos hk hcovered
    hawFit hbase hq3Fit hnFit hr2Fit hr2Bound hnBefore
  exact memoryWordNat_past_end_zero mem (r2.toNat + 32 * (kWords + 1)) hfresh

/-- The complete concrete truncated outer loop computes the low `k+1` limbs of `q3*n` from the
actual copied q3 and modulus arrays. -/
theorem truncatedRows_value_of_zero_payload
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState)
    (hstateIndex : state.i = 0) (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hinitialZero : memoryWordsFrom state.memory (r2.toNat + 32) (kWords + 1) =
      List.replicate (kWords + 1) (⟨0⟩ : UInt256))
    (hinitialLowZero : memoryWordsFrom state.memory (r2.toNat + 32) kWords =
      List.replicate kWords (⟨0⟩ : UInt256))
    (htopInitial : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
      (r2.toNat + 32 * (kWords + 1)) = 0)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ r2.toNat + 32)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat) :
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) state
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (q3.toNat + 32) (kWords + 1)) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (n.toNat + 32) kWords)) %
        UInt256.size ^ (kWords + 1) := by
  let total := kWords + 1
  let nValue := Modexp.wordLimbsToNat
    (memoryWordsFrom state.memory (n.toNat + 32) kWords)
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q state).i = q := by
    rw [truncatedRowsIterate_i, hstateIndex, Nat.zero_add]
  have hindices (limit : Nat) (hlimit : limit ≤ total) :
      ∀ q, q < limit →
        (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    dsimp only [total] at hlimit
    omega
  have hcoverage (q : Nat) (hq : q ≤ total) :=
    truncatedRows_coverage q3 n r2 kWords q state hk (hindices q hq)
      hcovered hawFit hq3Fit hnFit hr2Fit hr2Bound
  have hbases (limit : Nat) (hlimit : limit ≤ total) :
      ∀ q, q < limit →
        32 ≤ (truncatedRowsIterate q3 n r2 kWords q state).memory.size := by
    intro q hq
    exact hbase.trans (hcoverage q (by omega)).2.2
  have hframes (q ptr words : Nat) (hq : q ≤ total)
      (hbelow : ptr + 32 * words ≤ r2.toNat + 32) :
      memoryWordsFrom
          (truncatedRowsIterate q3 n r2 kWords q state).memory ptr words =
        memoryWordsFrom state.memory ptr words := by
    exact truncatedRows_memoryWords_below q3 n r2 kWords q ptr words state
      (hindices q hq) (hbases q hq) hr2Bound hbelow
  have hupdates : ∀ q, q < total →
      let current := truncatedRowsIterate q3 n r2 kWords q state
      let next := truncatedRowAdvance q3 n r2 kWords current
      let qi := q3Word current.memory current.activeWords q3 (UInt256.ofNat current.i)
      Modexp.wordLimbsToNat
          (memoryWordsFrom next.memory (r2.toNat + 32) total) % UInt256.size ^ total =
        (Modexp.wordLimbsToNat
            (memoryWordsFrom current.memory (r2.toNat + 32) total) +
          UInt256.size ^ q * (qi.toNat * nValue)) % UInt256.size ^ total := by
    intro q hq
    dsimp only
    let current := truncatedRowsIterate q3 n r2 kWords q state
    let qi := q3Word current.memory current.activeWords q3 (UInt256.ofNat current.i)
    have hqLe : q ≤ kWords := by dsimp only [total] at hq; omega
    have hcurrentIndex : current.i = q := by simpa only [current] using hindex q
    have hqiEq : qi = q3Word current.memory current.activeWords q3 (UInt256.ofNat q) := by
      simp only [qi, hcurrentIndex]
    have hcurrentCoverage := hcoverage q (by omega)
    have hcurrentBase : 32 ≤ current.memory.size :=
      hbase.trans (by simpa only [current] using hcurrentCoverage.2.2)
    have hnFrame : memoryWordsFrom current.memory (n.toNat + 32) kWords =
        memoryWordsFrom state.memory (n.toNat + 32) kWords := by
      simpa only [current] using hframes q (n.toNat + 32) kWords (by omega) (by omega)
    change Modexp.wordLimbsToNat
          (memoryWordsFrom (truncatedRowAdvance q3 n r2 kWords current).memory
            (r2.toNat + 32) total) % UInt256.size ^ total =
        (Modexp.wordLimbsToNat
            (memoryWordsFrom current.memory (r2.toNat + 32) total) +
          UInt256.size ^ q * (qi.toNat * nValue)) % UInt256.size ^ total
    by_cases hzero : qi = ⟨0⟩
    · have hzeroQ : q3Word current.memory current.activeWords q3
          (UInt256.ofNat q) = ⟨0⟩ := by rw [← hqiEq]; exact hzero
      simp [truncatedRowAdvance, hcurrentIndex, hzeroQ, qi, hzero]
    · by_cases hqZero : q = 0
      · have hcurrent : current = state := by
          rw [show current = truncatedRowsIterate q3 n r2 kWords q state by rfl, hqZero]
          rfl
        have hcurrentIndexZero : current.i = 0 := by omega
        have hzero0 : q3Word current.memory current.activeWords q3 ⟨0⟩ ≠ ⟨0⟩ := by
          simpa only [qi, hcurrentIndexZero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
            using hzero
        have hfirst := firstNonzeroRow_value_of_zero_top current.memory
          current.activeWords q3 n r2 kWords hkPos hk
          (by simpa only [current] using hcurrentCoverage.1)
          (by simpa only [current] using hcurrentCoverage.2.1) hcurrentBase
          hq3Fit hnFit hr2Fit hr2Bound hnBefore (by
            simpa only [hcurrent] using htopInitial)
        have hresultZero : memoryWordsFrom current.memory (r2.toNat + 32) total =
            List.replicate total (⟨0⟩ : UInt256) := by
          simpa only [hcurrent, total] using hinitialZero
        have hresultLowZero : memoryWordsFrom current.memory (r2.toNat + 32) kWords =
            List.replicate kWords (⟨0⟩ : UInt256) := by
          simpa only [hcurrent] using hinitialLowZero
        have hnextMemory :
            (truncatedRowAdvance q3 n r2 kWords current).memory =
              firstNonzeroRowMemory current.memory current.activeWords q3 n r2 kWords := by
          have hnonzero0 : q3Word current.memory current.activeWords q3
              (UInt256.ofNat 0) ≠ ⟨0⟩ := by
            simpa only [hqZero] using (show q3Word current.memory current.activeWords q3
              (UInt256.ofNat q) ≠ ⟨0⟩ by rw [← hqiEq]; exact hzero)
          simp [truncatedRowAdvance, hcurrentIndexZero, hnonzero0]
        rw [hnextMemory, hfirst, hresultZero, hresultLowZero, hnFrame]
        simp [Modexp.wordLimbsToNat_replicate_zero, hqZero, current, qi, nValue,
          hcurrent, hstateIndex, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl]
      · have hqPos : 0 < q := Nat.pos_of_ne_zero hqZero
        let width := kWords + 1 - q
        let rowInitial := truncatedInitialState current.memory current.activeWords q3
          (UInt256.ofNat q)
        have hq3Address : (q3ElementPtr q3 (UInt256.ofNat q)).toNat =
            q3.toNat + 32 * (q + 1) := by
          have hqWord : q < UInt256.size :=
            (show q < 2 ^ 64 by omega).trans (by decide)
          unfold q3ElementPtr
          rw [elementPtr_toNat_of_fit q3 (UInt256.ofNat q) (by
            rw [UInt256.toNat_ofNat_of_lt hqWord]
            omega), UInt256.toNat_ofNat_of_lt hqWord]
        have hq3Read := readWords1_coverage current.memory current.activeWords
          (q3ElementPtr q3 (UInt256.ofNat q))
          (by simpa only [current] using hcurrentCoverage.1)
          (by simpa only [current] using hcurrentCoverage.2.1)
          (by rw [hq3Address]; omega)
        have hrowCovered : MemoryCovered rowInitial.memory rowInitial.activeWords := by
          simpa only [rowInitial, truncatedInitialState, q3Words, afterLoad] using hq3Read.1
        have hrowFit : rowInitial.activeWords.toNat * 32 < UInt256.size := by
          simpa only [rowInitial, truncatedInitialState, q3Words, afterLoad] using hq3Read.2
        have hgaps := truncatedInner_gaps current.memory current.activeWords q3 n r2 q kWords
          width hqLe (by omega) hr2Bound
        have hlater := laterNonzeroRow_value_mod current.memory current.activeWords q3 n r2
          q kWords hqPos hqLe hk hrowCovered hrowFit hcurrentBase hnFit hr2Fit hnBefore
          (by simpa only [rowInitial, width] using hgaps)
        let low := memoryWordsFrom current.memory (n.toNat + 32) width
        let high := memoryWordsFrom current.memory (n.toNat + 32 + 32 * width)
          (kWords - width)
        have hnSplit : low ++ high = memoryWordsFrom current.memory (n.toNat + 32) kWords := by
          have hsplit := memoryWordsFrom_split current.memory (n.toNat + 32) width
            (kWords - width)
          have hsum : width + (kWords - width) = kWords := by
            dsimp only [width]
            omega
          rw [hsum] at hsplit
          simpa only [low, high] using hsplit.symm
        have hshift := shiftedPrefixProduct_mod
          (q3Word current.memory current.activeWords q3 (UInt256.ofNat q)) low high q total
          (by simp only [low, memoryWordsFrom_length]; dsimp only [width, total]; omega)
        have hqiIndex : UInt256.ofNat current.i = UInt256.ofNat q := by
          rw [hcurrentIndex]
        have hshift' :
            (UInt256.size ^ q * (qi.toNat * Modexp.wordLimbsToNat low)) %
                UInt256.size ^ total =
              (UInt256.size ^ q * (qi.toNat * nValue)) % UInt256.size ^ total := by
          rw [hnSplit, hnFrame] at hshift
          rw [hqiEq]
          simpa only [nValue] using hshift
        have hlater' :
            Modexp.wordLimbsToNat
                (memoryWordsFrom
                  (laterNonzeroRowMemory current.memory current.activeWords q3 n r2 q kWords)
                  (r2.toNat + 32) total) % UInt256.size ^ total =
              (Modexp.wordLimbsToNat
                  (memoryWordsFrom current.memory (r2.toNat + 32) total) +
                UInt256.size ^ q * (qi.toNat * Modexp.wordLimbsToNat low)) %
                UInt256.size ^ total := by
          simpa only [total, width, low, qi, hcurrentIndex] using hlater
        have hreplace :
            (Modexp.wordLimbsToNat
                (memoryWordsFrom current.memory (r2.toNat + 32) total) +
              UInt256.size ^ q * (qi.toNat * Modexp.wordLimbsToNat low)) %
                UInt256.size ^ total =
              (Modexp.wordLimbsToNat
                  (memoryWordsFrom current.memory (r2.toNat + 32) total) +
                UInt256.size ^ q * (qi.toNat * nValue)) % UInt256.size ^ total := by
          calc
            _ = (Modexp.wordLimbsToNat
                    (memoryWordsFrom current.memory (r2.toNat + 32) total) %
                    UInt256.size ^ total +
                  (UInt256.size ^ q * (qi.toNat * Modexp.wordLimbsToNat low)) %
                    UInt256.size ^ total) % UInt256.size ^ total := Nat.add_mod _ _ _
            _ = (Modexp.wordLimbsToNat
                    (memoryWordsFrom current.memory (r2.toNat + 32) total) %
                    UInt256.size ^ total +
                  (UInt256.size ^ q * (qi.toNat * nValue)) %
                    UInt256.size ^ total) % UInt256.size ^ total := by rw [hshift']
            _ = _ := (Nat.add_mod _ _ _).symm
        have hnextMemory :
            (truncatedRowAdvance q3 n r2 kWords current).memory =
              laterNonzeroRowMemory current.memory current.activeWords q3 n r2 q kWords := by
          have hnonzeroQ : q3Word current.memory current.activeWords q3
              (UInt256.ofNat q) ≠ ⟨0⟩ := by rw [← hqiEq]; exact hzero
          simp [truncatedRowAdvance, hcurrentIndex, hnonzeroQ, hqZero]
        rw [hnextMemory, hlater', hreplace]
  have hrows := truncatedRows_value_of_updates q3 n r2 kWords total total nValue state hupdates
  have hsource := truncatedSourceWords_eq_q3Payload q3 n r2 kWords total state
    hstateIndex (by rfl) hk hcovered hawFit hbase hq3Fit hnFit hr2Fit hr2Bound hq3Before
  let final := truncatedRowsIterate q3 n r2 kWords total state
  have hfinalBound := Modexp.wordLimbsToNat_lt_pow
    (memoryWordsFrom final.memory (r2.toNat + 32) total)
  rw [memoryWordsFrom_length] at hfinalBound
  change Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (r2.toNat + 32) total) =
    (Modexp.wordLimbsToNat
        (memoryWordsFrom state.memory (q3.toNat + 32) total) *
      Modexp.wordLimbsToNat (memoryWordsFrom state.memory (n.toNat + 32) kWords)) %
      UInt256.size ^ total
  change Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (r2.toNat + 32) total) % UInt256.size ^ total =
    (Modexp.wordLimbsToNat (memoryWordsFrom state.memory (r2.toNat + 32) total) +
      Modexp.wordLimbsToNat (truncatedSourceWords q3 n r2 kWords total state) * nValue) %
      UInt256.size ^ total at hrows
  rw [Nat.mod_eq_of_lt hfinalBound] at hrows
  simpa only [total, nValue, hsource, hinitialZero,
    Modexp.wordLimbsToNat_replicate_zero, Nat.zero_add] using hrows

/-- A fresh payload satisfies the explicit zero facts used by the generalized truncated-row
semantic theorem. -/
theorem truncatedRows_value_of_fresh_payload
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState)
    (hstateIndex : state.i = 0) (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hfresh : state.memory.size ≤ r2.toNat + 32)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ r2.toNat + 32)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat) :
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) state
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (q3.toNat + 32) (kWords + 1)) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory (n.toNat + 32) kWords)) %
        UInt256.size ^ (kWords + 1) := by
  apply truncatedRows_value_of_zero_payload q3 n r2 kWords state hstateIndex hkPos hk
    hcovered hawFit hbase
  · exact memoryWordsFrom_past_end_zero state.memory (r2.toNat + 32) (kWords + 1) hfresh
  · exact memoryWordsFrom_past_end_zero state.memory (r2.toNat + 32) kWords hfresh
  · apply memoryWordNat_past_end_zero
    exact hfresh.trans (by omega)
  · exact hq3Fit
  · exact hnFit
  · exact hr2Fit
  · exact hr2Bound
  · exact hq3Before
  · exact hnBefore

/-- Instantiating the semantic theorem with the exact Solidity `r2` allocation proves the
deployed truncated multiplication result directly from the allocated EVM state. -/
theorem r2Allocated_truncatedRows_value
    (mem : ByteArray) (aw q3 n : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ fp + 32)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ fp) :
    let allocatedMemory := r2AllocatedMemory mem fp kWords
    let allocatedWords := r2AllocatedWords aw fp kWords
    let r2 := UInt256.ofNat fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (kWords + 1)) =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom allocatedMemory (q3.toNat + 32) (kWords + 1)) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom allocatedMemory (n.toNat + 32) kWords)) %
        UInt256.size ^ (kWords + 1) := by
  let allocatedMemory := r2AllocatedMemory mem fp kWords
  let allocatedWords := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  have hfpNat : r2.toNat = fp := by
    simpa only [r2] using r2AllocatedPtr_toNat fp kWords hbound
  have hallocatedCoverage := r2AllocatedMemory_coverage mem aw fp kWords hcovered hawFit
    hmemSize hmemLe hgap hbound
  have hallocatedSize : allocatedMemory.size = fp + 32 := by
    simpa only [allocatedMemory] using
      r2AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    have h64 : fp + 32 * (kWords + 2) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact lt_trans (by omega : q3.toNat + 32 * (kWords + 3) < 2 ^ 64 + 32)
      (by decide : 2 ^ 64 + 32 < UInt256.size)
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    have h64 : fp + 32 * (kWords + 2) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact lt_trans (by omega : n.toNat + 32 * (kWords + 2) < 2 ^ 64 + 32)
      (by decide : 2 ^ 64 + 32 < UInt256.size)
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hfpNat]
    have h64 : fp + 32 * (kWords + 2) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact lt_trans (by omega : fp + 32 * (kWords + 3) < 2 ^ 64 + 32)
      (by decide : 2 ^ 64 + 32 < UInt256.size)
  have hsemantic := truncatedRows_value_of_fresh_payload q3 n r2 kWords initial
    (by rfl) hkPos hk
    (by simpa only [initial, allocatedMemory, allocatedWords] using hallocatedCoverage.1)
    (by simpa only [initial, allocatedMemory, allocatedWords] using hallocatedCoverage.2)
    (by rw [show initial.memory.size = fp + 32 by simpa only [initial] using hallocatedSize]
        omega)
    (by rw [show initial.memory.size = fp + 32 by simpa only [initial] using hallocatedSize,
        hfpNat])
    hq3Fit hnFit hr2Fit
    (by simpa only [r2, hfpNat] using hbound)
    (by rw [hfpNat]; exact hq3Before)
    (by rw [hfpNat]; exact hnBefore)
  simpa only [allocatedMemory, allocatedWords, r2, initial, hfpNat] using hsemantic

end Modexp.MultiLimbBarrettTruncatedMulSemantic
