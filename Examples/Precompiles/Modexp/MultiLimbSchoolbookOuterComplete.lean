import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationComplete
import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterLoopFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationSemantic

/-!
# Semantic composition of arbitrary schoolbook iterations

This file folds complete semantic iterations in the same descending quotient-index order as the
deployed loop. The frame theorem proves that lower-index iterations retain every earlier quotient
word, so the final quotient array is derived rather than assumed.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookOuterComplete

open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookOuterSemantic
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookDigitSemantic
open MultiLimbSchoolbookIterationFunction
open MultiLimbSchoolbookIterationComplete
open MultiLimbSchoolbookOuterLoopFunction
open MultiLimbSchoolbookSingle
open MultiLimbSchoolbookNormalizationSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The generated wrapped expression for a current-window word is the ordinary array address
once the bounded schoolbook-loop geometry rules out wrapping. -/
theorem currentUAddress_eq_arrayAddress
    (u : UInt256) (current index : Nat)
    (hcurrent : 0 < current)
    (hsumWord : current + index < UInt256.size)
    (hrange : current + index - 1 ≤ 65)
    (hfit : u.toNat + 32 * (current + index) < UInt256.size) :
    MultiLimbSchoolbookDivision.multiplySubtractUAddress u (UInt256.ofNat current)
        (UInt256.ofNat index) =
      arrayAddress u (current + index - 1) := by
  apply u256_inj
  rw [MultiLimbSchoolbookIterationSemantic.multiplySubtractUAddress_ofNat_toNat u current
    index hcurrent hsumWord hrange hfit]
  change _ = (MultiLimbOddCompare.elementPtr u
    (UInt256.ofNat (current + index - 1))).toNat
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit u (current + index - 1) (by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ current + index)] using hfit)]
  omega

/-- A generated current-window slice is the corresponding ordinary little-endian array slice. -/
theorem windowReadSlice_eq_arrayReadWords
    (mem : ByteArray) (aw u : UInt256) (current start count : Nat)
    (hcurrent : 0 < current)
    (hrange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hfit : u.toNat + 32 * (current + start + count) < UInt256.size) :
    MultiLimbSchoolbookIterationSemantic.windowReadSlice mem aw u current start count =
      arrayReadWords mem aw u (current + start - 1) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have haddress := currentUAddress_eq_arrayAddress u current start hcurrent
        (by omega) (by omega) (by omega)
      simp only [MultiLimbSchoolbookIterationSemantic.windowReadSlice, arrayReadWords]
      rw [haddress]
      change MultiLimbSchoolbookNormalization.arrayWord mem aw u
          (current + start - 1) :: _ = _
      have hstart : current + (start + 1) - 1 = current + start - 1 + 1 := by omega
      rw [ih (start + 1) (by omega) (by omega) (by omega), hstart]

/-- One complete iteration's model window is exactly the concrete `(count+1)`-word array segment
that the generated loads consume. -/
theorem semanticIteration_window_eq_arraySegment
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit) :
    Modexp.wordLimbsToNat (arrayReadWords mem aw u (cursor - 1) (count + 1)) =
      MultiLimbSchoolbookDivisionSemantic.windowNat (uRest ++ [uSecond, uLo]) uHi := by
  rw [arrayReadWords_succ_append,
    MultiLimbSchoolbookDigitSemantic.windowNat_eq_append]
  have hlower0 := windowReadSlice_eq_arrayReadWords mem aw u cursor 0 count h.hcurrent
    (by simpa using h.hwindowRange) (by simpa using h.hsumWord) (by simpa using h.huFit)
  have hlower : MultiLimbSchoolbookIterationSemantic.windowReadSlice mem aw u cursor 0 count =
      arrayReadWords mem aw u (cursor - 1) count := by
    simpa only [Nat.add_zero] using hlower0
  have htop := currentUAddress_eq_arrayAddress u cursor count h.hcurrent h.hsumWord
    (by have := h.hwindowRange; omega) h.huFit
  have htopIndex : cursor - 1 + count = cursor + count - 1 := by
    have := h.hcurrent
    omega
  rw [htopIndex, ← hlower]
  change Modexp.wordLimbsToNat
      (MultiLimbSchoolbookIterationSemantic.windowReadSlice mem aw u cursor 0 count ++
        [MultiLimbDivisionTrace.readWord mem aw (arrayAddress u (cursor + count - 1))]) = _
  rw [← htop, h.huSlice, h.huTop]

/-- A complete iteration preserves an arbitrary low prefix that lies below its current window. -/
theorem semanticIteration_preserves_u_prefix
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount lowCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hprefix : lowCount + 1 ≤ cursor)
    (hstoreBelow : ∀ sourceIndex, sourceIndex < lowCount ->
      (arrayAddress quotient jj).toNat + 32 ≤ (arrayAddress u sourceIndex).toNat) :
    arrayReadWords digit.memory digit.activeWords u 0 lowCount =
      arrayReadWords mem aw u 0 lowCount := by
  have hactive := (semanticIteration_eq_div_mod h).1
  rw [hactive]
  induction lowCount with
  | zero => rfl
  | succ lowCount ih =>
      rw [arrayReadWords_succ_append, arrayReadWords_succ_append]
      have hprefix' : lowCount + 1 ≤ cursor := by omega
      have ih' := ih hprefix' (fun sourceIndex hsource =>
        hstoreBelow sourceIndex (by omega))
      rw [ih']
      have hword := semanticIteration_preserves_u_word_below h
        (sourceIndex := lowCount) (by omega) (hstoreBelow lowCount (by omega))
      congr 1
      have hword' : MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u lowCount =
          MultiLimbSchoolbookNormalization.arrayWord mem aw u lowCount := hword
      have hword0 : MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u
            (0 + lowCount) =
          MultiLimbSchoolbookNormalization.arrayWord mem aw u (0 + lowCount) := by
        simpa only [Nat.zero_add] using hword'
      exact congrArg (fun word => [word]) hword0

theorem arrayReadWords_add
    (mem : ByteArray) (aw array : UInt256) (start left right : Nat) :
    arrayReadWords mem aw array start (left + right) =
      arrayReadWords mem aw array start left ++
        arrayReadWords mem aw array (start + left) right := by
  induction left generalizing start with
  | zero => simp [arrayReadWords]
  | succ left ih =>
      simp only [Nat.succ_add, arrayReadWords, List.cons_append]
      rw [ih (start + 1)]
      congr 2
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem divisorReadSlice_length
    (mem : ByteArray) (aw v : UInt256) (start count : Nat) :
    (MultiLimbSchoolbookIterationSemantic.divisorReadSlice mem aw v start count).length =
      count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [MultiLimbSchoolbookIterationSemantic.divisorReadSlice, ih]

/-- The low `count` output words of one iteration are the exact reduced remainder.  The generated
iteration also writes a high word, but normalized-divisor bounds force that word to zero. -/
theorem semanticIteration_resultSegment_eq_mod
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords digit.memory digit.activeWords u (cursor - 1) count) =
      MultiLimbSchoolbookDivisionSemantic.windowNat (uRest ++ [uSecond, uLo]) uHi %
        Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  let divisorWords := vRest ++ [vSecond, vTop]
  let divisor := Modexp.wordLimbsToNat divisorWords
  let window := MultiLimbSchoolbookDivisionSemantic.windowNat
    (uRest ++ [uSecond, uLo]) uHi
  have hlength : divisorWords.length = count := by
    have hsliced := congrArg List.length h.hvSlice
    simpa only [divisorWords, divisorReadSlice_length] using hsliced.symm
  have hdivisorPos : 0 < divisor :=
    normalizedDivisor_positive vRest vSecond vTop hnormalized
  have hdivisorBound : divisor < UInt256.size ^ count := by
    have hbound := Modexp.wordLimbsToNat_lt_pow divisorWords
    simpa only [hlength] using hbound
  have hlocal := semanticIteration_eq_div_mod h
  have hactive : digit.activeWords = aw := hlocal.1
  have hlower0 := windowReadSlice_eq_arrayReadWords digit.memory aw u cursor 0 count
    h.hcurrent (by simpa using h.hwindowRange) (by simpa using h.hsumWord)
    (by simpa [hlocal.2.1] using h.huFit)
  have hlower : MultiLimbSchoolbookIterationSemantic.windowReadSlice digit.memory aw u cursor
      0 count = arrayReadWords digit.memory aw u (cursor - 1) count := by
    simpa only [Nat.add_zero] using hlower0
  have htop := currentUAddress_eq_arrayAddress u cursor count h.hcurrent h.hsumWord
    (by have := h.hwindowRange; omega) h.huFit
  have hwindow :
      Modexp.wordLimbsToNat (arrayReadWords digit.memory aw u (cursor - 1) count) +
          UInt256.size ^ count *
            (MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u
              (cursor + count - 1)).toNat =
        window % divisor := by
    have hresult := hlocal.2.2.2
    rw [hlower] at hresult
    change Modexp.wordLimbsToNat
        (arrayReadWords digit.memory aw u (cursor - 1) count) +
          UInt256.size ^ (arrayReadWords digit.memory aw u (cursor - 1) count).length *
            (MultiLimbDivisionTrace.readWord digit.memory aw
              (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
                (UInt256.ofNat cursor) (UInt256.ofNat count))).toNat = window % divisor at hresult
    rw [arrayReadWords_length, htop] at hresult
    exact hresult
  have hremainderBound : window % divisor < UInt256.size ^ count :=
    lt_trans (Nat.mod_lt window hdivisorPos) hdivisorBound
  have htopZero :
      (MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u
        (cursor + count - 1)).toNat = 0 := by
    by_contra hne
    have hone : 1 ≤ (MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u
        (cursor + count - 1)).toNat := Nat.one_le_iff_ne_zero.mpr hne
    have hpow : 0 < UInt256.size ^ count := Nat.pow_pos (by norm_num [UInt256.size])
    rw [← hwindow] at hremainderBound
    nlinarith
  rw [hactive]
  rw [htopZero] at hwindow
  simpa only [Nat.mul_zero, Nat.add_zero, divisor, window] using hwindow

/-- Quotient digits emitted most significant first by the ordinary division fold. -/
def divisionQuotientDigits (radix divisor : Nat) :
    DivisionFoldState -> List Nat -> List Nat
  | _, [] => []
  | state, digit :: digits =>
      let window := state.remainder * radix + digit
      (window / divisor) ::
        divisionQuotientDigits radix divisor
          (divisionDigitStep radix divisor digit state) digits

/-- Natural values of the first `count` quotient words, in little-endian array order. -/
def quotientReadNats (mem : ByteArray) (aw quotient : UInt256) : Nat -> List Nat
  | 0 => []
  | count + 1 =>
      quotientReadNats mem aw quotient count ++ [(arrayWord mem aw quotient count).toNat]

/-- Natural value of a little-endian list of radix digits. -/
def natLimbsToNat (radix : Nat) : List Nat -> Nat
  | [] => 0
  | digit :: digits => digit + radix * natLimbsToNat radix digits

/-- Natural value of the terminal remainder window left by the last quotient iteration. -/
def terminalRemainderNat
    (mem : ByteArray) (aw u : UInt256) (count : Nat) : Nat :=
  windowNat (MultiLimbSchoolbookIterationSemantic.windowReadSlice mem aw u 1 0 count)
    (MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u (UInt256.ofNat 1)
        (UInt256.ofNat count)))

theorem natLimbsToNat_reverse (radix : Nat) (digits : List Nat) :
    natLimbsToNat radix digits.reverse = digitsToNatMSB radix digits := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      rw [List.reverse_cons]
      simp only [digitsToNatMSB]
      have happend : ∀ words value,
          natLimbsToNat radix (words ++ [value]) =
            natLimbsToNat radix words + radix ^ words.length * value := by
        intro words value
        induction words with
        | nil => simp [natLimbsToNat]
        | cons word words ihWords =>
            simp only [List.cons_append, natLimbsToNat, List.length_cons, pow_succ,
              ihWords]
            ring
      rw [happend, ih, List.length_reverse]
      ring

@[simp] theorem divisionQuotientDigits_length
    (radix divisor : Nat) (state : DivisionFoldState) (digits : List Nat) :
    (divisionQuotientDigits radix divisor state digits).length = digits.length := by
  induction digits generalizing state with
  | nil => rfl
  | cons digit digits ih =>
      simp [divisionQuotientDigits, ih]

/-- The pure fold's quotient accumulator is exactly its emitted MSB-first digit list, extending
the incoming accumulator by the appropriate radix power. -/
theorem divisionDigits_quotient_eq_digits
    (radix divisor : Nat) (state : DivisionFoldState) (digits : List Nat) :
    (divisionDigits radix divisor state digits).quotient =
      state.quotient * radix ^ digits.length +
        digitsToNatMSB radix (divisionQuotientDigits radix divisor state digits) := by
  induction digits generalizing state with
  | nil => simp [divisionDigits, divisionQuotientDigits, digitsToNatMSB]
  | cons digit digits ih =>
      let next := divisionDigitStep radix divisor digit state
      let qDigit := (state.remainder * radix + digit) / divisor
      have hrest := ih next
      simp only [divisionDigits, divisionQuotientDigits, digitsToNatMSB,
        List.length_cons]
      dsimp only [next, qDigit, divisionDigitStep] at hrest ⊢
      rw [hrest]
      rw [divisionQuotientDigits_length]
      ring

/-- Semantic counterpart of the deployed descending continuation chain. The two frame fields are
ordinary allocator separation facts used to retain quotient words at higher indices. -/
inductive SemanticContinuations
    (count uCount quotientCount : Nat)
    (u shift ret rem v quotient vTop normalizationMarker : UInt256)
    (vRest : List UInt256) (vSecond : UInt256) :
    DivisionFoldState -> List Nat -> ByteArray -> UInt256 ->
      ByteArray -> UInt256 -> Nat -> Nat -> Prop
  | done (state : DivisionFoldState) (mem : ByteArray) (aw : UInt256) :
      SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
        normalizationMarker vRest vSecond state [] mem aw mem aw 0 0
  | step
      (state : DivisionFoldState) (input : Nat) (inputs : List Nat)
      (mem : ByteArray) (aw uHi uLo uSecond : UInt256)
      (uRest : List UInt256) (estimate : EstimateResult) (digit : DigitResult)
      (finalMem : ByteArray) (finalAw : UInt256) (restSteps restGas : Nat)
      (layout : OperandLayout mem aw u uHi uLo (inputs.length + 1) count uCount)
      (semantic : SemanticIteration mem aw inputs.length (inputs.length + 1) count uCount
        quotientCount uHi vTop uLo u shift ret rem v quotient normalizationMarker
        vRest uRest vSecond uSecond estimate digit)
      (hwindow : windowNat (uRest ++ [uSecond, uLo]) uHi =
        state.remainder * UInt256.size + input)
      (hindex : inputs.length < quotientCount)
      (hsourceBelowU : ∀ sourceIndex, inputs.length + 1 ≤ sourceIndex ->
        sourceIndex < quotientCount ->
        (arrayAddress quotient sourceIndex).toNat + 32 ≤
          u.toNat + 32 * (inputs.length + 1))
      (hstoreBelowSource : ∀ sourceIndex, inputs.length + 1 ≤ sourceIndex ->
        sourceIndex < quotientCount ->
        (arrayAddress quotient inputs.length).toNat + 32 ≤
          (arrayAddress quotient sourceIndex).toNat)
      (rest : SemanticContinuations count uCount quotientCount u shift ret rem v quotient
        vTop normalizationMarker vRest vSecond
        (divisionDigitStep UInt256.size
          (Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) input state)
        inputs digit.memory digit.activeWords finalMem finalAw restSteps restGas) :
      SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
        normalizationMarker vRest vSecond state (input :: inputs) mem aw finalMem finalAw
        (109 + (estimate.steps + digit.steps) + restSteps)
        (397 + (estimate.gas + digit.gas) + restGas)

/-- The fold inputs are forced by the concrete overlapping `u` windows.  The value on the left
is the initial normalized dividend array; the extra state term makes the invariant compositional
for recursive tails.  The address-order premise is only the quotient-before-`u` allocator layout
needed to retain lower source words. -/
theorem semanticContinuations_inputValue
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat) :
    Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 (inputs.length + count)) =
      digitsToNatMSB UInt256.size inputs +
        state.remainder * UInt256.size ^ inputs.length := by
  induction h with
  | done => exact (hnonempty rfl).elim
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      have hparentWindow := semanticIteration_window_eq_arraySegment semantic
      cases inputs with
      | nil =>
          rw [hwindow] at hparentWindow
          simpa [digitsToNatMSB, pow_one, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hparentWindow
      | cons next inputs =>
          let tailInputs := next :: inputs
          let nextState := divisionDigitStep UInt256.size
            (Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) input state
          have htailNonempty : tailInputs ≠ [] := by simp [tailInputs]
          have htailValue :
              Modexp.wordLimbsToNat
                  (arrayReadWords digit.memory digit.activeWords u 0
                    (tailInputs.length + count)) =
                digitsToNatMSB UInt256.size tailInputs +
                  nextState.remainder * UInt256.size ^ tailInputs.length := by
            simpa only [tailInputs, nextState] using ih htailNonempty
          have hprefix := semanticIteration_preserves_u_prefix semantic
            (lowCount := tailInputs.length) (by simp [tailInputs]) (by
              intro sourceIndex hsource
              exact hquotBelowU tailInputs.length sourceIndex hindex hsource)
          have hresult0 := semanticIteration_resultSegment_eq_mod semantic hnormalized
          have hresult :
              Modexp.wordLimbsToNat
                  (arrayReadWords digit.memory digit.activeWords u tailInputs.length count) =
                nextState.remainder := by
            rw [hwindow] at hresult0
            simpa only [tailInputs, List.length_cons, nextState, divisionDigitStep] using hresult0
          have hchildSplit := arrayReadWords_add digit.memory digit.activeWords u 0
            tailInputs.length count
          simp only [Nat.zero_add] at hchildSplit
          have hchildValue :
              Modexp.wordLimbsToNat
                  (arrayReadWords digit.memory digit.activeWords u 0
                    (tailInputs.length + count)) =
                Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 tailInputs.length) +
                  nextState.remainder * UInt256.size ^ tailInputs.length := by
            rw [hchildSplit, Modexp.wordLimbsToNat_append, arrayReadWords_length, hprefix,
              hresult]
            ring
          have hprefixValue :
              Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 tailInputs.length) =
                digitsToNatMSB UInt256.size tailInputs := by
            rw [hchildValue] at htailValue
            exact Nat.add_right_cancel htailValue
          have hparentSplit0 := arrayReadWords_add mem aw u 0 tailInputs.length (count + 1)
          have hparentWindow' :
              Modexp.wordLimbsToNat
                  (arrayReadWords mem aw u tailInputs.length (count + 1)) =
                MultiLimbSchoolbookDivisionSemantic.windowNat
                  (uRest ++ [uSecond, uLo]) uHi := by
            simpa only [tailInputs, List.length_cons, Nat.add_sub_cancel_left] using
              hparentWindow
          have hparentSplit :
              arrayReadWords mem aw u 0 ((input :: tailInputs).length + count) =
                arrayReadWords mem aw u 0 tailInputs.length ++
                  arrayReadWords mem aw u tailInputs.length (count + 1) := by
            simpa only [List.length_cons, Nat.zero_add, Nat.add_assoc, Nat.add_comm count 1]
              using hparentSplit0
          rw [hparentSplit, Modexp.wordLimbsToNat_append, arrayReadWords_length,
            hparentWindow', hprefixValue, hwindow]
          dsimp only [tailInputs]
          simp only [digitsToNatMSB, List.length_cons]
          rw [pow_succ]
          ring

/-- At the deployed zero initial fold state, the abstract input sequence is exactly the natural
value of the concrete normalized `u` array. -/
theorem semanticContinuations_zero_inputValue
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat) :
    digitsToNatMSB UInt256.size inputs =
      Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 (inputs.length + count)) := by
  have hvalue := semanticContinuations_inputValue h hnonempty hnormalized hquotBelowU
  simpa only [DivisionFoldState.remainder, zero_mul, Nat.add_zero] using hvalue.symm

/-- The complete selected continuation preserves memory size and the active-word counter. -/
theorem semanticContinuations_final_geometry
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas) :
    finalAw = aw ∧ finalMem.size = mem.size := by
  induction h with
  | done => exact ⟨rfl, rfl⟩
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      have hlocal := semanticIteration_eq_div_mod semantic
      exact ⟨ih.1.trans hlocal.1, ih.2.trans hlocal.2.1⟩

/-- Every quotient digit preserves a padded word that lies below the first `u` payload word and
below every quotient destination. -/
theorem semanticContinuations_read_below_frame
    {count uCount quotientCount read : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hreadBelowU : read + 32 ≤ u.toNat + 32)
    (hreadBelowQuotient : ∀ jj, jj < quotientCount ->
      read + 32 ≤ (arrayAddress quotient jj).toNat) :
    finalMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction h with
  | done => rfl
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      have hlocal := semanticIteration_read_below_frame semantic (by omega)
        (hreadBelowQuotient inputs.length hindex)
      exact ih.trans hlocal

/-- All iterations in a chain preserve a quotient word above the range they will write. -/
theorem semanticContinuations_preserves_quotient_word
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (sourceIndex : Nat) (hsource : inputs.length ≤ sourceIndex)
    (hsourceBound : sourceIndex < quotientCount) :
    arrayWord finalMem finalAw quotient sourceIndex =
      arrayWord mem aw quotient sourceIndex := by
  induction h generalizing sourceIndex with
  | done => rfl
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      have hlocal := semanticIteration_preserves_quotient_word semantic
        (hsourceBelowU sourceIndex (by simpa using hsource) hsourceBound)
        (hstoreBelowSource sourceIndex (by simpa using hsource) hsourceBound)
      have hsemantic := semanticIteration_eq_div_mod semantic
      have htailSource : inputs.length ≤ sourceIndex :=
        Nat.le_trans (by simp) hsource
      have htail := ih sourceIndex htailSource hsourceBound
      calc
        arrayWord finalMem finalAw quotient sourceIndex =
            arrayWord digit.memory digit.activeWords quotient sourceIndex := htail
        _ = arrayWord digit.memory aw quotient sourceIndex := by rw [hsemantic.1]
        _ = arrayWord mem aw quotient sourceIndex := hlocal

/-- The final little-endian quotient words are exactly the reverse of the pure fold's emitted
MSB-first digits. -/
theorem semanticContinuations_quotient_words
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas) :
    quotientReadNats finalMem finalAw quotient inputs.length =
      (divisionQuotientDigits UInt256.size
        (Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) state inputs).reverse := by
  induction h with
  | done => rfl
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      have hlocal := semanticIteration_eq_div_mod semantic
      have hretain := semanticContinuations_preserves_quotient_word rest inputs.length
        (by simp) hindex
      simp only [List.length_cons, divisionQuotientDigits, List.reverse_cons]
      change quotientReadNats finalMem finalAw quotient (inputs.length + 1) = _
      simp only [quotientReadNats]
      rw [ih]
      congr 1
      rw [hretain, hlocal.1, hlocal.2.2.1]
      rw [hwindow]

/-- A nonempty continuation chain leaves the pure fold's final remainder in the concrete
low `u` window consumed by denormalization. -/
theorem semanticContinuations_remainder_eq_fold
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ []) :
    terminalRemainderNat finalMem finalAw u count =
      (divisionDigits UInt256.size
        (Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) state inputs).remainder := by
  induction h with
  | done => exact (hnonempty rfl).elim
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      cases inputs with
      | nil =>
          cases rest
          have hlocal := semanticIteration_eq_div_mod semantic
          simp only [divisionDigits, divisionDigitStep]
          rw [hlocal.1]
          simpa only [terminalRemainderNat, List.length_nil, zero_add, hwindow] using
            hlocal.2.2.2
      | cons next inputs =>
          simpa only [divisionDigits] using ih (by simp)

/-- Forgetting the semantic interpretation of a chain produces the exact deployed continuation
certificate, with concrete final memory and exact path-sensitive step/gas totals. -/
theorem SemanticContinuations.toValidContinuations
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas) :
    ValidContinuations count uCount quotientCount shift ret rem v quotient u vTop
      normalizationMarker inputs.length mem aw ⟨finalMem, finalAw, steps, gas⟩ := by
  induction h with
  | done =>
      exact ValidContinuations.done _ _
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      exact ValidContinuations.step (inputs.length + 1) mem aw uHi uLo
        ⟨digit.memory, digit.activeWords, estimate.steps + digit.steps,
          estimate.gas + digit.gas⟩
        ⟨finalMem, finalAw, restSteps, restGas⟩ layout semantic.toValidIteration ih

/-- Execute a nonempty semantic chain from the distinct first-iteration entry at PC 5450. The
semantic chain charges continuation prefixes, so the first entry contributes exactly five more
steps and thirteen more gas than its indexed continuation total. -/
theorem semanticDivisionLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count uCount quotientCount : Nat} {tail : List UInt256}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (hsemantic : SemanticContinuations count uCount quotientCount u shift ret rem v quotient
      vTop normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hcountWord : count < UInt256.size)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (shift :: ret :: rem :: UInt256.ofNat inputs.length :: UInt256.ofNat count :: v ::
        quotient :: u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: shift :: ret :: rem :: ⟨0⟩ ::
        UInt256.ofNat count :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      finalMem finalAw rdata acc (k + steps + 5) (C + gas + 13) := by
  cases hsemantic with
  | done => exact (hnonempty rfl).elim
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest =>
      have hrest := rest.toValidContinuations
      have hexact := divisionLoopExact hcountWord layout semantic.toValidIteration hrest hdepth h
      exact hexact.withIndices
        (by
          change k + 114 + (estimate.steps + digit.steps) + restSteps =
            k + (109 + (estimate.steps + digit.steps) + restSteps) + 5
          omega)
        (by
          change C + 410 + (estimate.gas + digit.gas) + restGas =
            C + (397 + (estimate.gas + digit.gas) + restGas) + 13
          omega)

/-- Starting from the zero fold state, the terminal concrete `u` window is the natural remainder
of the full input digit sequence. -/
theorem semanticContinuations_remainder_eq_mod
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    terminalRemainderNat finalMem finalAw u count =
      digitsToNatMSB UInt256.size inputs %
        Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  let divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])
  have hfold := semanticContinuations_remainder_eq_fold h hnonempty
  have hdivision := divisionDigits_eq_div_mod UInt256.size divisor inputs
    (normalizedDivisor_positive vRest vSecond vTop hnormalized)
  exact hfold.trans hdivision.2

/-- Starting from the zero fold state, an arbitrary semantic continuation chain leaves the exact
natural quotient in its concrete quotient array. -/
theorem semanticContinuations_quotient_eq_div
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    natLimbsToNat UInt256.size
        (quotientReadNats finalMem finalAw quotient inputs.length) =
      digitsToNatMSB UInt256.size inputs /
        Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  let divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])
  have hwords := semanticContinuations_quotient_words h
  have hquotientDigits := divisionDigits_quotient_eq_digits UInt256.size divisor
    ⟨0, 0⟩ inputs
  have hdivision := divisionDigits_eq_div_mod UInt256.size divisor inputs
    (normalizedDivisor_positive vRest vSecond vTop hnormalized)
  rw [hwords, natLimbsToNat_reverse]
  simpa only [DivisionFoldState.quotient, zero_mul, zero_add] using
    hquotientDigits.symm.trans hdivision.1

end Modexp.MultiLimbSchoolbookOuterComplete
