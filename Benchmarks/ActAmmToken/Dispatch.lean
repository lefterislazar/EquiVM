import Benchmarks.ActAmmToken.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.ActAmmToken

abbrev tokenSplitPc : UInt256 := ⟨30⟩
abbrev tokenHighFirstArmPc : UInt256 := ⟨41⟩
abbrev tokenLowJumpdestPc : UInt256 := ⟨100⟩
abbrev tokenLowFirstArmPc : UInt256 := ⟨101⟩

theorem tokenSplitWellFormed : selectorSplitWellFormed tokenBytecode tokenSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 1000000 in
theorem tokenHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed tokenBytecode
      (nthArmPc tokenBytecode tokenHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 1000000 in
theorem tokenLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed tokenBytecode
      (nthArmPc tokenBytecode tokenLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem tokenLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc j))
        (tokenSelWord I)
      = if (tokenSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem tokenHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc j))
        (tokenSelWord I)
      = if (tokenSelBytes (j + 4) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem tokenLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (tokenSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i → UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc j))
        (tokenSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc i))
        (tokenSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = tokenSelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [tokenLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [tokenLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem tokenHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (tokenSelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i → UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc j))
        (tokenSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc i))
        (tokenSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = tokenSelBytes (i + 4) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [tokenHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [tokenHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem tokenSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    tokenSelWord I = sel := by
  apply u256_inj
  dsimp [tokenSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

theorem tokenReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) tokenSplitPc
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed tokenBytecode tokenSplitPc := by
    solc_dispatch_prefix
  simpa [tokenSelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

theorem tokenPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (tokenSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat tokenBytecode tokenSplitPc) (tokenSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : tokenSelWord I = ⟨0x095ea7b3⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0x18160ddd⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0x23b872dd⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0x40c10f19⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x40 0xc1 0x0f 0x19 _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide

theorem tokenPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (tokenSelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat tokenBytecode tokenSplitPc) (tokenSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : tokenSelWord I = ⟨0x42966c68⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x42 0x96 0x6c 0x68 _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0x70a08231⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0x79cc6790⟩ :=
      tokenSelWord_eq_of_beq I hsz 0x79 0xcc 0x67 0x90 _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0xb7760c8f⟩ :=
      tokenSelWord_eq_of_beq I hsz 0xb7 0x76 0x0c 0x8f _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide
  · have hword : tokenSelWord I = ⟨0xdd62ed3e⟩ :=
      tokenSelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e _ (by decide)
        (by simpa [tokenSelBytes] using hsel)
    rw [hword]
    decide

set_option maxHeartbeats 1000000 in
theorem tokenReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat tokenBytecode tokenSplitPc) (tokenSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc j))
        (tokenSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc i))
        (tokenSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J tokenBytecode 0).contains bodyPC = true)
    (hbody : armTgt tokenBytecode (nthArmPc tokenBytecode tokenHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed tokenBytecode tokenSplitPc := by
    solc_dispatch_prefix
  simpa [tokenSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := tokenBytecode) (splitPc := tokenSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) tokenSplitWellFormed
      (by simpa [tokenSelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [tokenHighFirstArmPc, tokenSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          tokenHighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [tokenSelWord, solcSelectorWord, tokenHighFirstArmPc, tokenSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using heq0 j hj)
      (by
        simpa [tokenSelWord, solcSelectorWord, tokenHighFirstArmPc, tokenSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using htake)
      hjd
      (by
        simpa [tokenHighFirstArmPc, tokenSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

set_option maxHeartbeats 1000000 in
theorem tokenReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = tokenBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat tokenBytecode tokenSplitPc) (tokenSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc j))
        (tokenSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc i))
        (tokenSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J tokenBytecode 0).contains bodyPC = true)
    (hbody : armTgt tokenBytecode (nthArmPc tokenBytecode tokenLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed tokenBytecode tokenSplitPc := by
    solc_dispatch_prefix
  simpa [tokenSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := tokenBytecode) (splitPc := tokenSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) tokenSplitWellFormed
      (by simpa [tokenSelWord, solcSelectorWord] using hpivot) (by jump_dest) (by decide)
      (fun j hj => by
        simpa [tokenLowFirstArmPc, tokenLowJumpdestPc, tokenSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          tokenLowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [tokenSelWord, solcSelectorWord, tokenLowFirstArmPc, tokenLowJumpdestPc,
          tokenSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          heq0 j hj)
      (by
        simpa [tokenSelWord, solcSelectorWord, tokenLowFirstArmPc, tokenLowJumpdestPc,
          tokenSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [tokenLowFirstArmPc, tokenLowJumpdestPc, tokenSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

end Benchmarks.ActAmmToken
