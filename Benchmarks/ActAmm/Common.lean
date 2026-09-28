import Benchmarks.ActAmm.Bytecode
import Reasoning.ABI
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

/-- Selector word left on the stack by the solc dispatcher. -/
abbrev ammSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- A calldata selector matches four literal bytes. -/
abbrev ammSelIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

-- LIBRARY CANDIDATE: Reasoning.Solc, the caller's address as a storage mapping key.
theorem ammSource_keyValueToWord (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  unfold keyValueToWord UInt256.ofNat
  change a.val = (Fin.ofNat UInt256.size a.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

/-- Dispatcher selectors in low-half then high-half order. -/
def ammSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ -- approve
  | 1 => ⟨#[0x13, 0xbd, 0x59, 0xeb]⟩ -- swap0
  | 2 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ -- totalSupply
  | 3 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ -- transferFrom
  | 4 => ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩ -- swap1
  | 5 => ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ -- mint
  | 6 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ -- balanceOf
  | 7 => ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ -- transfer
  | 8 => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ -- allowance
  | _ => ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ -- burn

/-- The binary-search pivot is at PC 30; its low group starts at PC 101. -/
abbrev ammSplitPc : UInt256 := ⟨30⟩
abbrev ammHighFirstArmPc : UInt256 := ⟨41⟩
abbrev ammLowJumpdestPc : UInt256 := ⟨100⟩
abbrev ammLowFirstArmPc : UInt256 := ⟨101⟩

set_option maxRecDepth 2000000 in
theorem ammSplitWellFormed : selectorSplitWellFormed ammBytecode ammSplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

set_option maxRecDepth 2000000 in
theorem ammHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed ammBytecode
      (nthArmPc ammBytecode ammHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, by native_decide⟩

set_option maxRecDepth 2000000 in
theorem ammLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed ammBytecode
      (nthArmPc ammBytecode ammLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, by native_decide⟩

-- LIBRARY CANDIDATE: Reasoning.ABI, selector-word equality from four matching bytes.
theorem ammSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ammSelWord I = sel := by
  apply u256_inj
  dsimp [ammSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

set_option maxRecDepth 2000000 in
theorem ammLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammLowFirstArmPc j))
        (ammSelWord I) =
      if (ammSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

set_option maxRecDepth 2000000 in
theorem ammHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammHighFirstArmPc j))
        (ammSelWord I) =
      if (ammSelBytes (j + 5) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem ammLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ammSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammLowFirstArmPc j))
        (ammSelWord I) = ⟨0⟩) ∧
      UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammLowFirstArmPc i))
        (ammSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = ammSelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [ammLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [ammLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem ammHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ammSelBytes (i + 5) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammHighFirstArmPc j))
        (ammSelWord I) = ⟨0⟩) ∧
      UInt256.eq (armSelNat ammBytecode (nthArmPc ammBytecode ammHighFirstArmPc i))
        (ammSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = ammSelBytes (i + 5) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [ammHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [ammHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

set_option maxRecDepth 2000000 in
theorem ammLowPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ammSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat ammBytecode ammSplitPc) (ammSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : ammSelWord I = ⟨157198259⟩ :=
      ammSelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨331176427⟩ :=
      ammSelWord_eq_of_beq I hsz 0x13 0xbd 0x59 0xeb _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨404098525⟩ :=
      ammSelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨599290589⟩ :=
      ammSelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨1035340611⟩ :=
      ammSelWord_eq_of_beq I hsz 0x3d 0xb6 0x0b 0x43 _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide

set_option maxRecDepth 2000000 in
theorem ammHighPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ammSelBytes (i + 5) == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat ammBytecode ammSplitPc) (ammSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : ammSelWord I = ⟨1784838210⟩ :=
      ammSelWord_eq_of_beq I hsz 0x6a 0x62 0x78 0x42 _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨1889567281⟩ :=
      ammSelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨3077966991⟩ :=
      ammSelWord_eq_of_beq I hsz 0xb7 0x76 0x0c 0x8f _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨3714247998⟩ :=
      ammSelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : ammSelWord I = ⟨4241707836⟩ :=
      ammSelWord_eq_of_beq I hsz 0xfc 0xd3 0x53 0x3c _ (by decide)
        (by simpa [ammSelBytes] using hsel)
    rw [hword]
    native_decide

set_option maxRecDepth 2000000 in
theorem ammReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ammBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ammSplitPc
      [ammSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ammBytecode ammSplitPc := by
    solc_dispatch_prefix
  simpa [ammSelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = ammBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat ammBytecode ammSplitPc) (ammSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat ammBytecode
        (nthArmPc ammBytecode ammHighFirstArmPc j)) (ammSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat ammBytecode
      (nthArmPc ammBytecode ammHighFirstArmPc i)) (ammSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J ammBytecode 0).contains bodyPC = true)
    (hbody : armTgt ammBytecode
      (nthArmPc ammBytecode ammHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [ammSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ammBytecode ammSplitPc := by
    solc_dispatch_prefix
  simpa [ammSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := ammBytecode) (splitPc := ammSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) ammSplitWellFormed
      (by simpa [ammSelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [ammHighFirstArmPc, ammSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          ammHighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [ammSelWord, solcSelectorWord, ammHighFirstArmPc, ammSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [ammSelWord, solcSelectorWord, ammHighFirstArmPc, ammSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [ammHighFirstArmPc, ammSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = ammBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat ammBytecode ammSplitPc) (ammSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat ammBytecode
        (nthArmPc ammBytecode ammLowFirstArmPc j)) (ammSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat ammBytecode
      (nthArmPc ammBytecode ammLowFirstArmPc i)) (ammSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J ammBytecode 0).contains bodyPC = true)
    (hbody : armTgt ammBytecode
      (nthArmPc ammBytecode ammLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [ammSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ammBytecode ammSplitPc := by
    solc_dispatch_prefix
  simpa [ammSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := ammBytecode) (splitPc := ammSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) ammSplitWellFormed
      (by simpa [ammSelWord, solcSelectorWord] using hpivot)
      (by jump_dest) (by native_decide)
      (fun j hj => by
        simpa [ammLowFirstArmPc, ammLowJumpdestPc, ammSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          ammLowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [ammSelWord, solcSelectorWord, ammLowFirstArmPc, ammLowJumpdestPc,
          ammSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using heq0 j hj)
      (by
        simpa [ammSelWord, solcSelectorWord, ammLowFirstArmPc, ammLowJumpdestPc,
          ammSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using htake)
      hjd
      (by
        simpa [ammLowFirstArmPc, ammLowJumpdestPc, ammSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

-- LIBRARY CANDIDATE: Reasoning.Memory, zero-gap write without a USize bound.
theorem toByteArray_write_eq_no_gap (v : UInt256) (mem : ByteArray) (off : ℕ)
    (hoff : mem.size ≤ off) :
    (UInt256.toByteArray v).write 0 mem off 32 =
      mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (off - mem.size)).data.size =
      (ffi.ByteArray.zeroes (off - mem.size)).size from rfl, ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32:ℕ) = 0)),
      if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
        rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]; show mem.size + (off - mem.size) = off; omega
  rw [hv, show (min 32 (32 - 0) : ℕ) = 32 from rfl,
      show min mem.size (off + 32) - (off + 32) = 0 from by omega,
      show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
        rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
      Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
      Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
      Array.append_empty]

-- GENERALIZES Reasoning.Memory.toByteArray_write_read_window_of_gap by removing its
-- redundant platform-size assumption.
theorem toByteArray_write_read_window_no_gap
    (b : UInt256) (mem : ByteArray) (off start len : Nat)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding (off + start) len =
      (UInt256.toByteArray b).extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · have hprefix : (mem.extract 0 off).size = off := by
      rw [ByteArray.size_extract]
      omega
    have hword : ((UInt256.toByteArray b).extract 0 32).size = 32 := by
      rw [ByteArray.size_extract, toByteArray_size]
      omega
    rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hword]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hprefix, hword]; omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]
    rw [extract_extract_BA]
    rw [show 0 + start = start by omega,
      show min (0 + (start + len)) 32 = start + len by omega]
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    have hprefix : (mem ++ ffi.ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen64 (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show off + start - off = start by omega,
      show off + start + len - off = start + len by omega]

-- GENERALIZES Reasoning.Memory.toByteArray_write_read_below_of_gap by removing its
-- redundant platform-size assumption.
theorem toByteArray_write_read_below_no_gap
    (b : UInt256) (mem : ByteArray) (off read : ℕ)
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact write32_read_below _ _ off read (by rw [toByteArray_size]) hle hbelow
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

-- GENERALIZES Reasoning.Memory.toByteArray_write_size_ge_off_add32 by removing its
-- redundant platform-size assumption.
theorem toByteArray_write_size_ge_off_add32_no_gap (b : UInt256)
    (mem : ByteArray) (off : ℕ) :
    off + 32 ≤ ((UInt256.toByteArray b).write 0 mem off 32).size := by
  by_cases hle : off ≤ mem.size
  · rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    rw [toByteArray_size]
    rw [Nat.min_eq_left hle]
    norm_num
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq_no_gap _ _ off hge]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      toByteArray_size]
    omega

end Benchmarks.ActAmm
