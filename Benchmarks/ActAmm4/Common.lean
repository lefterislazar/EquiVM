import Benchmarks.ActAmm4.Bytecode
import Reasoning.ABI
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

/-- Selector word left on the stack by the solc dispatcher. -/
abbrev amm4SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- A calldata selector matches four literal bytes. -/
abbrev amm4SelIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

-- LIBRARY CANDIDATE: Reasoning.Solc, the caller's address as a storage mapping key.
theorem amm4Source_keyValueToWord (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  unfold keyValueToWord UInt256.ofNat
  change a.val = (Fin.ofNat UInt256.size a.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

/-- Dispatcher selectors in low-half then high-half order. -/
def amm4SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ -- approve
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ -- totalSupply
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ -- transferFrom
  | 3 => ⟨#[0x6a, 0x62, 0x78, 0x42]⟩ -- mint
  | 4 => ⟨#[0x6d, 0x9a, 0x64, 0x0a]⟩ -- swap
  | 5 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ -- balanceOf
  | 6 => ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ -- transfer
  | 7 => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ -- allowance
  | _ => ⟨#[0xfc, 0xd3, 0x53, 0x3c]⟩ -- burn

/-- The binary-search pivot is at PC 30; its low group starts at PC 101. -/
abbrev amm4SplitPc : UInt256 := ⟨30⟩
abbrev amm4HighFirstArmPc : UInt256 := ⟨41⟩
abbrev amm4LowJumpdestPc : UInt256 := ⟨100⟩
abbrev amm4LowFirstArmPc : UInt256 := ⟨101⟩

set_option maxRecDepth 2000000 in
theorem amm4SplitWellFormed : selectorSplitWellFormed amm4Bytecode amm4SplitPc := by
  exact ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

set_option maxRecDepth 2000000 in
theorem amm4HighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed amm4Bytecode
      (nthArmPc amm4Bytecode amm4HighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, by native_decide⟩

set_option maxRecDepth 2000000 in
theorem amm4LowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed amm4Bytecode
      (nthArmPc amm4Bytecode amm4LowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide, by native_decide⟩

-- LIBRARY CANDIDATE: Reasoning.ABI, selector-word equality from four matching bytes.
theorem amm4SelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    amm4SelWord I = sel := by
  apply u256_inj
  dsimp [amm4SelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

set_option maxRecDepth 2000000 in
theorem amm4LowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4LowFirstArmPc j))
        (amm4SelWord I) =
      if (amm4SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

set_option maxRecDepth 2000000 in
theorem amm4HighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4HighFirstArmPc j))
        (amm4SelWord I) =
      if (amm4SelBytes (j + 4) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem amm4LowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (amm4SelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4LowFirstArmPc j))
        (amm4SelWord I) = ⟨0⟩) ∧
      UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4LowFirstArmPc i))
        (amm4SelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = amm4SelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [amm4LowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [amm4LowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem amm4HighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (amm4SelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4HighFirstArmPc j))
        (amm4SelWord I) = ⟨0⟩) ∧
      UInt256.eq (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4HighFirstArmPc i))
        (amm4SelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = amm4SelBytes (i + 4) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [amm4HighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [amm4HighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

set_option maxRecDepth 2000000 in
theorem amm4LowPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (amm4SelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat amm4Bytecode amm4SplitPc) (amm4SelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : amm4SelWord I = ⟨157198259⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨404098525⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨599290589⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨1784838210⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x6a 0x62 0x78 0x42 _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide

set_option maxRecDepth 2000000 in
theorem amm4HighPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 5)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (amm4SelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat amm4Bytecode amm4SplitPc) (amm4SelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : amm4SelWord I = ⟨1838834698⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x6d 0x9a 0x64 0x0a _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨1889567281⟩ :=
      amm4SelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨3077966991⟩ :=
      amm4SelWord_eq_of_beq I hsz 0xb7 0x76 0x0c 0x8f _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨3714247998⟩ :=
      amm4SelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide
  · have hword : amm4SelWord I = ⟨4241707836⟩ :=
      amm4SelWord_eq_of_beq I hsz 0xfc 0xd3 0x53 0x3c _ (by decide)
        (by simpa [amm4SelBytes] using hsel)
    rw [hword]
    native_decide

set_option maxRecDepth 2000000 in
theorem amm4ReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) amm4SplitPc
      [amm4SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed amm4Bytecode amm4SplitPc := by
    solc_dispatch_prefix
  simpa [amm4SelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4ReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat amm4Bytecode amm4SplitPc) (amm4SelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat amm4Bytecode
        (nthArmPc amm4Bytecode amm4HighFirstArmPc j)) (amm4SelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat amm4Bytecode
      (nthArmPc amm4Bytecode amm4HighFirstArmPc i)) (amm4SelWord I) ≠ ⟨0⟩)
    (hjd : (D_J amm4Bytecode 0).contains bodyPC = true)
    (hbody : armTgt amm4Bytecode
      (nthArmPc amm4Bytecode amm4HighFirstArmPc i) = bodyPC) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [amm4SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed amm4Bytecode amm4SplitPc := by
    solc_dispatch_prefix
  simpa [amm4SelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := amm4Bytecode) (splitPc := amm4SplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) amm4SplitWellFormed
      (by simpa [amm4SelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [amm4HighFirstArmPc, amm4SplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          amm4HighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [amm4SelWord, solcSelectorWord, amm4HighFirstArmPc, amm4SplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using heq0 j hj)
      (by
        simpa [amm4SelWord, solcSelectorWord, amm4HighFirstArmPc, amm4SplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [amm4HighFirstArmPc, amm4SplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4ReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat amm4Bytecode amm4SplitPc) (amm4SelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat amm4Bytecode
        (nthArmPc amm4Bytecode amm4LowFirstArmPc j)) (amm4SelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat amm4Bytecode
      (nthArmPc amm4Bytecode amm4LowFirstArmPc i)) (amm4SelWord I) ≠ ⟨0⟩)
    (hjd : (D_J amm4Bytecode 0).contains bodyPC = true)
    (hbody : armTgt amm4Bytecode
      (nthArmPc amm4Bytecode amm4LowFirstArmPc i) = bodyPC) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
      [amm4SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed amm4Bytecode amm4SplitPc := by
    solc_dispatch_prefix
  simpa [amm4SelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := amm4Bytecode) (splitPc := amm4SplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) amm4SplitWellFormed
      (by simpa [amm4SelWord, solcSelectorWord] using hpivot)
      (by jump_dest) (by native_decide)
      (fun j hj => by
        simpa [amm4LowFirstArmPc, amm4LowJumpdestPc, amm4SplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          amm4LowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [amm4SelWord, solcSelectorWord, amm4LowFirstArmPc, amm4LowJumpdestPc,
          amm4SplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using heq0 j hj)
      (by
        simpa [amm4SelWord, solcSelectorWord, amm4LowFirstArmPc, amm4LowJumpdestPc,
          amm4SplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using htake)
      hjd
      (by
        simpa [amm4LowFirstArmPc, amm4LowJumpdestPc, amm4SplitPc, armTgt, pushAt,
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

end Benchmarks.ActAmm4
