import Benchmarks.Dss.End.Bytecode
import Benchmarks.Dss.End.RuntimeBlocks_001
import Benchmarks.Dss.End.RuntimeBlocks_002
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

/-! ## End-wide storage and ABI helpers -/

/-- Loading a full-slot DSS End `uint256` location returns the source integer for that word. -/
theorem endRuntimeStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

/-- Loading an address stored at byte offset 0 returns the low-160-bit address word. -/
theorem endRuntimeStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot)
      = .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

/-- ABI-encoding an End `uint256` return is exactly the returned word bytes. -/
theorem endUint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  simpa [uint256, uint256Int] using uint256ReturnEncoding v

/-- ABI-encoding an End `address` return is exactly solc's masked returned word. -/
theorem endAddressReturnEncoding (v : UInt256) :
    encodeReturnValue? addr
        (.address (AccountAddress.ofNat (UInt256.land v solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land v solcAddrMask)) := by
  simpa [addr] using solcAddressReturnEncoding (addrTy := addr) rfl v

/-! ## Selector bytes and dispatcher prefix -/

/-- The 4-byte function selector word computed by the deployed runtime. -/
abbrev endRuntimeSelWord (I : ExecutionEnv) : UInt256 := solcSelectorWord I

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev endSelectorMatches (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- DSS End selectors in `contract.transitions` order. -/
def endSelBytes : Nat → ByteArray
  | 0 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩
  | 1 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩
  | 2 => ⟨#[0xe4, 0x88, 0x18, 0x13]⟩
  | 3 => ⟨#[0xc3, 0xb3, 0xad, 0x7f]⟩
  | 4 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩
  | 5 => ⟨#[0x4b, 0xa2, 0x36, 0x3a]⟩
  | 6 => ⟨#[0x6f, 0x26, 0x5b, 0x93]⟩
  | 7 => ⟨#[0x84, 0x07, 0x82, 0xed]⟩
  | 8 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩
  | 9 => ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩
  | 10 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩
  | 11 => ⟨#[0x0d, 0xca, 0x59, 0xc1]⟩
  | 12 => ⟨#[0xee, 0x64, 0x47, 0xb5]⟩
  | 13 => ⟨#[0xe6, 0xee, 0x62, 0xaa]⟩
  | 14 => ⟨#[0xe1, 0x34, 0x0a, 0x3d]⟩
  | 15 => ⟨#[0x63, 0xfa, 0xd8, 0x5e]⟩
  | 16 => ⟨#[0x92, 0x55, 0xf8, 0x09]⟩
  | 17 => ⟨#[0xc9, 0x39, 0xeb, 0xfc]⟩
  | 18 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩
  | 19 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩
  | 20 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩
  | 21 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩
  | 22 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩
  | 23 => ⟨#[0xe2, 0x70, 0x2f, 0xdc]⟩
  | 24 => ⟨#[0x38, 0xc6, 0xde, 0x40]⟩
  | 25 => ⟨#[0x50, 0x3e, 0xcf, 0x06]⟩
  | 26 => ⟨#[0x89, 0xea, 0x45, 0xd3]⟩
  | 27 => ⟨#[0xc8, 0x30, 0x62, 0xc6]⟩
  | 28 => ⟨#[0x59, 0x20, 0x37, 0x5c]⟩
  | 29 => ⟨#[0x4a, 0x10, 0xea, 0xa6]⟩
  | 30 => ⟨#[0x6e, 0xa4, 0x25, 0x55]⟩
  | _ => ⟨#[0xfe, 0x85, 0x07, 0xc6]⟩

def endSelNat : Nat → UInt256
  | 0 => ⟨0xbf353dbb⟩
  | 1 => ⟨0x36569e77⟩
  | 2 => ⟨0xe4881813⟩
  | 3 => ⟨0xc3b3ad7f⟩
  | 4 => ⟨0x626cb3c5⟩
  | 5 => ⟨0x4ba2363a⟩
  | 6 => ⟨0x6f265b93⟩
  | 7 => ⟨0x840782ed⟩
  | 8 => ⟨0x957aa58c⟩
  | 9 => ⟨0xe2b0caef⟩
  | 10 => ⟨0x64bd7013⟩
  | 11 => ⟨0x0dca59c1⟩
  | 12 => ⟨0xee6447b5⟩
  | 13 => ⟨0xe6ee62aa⟩
  | 14 => ⟨0xe1340a3d⟩
  | 15 => ⟨0x63fad85e⟩
  | 16 => ⟨0x9255f809⟩
  | 17 => ⟨0xc939ebfc⟩
  | 18 => ⟨0x65fae35e⟩
  | 19 => ⟨0x9c52a7f1⟩
  | 20 => ⟨0xd4e8be83⟩
  | 21 => ⟨0x29ae8114⟩
  | 22 => ⟨0x69245009⟩
  | 23 => ⟨0xe2702fdc⟩
  | 24 => ⟨0x38c6de40⟩
  | 25 => ⟨0x503ecf06⟩
  | 26 => ⟨0x89ea45d3⟩
  | 27 => ⟨0xc83062c6⟩
  | 28 => ⟨0x5920375c⟩
  | 29 => ⟨0x4a10eaa6⟩
  | 30 => ⟨0x6ea42555⟩
  | _ => ⟨0xfe8507c6⟩

def endTransitionAt (i : Nat) (h : i < 32) : TransitionDecl :=
  transitions.get ⟨i, by simpa [transitions] using h⟩

/-- Trusted finite selector table for the 32 public End transitions. -/
axiom endRuntimeSelectorBytes_at (i : Nat) (h : i < 32) :
    selectorOf (endTransitionAt i h) = endSelBytes i

theorem endSelectorSizeAt (i : Nat) (h : i < 32) :
    (selectorOf (endTransitionAt i h)).size = 4 := by
  rw [endRuntimeSelectorBytes_at i h]
  interval_cases i <;> rfl

theorem endSelectorNomatchAt {cd : ByteArray}
    (hnm : ∀ i, i < 32 → (endSelBytes i == cd.extract 0 4) = false)
    (i : Nat) (h : i < 32) :
    (selectorOf (endTransitionAt i h) == cd.extract 0 4) = false := by
  rw [endRuntimeSelectorBytes_at i h]
  exact hnm i h

set_option maxHeartbeats 4000000 in
theorem endSelBytes_ne_of_ne (i j : Nat) (hi : i < 32) (hj : j < 32) (hij : i ≠ j) :
    (endSelBytes i == endSelBytes j) = false := by
  interval_cases i <;> interval_cases j <;> first | contradiction | native_decide

theorem endSelectorMiss_of_match {cd : ByteArray} (j i : Nat)
    (hj : j < 32) (hi : i < 32) (hji : j ≠ i)
    (hsel : (endSelBytes i == cd.extract 0 4) = true) :
    (endSelBytes j == cd.extract 0 4) = false := by
  have hcd : cd.extract 0 4 = endSelBytes i := (byteArray_eq_of_beq hsel).symm
  rw [hcd]
  exact endSelBytes_ne_of_ne j i hj hi hji

-- LIBRARY CANDIDATE: generic indexed positive dispatch for `Reasoning.Dispatch.dispatchList`.
theorem dispatchList_eq_some_getElem
    {ts : List TransitionDecl} {cd : ByteArray} {i : Nat} (hi : i < ts.length)
    (hpre : ∀ j (hj : j < ts.length), j < i →
      (selectorOf (ts.get ⟨j, hj⟩) == cd.extract 0 4) = false)
    (hhit : (selectorOf (ts.get ⟨i, hi⟩) == cd.extract 0 4) = true) :
    dispatchList ts cd = some (ts.get ⟨i, hi⟩) := by
  induction ts generalizing i with
  | nil => cases hi
  | cons t ts ih =>
      cases i with
      | zero =>
          rw [dispatchList_cons, if_pos (by simpa using hhit)]
          simp
      | succ i =>
          rw [dispatchList_cons, if_neg]
          · have hiTail : i < ts.length := by simpa using hi
            exact ih hiTail
              (fun j hj hji => by
                have hjCons : j.succ < (t :: ts).length := by simpa using Nat.succ_lt_succ hj
                simpa using hpre j.succ hjCons (Nat.succ_lt_succ hji))
              (by simpa using hhit)
          · have h0 : (0 : Nat) < Nat.succ i := by omega
            have h0len : 0 < (t :: ts).length := by simp
            simpa using hpre 0 h0len h0

theorem endDispatch_at {cd : ByteArray} (i : Nat) (hi : i < 32)
    (hsel : (endSelBytes i == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some (endTransitionAt i hi) := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList transitions cd = some (endTransitionAt i hi)
  have hiLen : i < transitions.length := by simpa [transitions] using hi
  have hpre : ∀ j (hj : j < transitions.length), j < i →
      (selectorOf (transitions.get ⟨j, hj⟩) == cd.extract 0 4) = false := by
    intro j hj hji
    have hj32 : j < 32 := by simpa [transitions] using hj
    have hs : selectorOf (transitions.get ⟨j, hj⟩) = endSelBytes j := by
      simpa [endTransitionAt] using endRuntimeSelectorBytes_at j hj32
    rw [hs]
    exact endSelectorMiss_of_match j i hj32 hi (by omega) hsel
  have hhit : (selectorOf (transitions.get ⟨i, hiLen⟩) == cd.extract 0 4) = true := by
    have hs : selectorOf (transitions.get ⟨i, hiLen⟩) = endSelBytes i := by
      simpa [endTransitionAt] using endRuntimeSelectorBytes_at i hi
    rw [hs]
    exact hsel
  simpa [endTransitionAt] using dispatchList_eq_some_getElem (ts := transitions) hiLen hpre hhit

theorem endSelectorMatches_size {I : ExecutionEnv} (i : Nat) (hi : i < 32)
    (hsel : endSelectorMatches I (endSelBytes i)) :
    4 ≤ I.calldata.size := by
  exact calldata_size_ge_of_selIs I (endSelBytes i)
    (by interval_cases i <;> rfl) hsel

theorem endDecode_noArgs {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

/-- If the calldata prefix matches a selector literal, the EVM selector word is that literal. -/
theorem endSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : Nat) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    endRuntimeSelWord I = sel := by
  simpa [endRuntimeSelWord] using solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

set_option maxHeartbeats 4000000 in
theorem endSelWord_eq_at (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : Nat) (hi : i < 32) (hsel : endSelectorMatches I (endSelBytes i)) :
    endRuntimeSelWord I = endSelNat i := by
  interval_cases i <;>
    simpa [endRuntimeSelWord, solcSelectorWord, endSelBytes, endSelNat] using
      (endSelWord_eq_of_beq I hsz _ _ _ _ _ (by native_decide) hsel)

/-- Standard solc prologue/guards/selector-load, stopping at End's top-level pivot split. -/
theorem endReachTopSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨32⟩
        [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simpa [endRuntimeSelWord, solcSelectorWord] using
    (solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (code := endBytecode)
      (bodyPc := ⟨18⟩) (loadPc := ⟨26⟩) (firstPc := ⟨32⟩)
      (guardTgt := ⟨16⟩) (revertTgt := ⟨496⟩)
      (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

/-! ## Shared revert obligations -/

/-- No calldata shorter than four bytes can dispatch to an End function. -/
theorem endDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList transitions cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp only [transitions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 0 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 1 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 2 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 3 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 4 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 5 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 6 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 7 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 8 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 9 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 10 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 11 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 12 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 13 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 14 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 15 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 16 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 17 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 18 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 19 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 20 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 21 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 22 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 23 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 24 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 25 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 26 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 27 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 28 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 29 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 30 (by omega)
    · simpa [endTransitionAt, transitions] using endSelectorSizeAt 31 (by omega)) h

set_option maxHeartbeats 2000000 in
/-- If all End selectors miss, `dispatchMsg` returns `none`. -/
theorem endDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 32 → (endSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  change t ∈ transitions at ht
  simp only [transitions, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 0 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 1 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 2 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 3 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 4 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 5 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 6 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 7 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 8 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 9 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 10 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 11 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 12 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 13 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 14 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 15 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 16 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 17 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 18 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 19 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 20 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 21 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 22 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 23 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 24 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 25 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 26 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 27 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 28 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 29 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 30 (by omega)
  · simpa [endTransitionAt, transitions] using endSelectorNomatchAt hnm 31 (by omega)

set_option maxHeartbeats 2000000 in
/-- Every End transition body reverts when the non-payable guard sees non-zero callvalue. -/
theorem endBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  change t ∈ transitions at ht
  simp only [transitions, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-- EVM non-payable guard reverts when `callvalue ≠ 0`. -/
theorem endX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd0 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  obtain ⟨_, _, _, rd12⟩ :=
    endRuntimeBlocks.endRuntime_block_0_fallthrough_packed (R := [])
      (by simp) (isZero_eq_zero_of_ne hwv) rd0
  exact endRuntimeBlocks.endRuntime_block_12 (R := [I.weiValue])
    (by simp) (by simpa [endRuntimeBlocks.endRuntime_block_0_fallthrough_stack] using rd12)

/-- EVM calldata-size guard reverts when calldata is shorter than a selector. -/
theorem endX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd0 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RD.initState hcode
  obtain ⟨_, _, _, rd16⟩ :=
    endRuntimeBlocks.endRuntime_block_0_taken_packed (R := [])
      (by simp) (by rw [hwv]; decide) (by jump_dest) rd0
  obtain ⟨_, _, _, rd496⟩ :=
    endRuntimeBlocks.endRuntime_block_16_taken_packed (x0 := I.weiValue) (R := [])
      (by simp) (lt_four_ne_zero_of_lt hsz) (by jump_dest) rd16
  exact endRuntimeBlocks.endRuntime_block_496 (R := [])
    (by simp) (by simpa [endRuntimeBlocks.endRuntime_block_16_taken_stack] using rd496)

/-- `callvalue ≠ 0` makes the shared non-payable guard revert on both sides. -/
theorem endNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (endBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector reverts before selector dispatch. -/
theorem endShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (_hsize : I.calldata.size < UInt256.size) (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (endDispatch_none_short hsz)

end Benchmarks.Dss.End
