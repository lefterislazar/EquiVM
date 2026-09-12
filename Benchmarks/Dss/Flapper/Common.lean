import Benchmarks.Dss.Flapper.Bytecode
import Benchmarks.Dss.Flapper.RuntimeBlocks_001
import Benchmarks.Dss.Flapper.RuntimeBlocks_002
import Benchmarks.Dss.Flapper.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flapper

/-!
# Flapper shared proof foundation

Dispatcher facts and global entry traces for the optimizer-on binary selector tree.
-/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev flapperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def flapperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ -- beg
  | 1 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ -- bids
  | 2 => ⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ -- cage
  | 3 => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ -- deal
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny
  | 5 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file
  | 6 => ⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩ -- fill
  | 7 => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ -- gem
  | 8 => ⟨#[0xca, 0x40, 0xc4, 0x19]⟩ -- kick
  | 9 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks
  | 10 => ⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ -- lid
  | 11 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live
  | 12 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely
  | 13 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau
  | 14 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend
  | 15 => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ -- tick
  | 16 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl
  | 17 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat
  | 18 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ -- yank

def flapperBodyPc : ℕ → UInt256
  | 0 => ⟨646⟩ -- beg
  | 1 => ⟨433⟩ -- bids
  | 2 => ⟨700⟩ -- cage
  | 3 => ⟨767⟩ -- deal
  | 4 => ⟨662⟩ -- deny
  | 5 => ⟨362⟩ -- file
  | 6 => ⟨847⟩ -- fill
  | 7 => ⟨638⟩ -- gem
  | 8 => ⟨796⟩ -- kick
  | 9 => ⟨839⟩ -- kicks
  | 10 => ⟨305⟩ -- lid
  | 11 => ⟨654⟩ -- live
  | 12 => ⟨600⟩ -- rely
  | 13 => ⟨831⟩ -- tau
  | 14 => ⟨524⟩ -- tend
  | 15 => ⟨855⟩ -- tick
  | 16 => ⟨565⟩ -- ttl
  | 17 => ⟨397⟩ -- vat
  | 18 => ⟨729⟩ -- wards
  | _ => ⟨331⟩ -- yank

theorem flapperSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat) :
    UInt256.eq sel (flapperSelWord I) =
      if ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) then
        ⟨1⟩
      else
        ⟨0⟩ := by
  simpa [flapperSelWord] using evmSelectorDecode (cd := I.calldata) hsz c0 c1 c2 c3 sel hsel

theorem flapperSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    flapperSelWord I = sel := by
  simpa [flapperSelWord] using solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem flapperSubRet32_toNat :
    (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  decide

def flapperScalarReturnBytes (v : UInt256) : ByteArray :=
  ((v.toByteArray.write 0 solcFreePtrMem
      (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32).readWithPadding
    (memLoad (UInt256.ofNat 64)
      (v.toByteArray.write 0 solcFreePtrMem
        (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32)).toNat
    (UInt256.ofNat 32 +
      (memLoad (UInt256.ofNat 64) solcFreePtrMem).sub
        (memLoad (UInt256.ofNat 64)
          (v.toByteArray.write 0 solcFreePtrMem
            (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32))).toNat)

@[simp] theorem flapperScalarReturnBytes_eq (v : UInt256) :
    flapperScalarReturnBytes v = UInt256.toByteArray v := by
  rw [flapperScalarReturnBytes]
  rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 by
    simpa [memLoad] using solcFreePtrMem_mload64]
  change (solcReturnMem v).readWithPadding
      (memLoad (UInt256.ofNat 64) (solcReturnMem v)).toNat
      (UInt256.ofNat 32 + (UInt256.ofNat 128).sub
        (memLoad (UInt256.ofNat 64) (solcReturnMem v))).toNat =
    UInt256.toByteArray v
  rw [show memLoad (UInt256.ofNat 64) (solcReturnMem v) = UInt256.ofNat 128 by
    simpa [memLoad] using solcReturnMem_mload64 v]
  rw [show (UInt256.ofNat 32 + (UInt256.ofNat 128).sub (UInt256.ofNat 128)).toNat = 32 by
    decide]
  exact solcReturnMem_read128 v

abbrev flapperAddressMask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)

@[simp] theorem flapperAddressMask_eq_solcAddrMask :
    flapperAddressMask = solcAddrMask := by
  decide

theorem flapperAddressMask_clean (w : UInt256) :
    UInt256.land (UInt256.land flapperAddressMask w) flapperAddressMask =
      UInt256.land w solcAddrMask := by
  rw [flapperAddressMask_eq_solcAddrMask]
  rw [u256_land_comm solcAddrMask w]
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

theorem flapperSolcAddrMask_clean (w : UInt256) :
    UInt256.land (UInt256.land solcAddrMask w) solcAddrMask =
      UInt256.land w solcAddrMask := by
  rw [u256_land_comm solcAddrMask w]
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

abbrev flapperUint48Mask : UInt256 :=
  UInt256.ofNat 281474976710655

abbrev flapperUint48Shift : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)

@[simp] theorem flapperUint48Shift_eq_pow :
    flapperUint48Shift = UInt256.ofNat (256 ^ 6) := by
  decide

theorem flapperUint48Mask_clean (w : UInt256) :
    UInt256.land (UInt256.land flapperUint48Mask w) flapperUint48Mask =
      UInt256.land w flapperUint48Mask := by
  apply u256_inj
  repeat rw [uland_toNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  simp [Bool.and_left_comm, Bool.and_comm]

theorem flapperUint48Word_lt (w : UInt256) :
    (UInt256.land w flapperUint48Mask).toNat < EVM.twoPow 48 := by
  rw [uland_toNat]
  have hle := nat_land_le_right w.toNat flapperUint48Mask.toNat
  exact lt_of_le_of_lt hle (by decide)

theorem flapperUint48ReturnEncoding (v : UInt256)
    (h48 : v.toNat < EVM.twoPow 48) :
    encodeReturnValue? (.elem (.int uint48Int)) (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  refine scalarReturnEncoding (t := .int uint48Int) (w := v) rfl ?_ ?_
  · simp only [uint48Int, abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType,
      bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, uint48Int, hword, h48]

theorem flapperStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem flapperStorageLocLoad_address (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem flapperStorageLocLoad_uint48_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask, uint48Int] using
    storageLocLoad_uint_offset0 evm slot ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide)

theorem flapperStorageLocLoad_uint48_offset6 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨6, by decide⟩ (by decide)) =
      .int (Int.ofNat
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            flapperUint48Shift)
          flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask, flapperUint48Shift, uint48Int] using
    storageLocLoad_uint_offset evm slot ⟨6, by decide⟩ ⟨6, by decide⟩
      ⟨48, by decide⟩ (hbound := by decide) (by decide) (by decide)

/-! ## Body reachability placeholders -/

abbrev FlapperBodyReach
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    (g : UInt256) (bodyPC : UInt256) : Prop :=
  ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
    (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) bodyPC
    [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
    (cA, σ) k C

theorem flapperReachDispatchLoad
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨26⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g) hcode (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h8 := h0.push2 (UInt256.ofNat 16) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h16 := h8.jumpiT (by native_decide) (by rw [hwv]; decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, flapperRuntimeBlocks.flapperRuntime_block_16_fallthrough
    (x0 := I.weiValue) (R := [])
    (by simp only [List.length_nil]; omega)
    (lt_four_eq_zero_of_ge hsz hsize)
    h16⟩

theorem flapperReachBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (i : ℕ) (hi : i < 20)
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes i)) :
    FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) g (flapperBodyPc i) := by
  obtain ⟨_, _, h26⟩ := flapperReachDispatchLoad (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  interval_cases i
  · have hmatch : ((⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 2105019778 :=
      flapperSelWord_eq_of_beq I hsz 0x7d 0x78 0x0d 0x82
        (UInt256.ofNat 2105019778) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss14 : UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss16 : UInt256.eq (UInt256.ofNat 1317739989) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss12 : UInt256.eq (UInt256.ofNat 1710941022) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss7 : UInt256.eq (UInt256.ofNat 2077408935) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 2105019778) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h185 := flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h173
    have h196 := flapperRuntimeBlocks.flapperRuntime_block_185_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss14 h185
    have h207 := flapperRuntimeBlocks.flapperRuntime_block_196_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss16 h196
    have h218 := flapperRuntimeBlocks.flapperRuntime_block_207_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss12 h207
    have h229 := flapperRuntimeBlocks.flapperRuntime_block_218_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss7 h218
    have h646 := flapperRuntimeBlocks.flapperRuntime_block_229_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h229
    exact ⟨_, _, h646⟩
  · have hmatch : ((⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 1143195121 :=
      flapperSelWord_eq_of_beq I hsz 0x44 0x23 0xc5 0xf1
        (UInt256.ofNat 1143195121) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss10 : UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss19 : UInt256.eq (UInt256.ofNat 652224497) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss5 : UInt256.eq (UInt256.ofNat 699302164) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss17 : UInt256.eq (UInt256.ofNat 911646327) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 1143195121) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h244 := flapperRuntimeBlocks.flapperRuntime_block_173_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h173
    have h256 := flapperRuntimeBlocks.flapperRuntime_block_244_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss10 h244
    have h267 := flapperRuntimeBlocks.flapperRuntime_block_256_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss19 h256
    have h278 := flapperRuntimeBlocks.flapperRuntime_block_267_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss5 h267
    have h289 := flapperRuntimeBlocks.flapperRuntime_block_278_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss17 h278
    have h433 := flapperRuntimeBlocks.flapperRuntime_block_289_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h289
    exact ⟨_, _, h433⟩
  · have hmatch : ((⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 2734234354 :=
      flapperSelWord_eq_of_beq I hsz 0xa2 0xf9 0x1a 0xf2
        (UInt256.ofNat 2734234354) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss11 : UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss4 : UInt256.eq (UInt256.ofNat 2622662641) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 2734234354) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h113 := flapperRuntimeBlocks.flapperRuntime_block_43_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h43
    have h125 := flapperRuntimeBlocks.flapperRuntime_block_113_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss11 h113
    have h136 := flapperRuntimeBlocks.flapperRuntime_block_125_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss4 h125
    have h700 := flapperRuntimeBlocks.flapperRuntime_block_136_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h136
    exact ⟨_, _, h700⟩
  · have hmatch : ((⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3378103339 :=
      flapperSelWord_eq_of_beq I hsz 0xc9 0x59 0xc4 0x2b
        (UInt256.ofNat 3378103339) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss11 : UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss4 : UInt256.eq (UInt256.ofNat 2622662641) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss2 : UInt256.eq (UInt256.ofNat 2734234354) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss18 : UInt256.eq (UInt256.ofNat 3207937467) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3378103339) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h113 := flapperRuntimeBlocks.flapperRuntime_block_43_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h43
    have h125 := flapperRuntimeBlocks.flapperRuntime_block_113_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss11 h113
    have h136 := flapperRuntimeBlocks.flapperRuntime_block_125_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss4 h125
    have h147 := flapperRuntimeBlocks.flapperRuntime_block_136_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss2 h136
    have h158 := flapperRuntimeBlocks.flapperRuntime_block_147_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss18 h147
    have h767 := flapperRuntimeBlocks.flapperRuntime_block_158_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h158
    exact ⟨_, _, h767⟩
  · have hmatch : ((⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 2622662641 :=
      flapperSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1
        (UInt256.ofNat 2622662641) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss11 : UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 2622662641) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h113 := flapperRuntimeBlocks.flapperRuntime_block_43_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h43
    have h125 := flapperRuntimeBlocks.flapperRuntime_block_113_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss11 h113
    have h662 := flapperRuntimeBlocks.flapperRuntime_block_125_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h125
    exact ⟨_, _, h662⟩
  · have hmatch : ((⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 699302164 :=
      flapperSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14
        (UInt256.ofNat 699302164) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss10 : UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss19 : UInt256.eq (UInt256.ofNat 652224497) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 699302164) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h244 := flapperRuntimeBlocks.flapperRuntime_block_173_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h173
    have h256 := flapperRuntimeBlocks.flapperRuntime_block_244_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss10 h244
    have h267 := flapperRuntimeBlocks.flapperRuntime_block_256_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss19 h256
    have h362 := flapperRuntimeBlocks.flapperRuntime_block_267_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h267
    exact ⟨_, _, h362⟩
  · have hmatch : ((⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3653590241 :=
      flapperSelWord_eq_of_beq I hsz 0xd9 0xc5 0x5c 0xe1
        (UInt256.ofNat 3653590241) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss8 : UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss13 : UInt256.eq (UInt256.ofNat 3485773653) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss9 : UInt256.eq (UInt256.ofNat 3487380226) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3653590241) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h54 := flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h43
    have h65 := flapperRuntimeBlocks.flapperRuntime_block_54_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss8 h54
    have h76 := flapperRuntimeBlocks.flapperRuntime_block_65_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss13 h65
    have h87 := flapperRuntimeBlocks.flapperRuntime_block_76_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss9 h76
    have h847 := flapperRuntimeBlocks.flapperRuntime_block_87_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h87
    exact ⟨_, _, h847⟩
  · have hmatch : ((⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 2077408935 :=
      flapperSelWord_eq_of_beq I hsz 0x7b 0xd2 0xbe 0xa7
        (UInt256.ofNat 2077408935) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss14 : UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss16 : UInt256.eq (UInt256.ofNat 1317739989) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss12 : UInt256.eq (UInt256.ofNat 1710941022) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 2077408935) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h185 := flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h173
    have h196 := flapperRuntimeBlocks.flapperRuntime_block_185_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss14 h185
    have h207 := flapperRuntimeBlocks.flapperRuntime_block_196_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss16 h196
    have h218 := flapperRuntimeBlocks.flapperRuntime_block_207_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss12 h207
    have h638 := flapperRuntimeBlocks.flapperRuntime_block_218_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h218
    exact ⟨_, _, h638⟩
  · have hmatch : ((⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3393242137 :=
      flapperSelWord_eq_of_beq I hsz 0xca 0x40 0xc4 0x19
        (UInt256.ofNat 3393242137) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h54 := flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h43
    have h796 := flapperRuntimeBlocks.flapperRuntime_block_54_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h54
    exact ⟨_, _, h796⟩
  · have hmatch : ((⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3487380226 :=
      flapperSelWord_eq_of_beq I hsz 0xcf 0xdd 0x33 0x02
        (UInt256.ofNat 3487380226) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss8 : UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss13 : UInt256.eq (UInt256.ofNat 3485773653) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3487380226) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h54 := flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h43
    have h65 := flapperRuntimeBlocks.flapperRuntime_block_54_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss8 h54
    have h76 := flapperRuntimeBlocks.flapperRuntime_block_65_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss13 h65
    have h839 := flapperRuntimeBlocks.flapperRuntime_block_76_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h76
    exact ⟨_, _, h839⟩
  · have hmatch : ((⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 651341276 :=
      flapperSelWord_eq_of_beq I hsz 0x26 0xd2 0xad 0xdc
        (UInt256.ofNat 651341276) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h244 := flapperRuntimeBlocks.flapperRuntime_block_173_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h173
    have h305 := flapperRuntimeBlocks.flapperRuntime_block_244_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h244
    exact ⟨_, _, h305⟩
  · have hmatch : ((⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 2507842956 :=
      flapperSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c
        (UInt256.ofNat 2507842956) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h113 := flapperRuntimeBlocks.flapperRuntime_block_43_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h43
    have h654 := flapperRuntimeBlocks.flapperRuntime_block_113_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h113
    exact ⟨_, _, h654⟩
  · have hmatch : ((⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 1710941022 :=
      flapperSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e
        (UInt256.ofNat 1710941022) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss14 : UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss16 : UInt256.eq (UInt256.ofNat 1317739989) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 1710941022) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h185 := flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h173
    have h196 := flapperRuntimeBlocks.flapperRuntime_block_185_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss14 h185
    have h207 := flapperRuntimeBlocks.flapperRuntime_block_196_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss16 h196
    have h600 := flapperRuntimeBlocks.flapperRuntime_block_207_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h207
    exact ⟨_, _, h600⟩
  · have hmatch : ((⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3485773653 :=
      flapperSelWord_eq_of_beq I hsz 0xcf 0xc4 0xaf 0x55
        (UInt256.ofNat 3485773653) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss8 : UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3485773653) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h54 := flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h43
    have h65 := flapperRuntimeBlocks.flapperRuntime_block_54_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss8 h54
    have h831 := flapperRuntimeBlocks.flapperRuntime_block_65_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h65
    exact ⟨_, _, h831⟩
  · have hmatch : ((⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 1262742802 :=
      flapperSelWord_eq_of_beq I hsz 0x4b 0x43 0xed 0x12
        (UInt256.ofNat 1262742802) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h185 := flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h173
    have h524 := flapperRuntimeBlocks.flapperRuntime_block_185_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h185
    exact ⟨_, _, h524⟩
  · have hmatch : ((⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 4235946734 :=
      flapperSelWord_eq_of_beq I hsz 0xfc 0x7b 0x6a 0xee
        (UInt256.ofNat 4235946734) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss8 : UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss13 : UInt256.eq (UInt256.ofNat 3485773653) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss9 : UInt256.eq (UInt256.ofNat 3487380226) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss6 : UInt256.eq (UInt256.ofNat 3653590241) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 4235946734) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h54 := flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h43
    have h65 := flapperRuntimeBlocks.flapperRuntime_block_54_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss8 h54
    have h76 := flapperRuntimeBlocks.flapperRuntime_block_65_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss13 h65
    have h87 := flapperRuntimeBlocks.flapperRuntime_block_76_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss9 h76
    have h98 := flapperRuntimeBlocks.flapperRuntime_block_87_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss6 h87
    have h855 := flapperRuntimeBlocks.flapperRuntime_block_98_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h98
    exact ⟨_, _, h855⟩
  · have hmatch : ((⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 1317739989 :=
      flapperSelWord_eq_of_beq I hsz 0x4e 0x8b 0x1d 0xd5
        (UInt256.ofNat 1317739989) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss14 : UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 1317739989) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h185 := flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit h173
    have h196 := flapperRuntimeBlocks.flapperRuntime_block_185_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss14 h185
    have h565 := flapperRuntimeBlocks.flapperRuntime_block_196_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h196
    exact ⟨_, _, h565⟩
  · have hmatch : ((⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 911646327 :=
      flapperSelWord_eq_of_beq I hsz 0x36 0x56 0x9e 0x77
        (UInt256.ofNat 911646327) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss10 : UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss19 : UInt256.eq (UInt256.ofNat 652224497) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss5 : UInt256.eq (UInt256.ofNat 699302164) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 911646327) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h244 := flapperRuntimeBlocks.flapperRuntime_block_173_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h173
    have h256 := flapperRuntimeBlocks.flapperRuntime_block_244_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss10 h244
    have h267 := flapperRuntimeBlocks.flapperRuntime_block_256_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss19 h256
    have h278 := flapperRuntimeBlocks.flapperRuntime_block_267_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss5 h267
    have h397 := flapperRuntimeBlocks.flapperRuntime_block_278_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h278
    exact ⟨_, _, h397⟩
  · have hmatch : ((⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 3207937467 :=
      flapperSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb
        (UInt256.ofNat 3207937467) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss11 : UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss4 : UInt256.eq (UInt256.ofNat 2622662641) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss2 : UInt256.eq (UInt256.ofNat 2734234354) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 3207937467) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h43 := flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) h26
    have h113 := flapperRuntimeBlocks.flapperRuntime_block_43_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h43
    have h125 := flapperRuntimeBlocks.flapperRuntime_block_113_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss11 h113
    have h136 := flapperRuntimeBlocks.flapperRuntime_block_125_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss4 h125
    have h147 := flapperRuntimeBlocks.flapperRuntime_block_136_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss2 h136
    have h729 := flapperRuntimeBlocks.flapperRuntime_block_147_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h147
    exact ⟨_, _, h729⟩
  · have hmatch : ((⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = true := by
      simpa [selIs, flapperSelBytes] using hsel
    have hword : flapperSelWord I = UInt256.ofNat 652224497 :=
      flapperSelWord_eq_of_beq I hsz 0x26 0xe0 0x27 0xf1
        (UInt256.ofNat 652224497) (by decide) hmatch
    have hroot : UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hsplit : UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have hmiss10 : UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) =
        UInt256.ofNat 0 := by rw [hword]; decide
    have hhit : UInt256.eq (UInt256.ofNat 652224497) (flapperSelWord I) ≠
        UInt256.ofNat 0 := by rw [hword]; decide
    have h173 := flapperRuntimeBlocks.flapperRuntime_block_26_taken
      (R := []) (by simp only [List.length_nil]; omega)
      (by simpa [flapperSelWord] using hroot) (by jump_dest) h26
    have h244 := flapperRuntimeBlocks.flapperRuntime_block_173_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hsplit (by jump_dest) h173
    have h256 := flapperRuntimeBlocks.flapperRuntime_block_244_fallthrough
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hmiss10 h244
    have h331 := flapperRuntimeBlocks.flapperRuntime_block_256_taken
      (x0 := flapperSelWord I) (R := []) (by simp only [List.length_nil]; omega)
      hhit (by jump_dest) h256
    exact ⟨_, _, h331⟩

/-! ## Dispatch failures and global non-payable guard -/

theorem flapperDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  exact dispatchList_none_short _ (by
    intro t ht
    simp [contract, transitions] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes]; rfl
    · rw [flapperBidsSelectorBytes]; rfl
    · rw [flapperCageSelectorBytes]; rfl
    · rw [flapperDealSelectorBytes]; rfl
    · rw [flapperDenySelectorBytes]; rfl
    · rw [flapperFileSelectorBytes]; rfl
    · rw [flapperFillSelectorBytes]; rfl
    · rw [flapperGemSelectorBytes]; rfl
    · rw [flapperKickSelectorBytes]; rfl
    · rw [flapperKicksSelectorBytes]; rfl
    · rw [flapperLidSelectorBytes]; rfl
    · rw [flapperLiveSelectorBytes]; rfl
    · rw [flapperRelySelectorBytes]; rfl
    · rw [flapperTauSelectorBytes]; rfl
    · rw [flapperTendSelectorBytes]; rfl
    · rw [flapperTickSelectorBytes]; rfl
    · rw [flapperTtlSelectorBytes]; rfl
    · rw [flapperVatSelectorBytes]; rfl
    · rw [flapperWardsSelectorBytes]; rfl
    · rw [flapperYankSelectorBytes]; rfl) h

theorem flapperDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (contract := contract) (cd := cd) (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [flapperBegSelectorBytes]
    simpa [flapperSelBytes] using hnm 0 (by omega)
  · rw [flapperBidsSelectorBytes]
    simpa [flapperSelBytes] using hnm 1 (by omega)
  · rw [flapperCageSelectorBytes]
    simpa [flapperSelBytes] using hnm 2 (by omega)
  · rw [flapperDealSelectorBytes]
    simpa [flapperSelBytes] using hnm 3 (by omega)
  · rw [flapperDenySelectorBytes]
    simpa [flapperSelBytes] using hnm 4 (by omega)
  · rw [flapperFileSelectorBytes]
    simpa [flapperSelBytes] using hnm 5 (by omega)
  · rw [flapperFillSelectorBytes]
    simpa [flapperSelBytes] using hnm 6 (by omega)
  · rw [flapperGemSelectorBytes]
    simpa [flapperSelBytes] using hnm 7 (by omega)
  · rw [flapperKickSelectorBytes]
    simpa [flapperSelBytes] using hnm 8 (by omega)
  · rw [flapperKicksSelectorBytes]
    simpa [flapperSelBytes] using hnm 9 (by omega)
  · rw [flapperLidSelectorBytes]
    simpa [flapperSelBytes] using hnm 10 (by omega)
  · rw [flapperLiveSelectorBytes]
    simpa [flapperSelBytes] using hnm 11 (by omega)
  · rw [flapperRelySelectorBytes]
    simpa [flapperSelBytes] using hnm 12 (by omega)
  · rw [flapperTauSelectorBytes]
    simpa [flapperSelBytes] using hnm 13 (by omega)
  · rw [flapperTendSelectorBytes]
    simpa [flapperSelBytes] using hnm 14 (by omega)
  · rw [flapperTickSelectorBytes]
    simpa [flapperSelBytes] using hnm 15 (by omega)
  · rw [flapperTtlSelectorBytes]
    simpa [flapperSelBytes] using hnm 16 (by omega)
  · rw [flapperVatSelectorBytes]
    simpa [flapperSelBytes] using hnm 17 (by omega)
  · rw [flapperWardsSelectorBytes]
    simpa [flapperSelBytes] using hnm 18 (by omega)
  · rw [flapperYankSelectorBytes]
    simpa [flapperSelBytes] using hnm 19 (by omega)

theorem flapperBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem flapperX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h8 := h0.push2 (UInt256.ofNat 16) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h12 := h8.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact flapperRuntimeBlocks.flapperRuntime_block_12
    (R := [I.weiValue])
    (by simp only [List.length_cons, List.length_nil]; omega)
    h12

theorem flapperX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h8 := h0.push2 (UInt256.ofNat 16) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h16 := h8.jumpiT (by native_decide) (by rw [hwv]; decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h300 := flapperRuntimeBlocks.flapperRuntime_block_16_taken
    (x0 := I.weiValue) (R := [])
    (by simp only [List.length_nil]; omega)
    (lt_four_ne_zero_of_lt hsz)
    (by jump_dest)
    h16
  exact flapperRuntimeBlocks.flapperRuntime_block_300
    (R := [])
    (by simp only [List.length_nil]; omega)
    h300

theorem flapperX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have h8 := h0.push2 (UInt256.ofNat 16) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h16 := h8.jumpiT (by native_decide) (by rw [hwv]; decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, _, h26⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_16_fallthrough_packed
      (x0 := I.weiValue) (R := [])
      (by simp only [List.length_nil]; omega)
      (lt_four_eq_zero_of_ge hsz hsize)
      h16
  have heq0 :
      UInt256.eq (UInt256.ofNat 2105019778) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 0 (by omega)
    rw [flapperSelectorEq I hsz 0x7d 0x78 0x0d 0x82 (UInt256.ofNat 2105019778)
      (by decide), hfalse]
    rfl
  have heq1 :
      UInt256.eq (UInt256.ofNat 1143195121) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 1 (by omega)
    rw [flapperSelectorEq I hsz 0x44 0x23 0xc5 0xf1 (UInt256.ofNat 1143195121)
      (by decide), hfalse]
    rfl
  have heq2 :
      UInt256.eq (UInt256.ofNat 2734234354) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 2 (by omega)
    rw [flapperSelectorEq I hsz 0xa2 0xf9 0x1a 0xf2 (UInt256.ofNat 2734234354)
      (by decide), hfalse]
    rfl
  have heq3 :
      UInt256.eq (UInt256.ofNat 3378103339) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 3 (by omega)
    rw [flapperSelectorEq I hsz 0xc9 0x59 0xc4 0x2b (UInt256.ofNat 3378103339)
      (by decide), hfalse]
    rfl
  have heq4 :
      UInt256.eq (UInt256.ofNat 2622662641) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 4 (by omega)
    rw [flapperSelectorEq I hsz 0x9c 0x52 0xa7 0xf1 (UInt256.ofNat 2622662641)
      (by decide), hfalse]
    rfl
  have heq5 :
      UInt256.eq (UInt256.ofNat 699302164) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 5 (by omega)
    rw [flapperSelectorEq I hsz 0x29 0xae 0x81 0x14 (UInt256.ofNat 699302164)
      (by decide), hfalse]
    rfl
  have heq6 :
      UInt256.eq (UInt256.ofNat 3653590241) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 6 (by omega)
    rw [flapperSelectorEq I hsz 0xd9 0xc5 0x5c 0xe1 (UInt256.ofNat 3653590241)
      (by decide), hfalse]
    rfl
  have heq7 :
      UInt256.eq (UInt256.ofNat 2077408935) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 7 (by omega)
    rw [flapperSelectorEq I hsz 0x7b 0xd2 0xbe 0xa7 (UInt256.ofNat 2077408935)
      (by decide), hfalse]
    rfl
  have heq8 :
      UInt256.eq (UInt256.ofNat 3393242137) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xca, 0x40, 0xc4, 0x19]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 8 (by omega)
    rw [flapperSelectorEq I hsz 0xca 0x40 0xc4 0x19 (UInt256.ofNat 3393242137)
      (by decide), hfalse]
    rfl
  have heq9 :
      UInt256.eq (UInt256.ofNat 3487380226) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 9 (by omega)
    rw [flapperSelectorEq I hsz 0xcf 0xdd 0x33 0x02 (UInt256.ofNat 3487380226)
      (by decide), hfalse]
    rfl
  have heq10 :
      UInt256.eq (UInt256.ofNat 651341276) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 10 (by omega)
    rw [flapperSelectorEq I hsz 0x26 0xd2 0xad 0xdc (UInt256.ofNat 651341276)
      (by decide), hfalse]
    rfl
  have heq11 :
      UInt256.eq (UInt256.ofNat 2507842956) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 11 (by omega)
    rw [flapperSelectorEq I hsz 0x95 0x7a 0xa5 0x8c (UInt256.ofNat 2507842956)
      (by decide), hfalse]
    rfl
  have heq12 :
      UInt256.eq (UInt256.ofNat 1710941022) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 12 (by omega)
    rw [flapperSelectorEq I hsz 0x65 0xfa 0xe3 0x5e (UInt256.ofNat 1710941022)
      (by decide), hfalse]
    rfl
  have heq13 :
      UInt256.eq (UInt256.ofNat 3485773653) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 13 (by omega)
    rw [flapperSelectorEq I hsz 0xcf 0xc4 0xaf 0x55 (UInt256.ofNat 3485773653)
      (by decide), hfalse]
    rfl
  have heq14 :
      UInt256.eq (UInt256.ofNat 1262742802) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x4b, 0x43, 0xed, 0x12]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 14 (by omega)
    rw [flapperSelectorEq I hsz 0x4b 0x43 0xed 0x12 (UInt256.ofNat 1262742802)
      (by decide), hfalse]
    rfl
  have heq15 :
      UInt256.eq (UInt256.ofNat 4235946734) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 15 (by omega)
    rw [flapperSelectorEq I hsz 0xfc 0x7b 0x6a 0xee (UInt256.ofNat 4235946734)
      (by decide), hfalse]
    rfl
  have heq16 :
      UInt256.eq (UInt256.ofNat 1317739989) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 16 (by omega)
    rw [flapperSelectorEq I hsz 0x4e 0x8b 0x1d 0xd5 (UInt256.ofNat 1317739989)
      (by decide), hfalse]
    rfl
  have heq17 :
      UInt256.eq (UInt256.ofNat 911646327) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 17 (by omega)
    rw [flapperSelectorEq I hsz 0x36 0x56 0x9e 0x77 (UInt256.ofNat 911646327)
      (by decide), hfalse]
    rfl
  have heq18 :
      UInt256.eq (UInt256.ofNat 3207937467) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 18 (by omega)
    rw [flapperSelectorEq I hsz 0xbf 0x35 0x3d 0xbb (UInt256.ofNat 3207937467)
      (by decide), hfalse]
    rfl
  have heq19 :
      UInt256.eq (UInt256.ofNat 652224497) (flapperSelWord I) = UInt256.ofNat 0 := by
    have hfalse : ((⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ : ByteArray) ==
        I.calldata.extract 0 4) = false := by
      simpa [flapperSelBytes] using hnm 19 (by omega)
    rw [flapperSelectorEq I hsz 0x26 0xe0 0x27 0xf1 (UInt256.ofNat 652224497)
      (by decide), hfalse]
    rfl
  by_cases hroot :
      UInt256.gt (UInt256.ofNat 2507842956) (flapperSelWord I) = UInt256.ofNat 0
  · obtain ⟨_, _, _, h43⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_26_fallthrough_packed
        (R := [])
        (by simp only [List.length_nil]; omega)
        (by simpa [flapperSelWord] using hroot)
        h26
    by_cases hsplit :
        UInt256.gt (UInt256.ofNat 3393242137) (flapperSelWord I) = UInt256.ofNat 0
    · obtain ⟨_, _, _, h54⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_43_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          hsplit
          h43
      obtain ⟨_, _, _, h65⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_54_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq8
          h54
      obtain ⟨_, _, _, h76⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_65_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq13
          h65
      obtain ⟨_, _, _, h87⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_76_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq9
          h76
      obtain ⟨_, _, _, h98⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_87_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq6
          h87
      obtain ⟨_, _, _, h109⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_98_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq15
          h98
      obtain ⟨_, _, _, h300⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_109_packed
          (R := [flapperSelWord I])
          (by simp only [List.length_cons, List.length_nil]; omega)
          (by jump_dest)
          h109
      exact flapperRuntimeBlocks.flapperRuntime_block_300
        (R := [flapperSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega)
        h300
    · obtain ⟨_, _, _, h113⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_43_taken_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          hsplit
          (by jump_dest)
          h43
      obtain ⟨_, _, _, h125⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_113_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq11
          h113
      obtain ⟨_, _, _, h136⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_125_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq4
          h125
      obtain ⟨_, _, _, h147⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_136_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq2
          h136
      obtain ⟨_, _, _, h158⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_147_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq18
          h147
      obtain ⟨_, _, _, h169⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_158_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq3
          h158
      obtain ⟨_, _, _, h300⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_169_packed
          (R := [flapperSelWord I])
          (by simp only [List.length_cons, List.length_nil]; omega)
          (by jump_dest)
          h169
      exact flapperRuntimeBlocks.flapperRuntime_block_300
        (R := [flapperSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega)
        h300
  · obtain ⟨_, _, _, h173⟩ :=
      flapperRuntimeBlocks.flapperRuntime_block_26_taken_packed
        (R := [])
        (by simp only [List.length_nil]; omega)
        (by simpa [flapperSelWord] using hroot)
        (by jump_dest)
        h26
    by_cases hsplit :
        UInt256.gt (UInt256.ofNat 1262742802) (flapperSelWord I) = UInt256.ofNat 0
    · obtain ⟨_, _, _, h185⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_173_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          hsplit
          h173
      obtain ⟨_, _, _, h196⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_185_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq14
          h185
      obtain ⟨_, _, _, h207⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_196_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq16
          h196
      obtain ⟨_, _, _, h218⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_207_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq12
          h207
      obtain ⟨_, _, _, h229⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_218_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq7
          h218
      obtain ⟨_, _, _, h240⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_229_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq0
          h229
      obtain ⟨_, _, _, h300⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_240_packed
          (R := [flapperSelWord I])
          (by simp only [List.length_cons, List.length_nil]; omega)
          (by jump_dest)
          h240
      exact flapperRuntimeBlocks.flapperRuntime_block_300
        (R := [flapperSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega)
        h300
    · obtain ⟨_, _, _, h244⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_173_taken_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          hsplit
          (by jump_dest)
          h173
      obtain ⟨_, _, _, h256⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_244_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq10
          h244
      obtain ⟨_, _, _, h267⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_256_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq19
          h256
      obtain ⟨_, _, _, h278⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_267_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq5
          h267
      obtain ⟨_, _, _, h289⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_278_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq17
          h278
      obtain ⟨_, _, _, h300⟩ :=
        flapperRuntimeBlocks.flapperRuntime_block_289_fallthrough_packed
          (x0 := flapperSelWord I) (R := [])
          (by simp only [List.length_nil]; omega)
          heq1
          h289
      exact flapperRuntimeBlocks.flapperRuntime_block_300
        (R := [flapperSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega)
        h300

theorem flapperNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (flapperBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem flapperShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (flapperDispatch_none_short hsz)

theorem flapperNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (flapperX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (flapperDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact flapperShortRevert hcode hsize hperm hwv hshort

end Benchmarks.Dss.Flapper
