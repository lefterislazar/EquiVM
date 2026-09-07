import Examples.NestedCaller.Blocks
import Examples.NestedCaller.Spec
import Reasoning.ABI
import Reasoning.Dispatch

namespace NestedCaller
open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory
open nestedCallerBlocks
set_option maxRecDepth 1500

def runSelector : ByteArray := ⟨#[0x38, 0x1f, 0xd1, 0x90]⟩

/-- Concrete Keccak selector fact, following the other contract examples. -/
axiom runSelectorBytes :
  (ffi.KEC (String.toByteArray (transitionSigStr runTransition))).extract 0 4 = runSelector

theorem dispatch : SingleSelectorDispatch nestedCallerContract runTransition runSelector :=
  singleSelectorDispatch rfl rfl runSelectorBytes rfl

abbrev selectorWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
abbrev targetArg (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes 4 32)
abbrev countArg (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes 36 32)

abbrev decodedLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "target" (.address (AccountAddress.ofNat (targetArg I).toNat))).insert "count"
    (.int (Int.ofNat (countArg I).toNat))

theorem selector_matches {I : ExecutionEnv} (hsize : 4 ≤ I.calldata.size) :
    UInt256.eq ⟨941609360⟩ (selectorWord I) =
      if (runSelector == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsize 0x38 0x1f 0xd1 0x90 ⟨941609360⟩ (by decide)

theorem nonPayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue ≠ ⟨0⟩) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have r12 := nestedCaller_block_0_fallthrough (by simp) (isZero_eq_zero_of_ne hcv) (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode)
  exact nestedCaller_block_12 (by simp) r12

theorem dispatchGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD nestedCallerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨15⟩ [I.weiValue]
      solcFreePtrMem ⟨3⟩ ByteArray.empty (cA, σ) k C := by
  have r := nestedCaller_block_0_taken (by simp) (by rw [hcv]; decide) (by jump_dest) (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode)
  exact ⟨_, _, r⟩

theorem shortSelector {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 4) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, r15⟩ := dispatchGuard (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hcv
  have r41 := nestedCaller_block_15_taken (by simp) (lt_four_ne_zero_of_lt hshort) (by jump_dest) r15
  exact nestedCaller_block_41 (by simp) r41

theorem selectorPrefix {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hfour : 4 ≤ I.calldata.size) :
    ∃ k C, RD nestedCallerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨25⟩ []
      solcFreePtrMem ⟨3⟩ ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, r15⟩ := dispatchGuard (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hcv
  exact ⟨_, _, nestedCaller_block_15_fallthrough (by simp) (lt_four_eq_zero_of_ge hfour hsize) r15⟩

theorem wrongSelector {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hfour : 4 ≤ I.calldata.size)
    (hmatch : (runSelector == I.calldata.extract 0 4) = false) :
    RDrev nestedCallerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, r25⟩ := selectorPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hcv hsize hfour
  have r41 := nestedCaller_block_25_fallthrough (by simp) (by
    change UInt256.eq ⟨941609360⟩ (selectorWord I) = ⟨0⟩
    rw [selector_matches hfour, hmatch]; rfl) r25
  exact nestedCaller_block_41 (by simp) r41

theorem decoderEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = nestedCallerBytecode) (hcv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hfour : 4 ≤ I.calldata.size)
    (hmatch : (runSelector == I.calldata.extract 0 4) = true) :
    ∃ k C, RD nestedCallerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩, selectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, r25⟩ := selectorPrefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hcv hsize hfour
  have r45 := nestedCaller_block_25_taken (by simp) (by
    change UInt256.eq ⟨941609360⟩ (selectorWord I) ≠ ⟨0⟩
    rw [selector_matches hfour, hmatch]; decide) (by jump_dest) r25
  have r491 := nestedCaller_block_45 (by simp) (by jump_dest) r45
  rw [uadd_lit_usub_ofNat_lit hfour hsize] at r491
  exact ⟨_, _, r491⟩

/-- Every failing ABI length check reaches the same generated revert stub. -/
theorem badLength {ee : ExecutionEnv} {g s0 mem aw rdata world k C sel}
    (hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩)
    (rd : RD nestedCallerBytecode ee g s0 ⟨491⟩
      [⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨66⟩, ⟨71⟩, sel] mem aw rdata world k C) :
    RDrev nestedCallerBytecode g s0 := by
  have r505 := nestedCaller_block_491_fallthrough (by simp)
    (by change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩; rw [hcheck]; decide) rd
  exact nestedCaller_block_346 (by simp)
    (nestedCaller_block_505 (by simp) (by jump_dest) r505)

/-- ABI address decoding up to the canonical-address check. -/
theorem addressCheck {ee : ExecutionEnv} {g s0 mem aw rdata world k C sel}
    (hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩)
    (rd : RD nestedCallerBytecode ee g s0 ⟨491⟩
      [⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨66⟩, ⟨71⟩, sel] mem aw rdata world k C) :
    ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨407⟩
      [UInt256.land (targetArg ee) solcAddrMask, targetArg ee, ⟨434⟩, targetArg ee, ⟨4⟩,
       UInt256.ofNat ee.calldata.size, ⟨526⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
       UInt256.ofNat ee.calldata.size, ⟨66⟩, ⟨71⟩, sel] mem aw rdata world k' C' := by
  have r513 := nestedCaller_block_491_taken (by simp)
    (by change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩; rw [hcheck]; decide) (by jump_dest) rd
  have r420 := nestedCaller_block_513 (by simp) (by jump_dest) r513
  have r398 := nestedCaller_block_420 (by simp) (by jump_dest) r420
  have r381 := nestedCaller_block_398 (by simp) (by jump_dest) r398
  have r350 := nestedCaller_block_381 (by simp) (by jump_dest) r381
  have r391 := nestedCaller_block_350 (by simp) (by jump_dest) r350
  exact ⟨_, _, nestedCaller_block_391 (by simp) (by jump_dest) r391⟩

/-- Canonical calldata reaches the function body. Noncanonical addresses revert. -/
theorem decodeBody {ee : ExecutionEnv} {g s0 mem aw rdata world k C sel}
    (hcheck : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩)
    (rd : RD nestedCallerBytecode ee g s0 ⟨491⟩
      [⟨4⟩, UInt256.ofNat ee.calldata.size, ⟨66⟩, ⟨71⟩, sel] mem aw rdata world k C) :
    if (targetArg ee).toNat < EVM.addressModulus then
      ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨93⟩ [countArg ee, targetArg ee, ⟨71⟩, sel]
        mem aw rdata world k' C'
    else RDrev nestedCallerBytecode g s0 := by
  obtain ⟨k1, C1, r407⟩ := addressCheck hcheck rd
  split_ifs with hcanon
  · have r417 := nestedCaller_block_407_taken (by simp) (by rw [solcAddrCanon_eq hcanon]; decide) (by jump_dest) r407
    have r434 := nestedCaller_block_417 (by simp) (by jump_dest) r417
    have r526 := nestedCaller_block_434 (by simp) (by jump_dest) r434
    have r471 := nestedCaller_block_526 (by simp) (by jump_dest) r526
    have r449 := nestedCaller_block_471 (by simp) (by jump_dest) r471
    have r440 := nestedCaller_block_449 (by simp) (by jump_dest) r449
    have r458 := nestedCaller_block_440 (by simp) (by jump_dest) r440
    have r468 := nestedCaller_block_458_taken (by simp) (by rw [uInt256_eq_self]; decide) (by jump_dest) r458
    have r485 := nestedCaller_block_468 (by simp) (by jump_dest) r468
    have r543 := nestedCaller_block_485 (by simp) (by jump_dest) r485
    have r66 := nestedCaller_block_543 (by simp) (by jump_dest) r543
    exact ⟨_, _, nestedCaller_block_66 (by simp) (by jump_dest) r66⟩
  · have hne : UInt256.eq (targetArg ee) (UInt256.land (targetArg ee) solcAddrMask) ≠ ⟨1⟩ :=
      fun h => hcanon (solcAddrCanonical_of_clean h)
    have r414 := nestedCaller_block_407_fallthrough (by simp) (uInt256_eq_zero_of_ne hne) r407
    exact nestedCaller_block_414 (by simp) r414

end NestedCaller
