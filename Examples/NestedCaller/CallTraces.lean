import Examples.NestedCaller.Blocks
import Examples.NestedCaller.CallMemory

namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory
open nestedCallerBlocks
set_option maxRecDepth 10000

private theorem word_add_ofNat (a b : ℕ) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat]
  change (a % UInt256.size + b % UInt256.size) % UInt256.size = (a + b) % UInt256.size
  exact (Nat.add_mod _ _ _).symm

private theorem word_add_zero (a : UInt256) : a + ⟨0⟩ = a := by
  apply u256_inj
  rw [uadd_toNat]
  change (a.toNat + 0) % UInt256.size = a.toNat
  exact Nat.mod_eq_of_lt a.val.isLt

def callRest (fp : ℕ) (target gas i : UInt256) (saved : List UInt256) : List UInt256 :=
  [UInt256.ofNat (fp + 36), ⟨3674743872⟩, target, gas, ⟨0⟩, i, target, ⟨135⟩] ++ saved

/-- Selector construction, uint256 ABI encoder, and CALL argument setup are all
composed from generated summaries. The result stops at the compiler-inserted GAS. -/
theorem reachCallGas {ee g s0 mem aw rdata world k C gas target i saved n fp}
    (hn : n ≤ 16) (hfp : 128 ≤ fp) (hfphi : fp ≤ allocationBound n)
    (hsize : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray)
    (hawlo : 3 ≤ aw.toNat) (hawhi : aw.toNat ≤ allocationBound n)
    (hmask : UInt256.land ⟨1461501637330902918203684832716283019655932542975⟩ target = target)
    (hlen : saved.length + 24 ≤ 1024)
    (rd : RD nestedCallerBytecode ee g s0 ⟨215⟩ ([gas, ⟨0⟩, i, target, ⟨135⟩] ++ saved)
      mem aw rdata world k C) :
    ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨284⟩
      ([target, ⟨0⟩, UInt256.ofNat fp, ⟨36⟩, UInt256.ofNat fp, ⟨32⟩] ++ callRest fp target gas i saved)
      (argumentMem mem fp i) (inputWords aw fp) rdata world k' C' := by
  have hb := allocationBound_small (n := n) (by omega)
  have hfps : fp < 2 ^ 144 := by omega
  have hfpu : fp + 67 < UInt256.size := by norm_num [UInt256.size] at *; omega
  have hload := mload64_eq hsize hread hawlo (by omega)
  have hexp : Reasoning.Reach.M aw ⟨64⟩ ⟨32⟩ = aw := expand_eq (by change 64 + 32 ≤ aw.toNat * 32; omega)
  change memLoad (UInt256.ofNat 64) aw mem = _ at hload
  change Reasoning.Reach.M aw (UInt256.ofNat 64) ⟨32⟩ = aw at hexp
  change UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) target = target at hmask
  have r568 := nestedCaller_block_215 (by simp; omega) (by jump_dest) rd
  rw [hload, hexp, hmask] at r568
  simp only [word_add_ofNat, ulit_toNat' fp (by omega)] at r568
  have hadd : 4 + fp = fp + 4 := by omega
  rw [hadd] at r568
  have r553 := nestedCaller_block_568 (by simp; omega) (by jump_dest) r568
  have r440 := nestedCaller_block_553 (by simp; omega) (by jump_dest) r553
  have r562 := nestedCaller_block_440 (by simp; omega) (by jump_dest) r440
  have r587 := nestedCaller_block_562 (by simp; omega) (by jump_dest) r562
  simp only [word_add_zero, word_add_ofNat, ulit_toNat' (fp + 4) (by omega)] at r587
  have r272 := nestedCaller_block_587 (by simp; omega) (by jump_dest) r587
  have haw := inputWords_bounds hn hawhi hfphi
  have haweq := inputWords_eq (aw := aw) hfps
  rw [haweq] at r272
  have hload' : memLoad ⟨64⟩ (inputWords aw fp) (argumentMem mem fp i) = UInt256.ofNat fp :=
    mload64_eq (by have := argumentMem_size mem fp i; omega)
      (by rw [argumentMem_read64 i hfp hsize]; exact hread) (by omega)
      (lt_of_le_of_lt haw.2.2 (allocationBound_small (by omega)))
  change RD nestedCallerBytecode ee g s0 _ _ (argumentMem mem fp i) _ _ _ _ _ at r272
  have r284 := nestedCaller_block_272 (by simp; omega) r272
  change ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨284⟩ _ _ _ _ _ k' C'
  have hexp' : Reasoning.Reach.M (inputWords aw fp) ⟨64⟩ ⟨32⟩ = inputWords aw fp :=
    expand_eq (by change 64 + 32 ≤ (inputWords aw fp).toNat * 32; omega)
  change RD nestedCallerBytecode ee g s0 _ _ (argumentMem mem fp i) _ _ _ _ _ at r284
  change memLoad (UInt256.ofNat 64) (inputWords aw fp) (argumentMem mem fp i) = _ at hload'
  change Reasoning.Reach.M (inputWords aw fp) (UInt256.ofNat 64) ⟨32⟩ = _ at hexp'
  rw [hload', hexp'] at r284
  have hsub : UInt256.sub (UInt256.ofNat (fp + 4 + 32)) (UInt256.ofNat fp) = ⟨36⟩ := by
    apply u256_inj
    rw [usub_toNat (by rw [ulit_toNat' fp (by omega), ulit_toNat' (fp + 4 + 32) (by omega)]; omega),
      ulit_toNat' fp (by omega), ulit_toNat' (fp + 4 + 32) (by omega)]
    change fp + 4 + 32 - fp = 36
    omega
  rw [hsub] at r284
  exact ⟨_, _, r284⟩

/-- CALL status failure shares a single generated revert tail, independently of
why the attempt failed and of its return-data contents. -/
theorem callFailure {ee g s0 mem aw out world k C rest}
    (hlen : rest.length + 4 ≤ 1024)
    (rd : RD nestedCallerBytecode ee g s0 ⟨286⟩ (⟨0⟩ :: rest) mem aw out world k C) :
    RDrev nestedCallerBytecode g s0 := by
  have r293 := nestedCaller_block_286_fallthrough (by omega) (by decide) rd
  exact nestedCaller_block_293 (by simp only [List.length_cons]; omega) r293


/-- The successful status check and decoder allocation preserve the old output
base on the stack while storing the next free pointer at memory slot 64. -/
theorem successToDecoder {ee g s0 mem aw out world k C fp d0 d1 d2 tail}
    (hlen : tail.length + 9 ≤ 1024) (hsize : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray)
    (hawlo : 3 ≤ aw.toNat) (hawhi : aw.toNat < 2 ^ 144)
    (rd : RD nestedCallerBytecode ee g s0 ⟨286⟩ (⟨1⟩ :: d0 :: d1 :: d2 :: tail)
      mem aw out world k C) :
    ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨613⟩
      ([UInt256.ofNat fp, UInt256.ofNat fp + UInt256.ofNat out.size, ⟨336⟩] ++ tail)
      ((nextPointer fp out).toByteArray.write 0 mem 64 32) aw out world k' C' := by
  have r300 := nestedCaller_block_286_taken (by simp; omega) (by decide) (by jump_dest) rd
  have rn := nestedCaller_block_300 (by simp; omega) (by jump_dest) r300
  have hm := mload64_eq hsize hread hawlo hawhi
  change memLoad (UInt256.ofNat 64) aw mem = _ at hm
  have he : Reasoning.Reach.M aw (UInt256.ofNat 64) ⟨32⟩ = aw :=
    expand_eq (by change 64 + 32 ≤ aw.toNat * 32; omega)
  simp only [hm, he] at rn
  exact ⟨_, _, rn⟩

/-- The return decoder rejects fewer than one word of data. -/
theorem shortReturn {ee g s0 mem aw out world k C fp tail}
    (hlen : tail.length + 9 ≤ 1024) (hfp : fp < UInt256.size) (hout : out.size < 32)
    (rd : RD nestedCallerBytecode ee g s0 ⟨613⟩
      ([UInt256.ofNat fp, UInt256.ofNat fp + UInt256.ofNat out.size, ⟨336⟩] ++ tail)
      mem aw out world k C) : RDrev nestedCallerBytecode g s0 := by
  have hdiff := usub_uadd_lit_cancel_mod (base := fp) (n := out.size) hfp
    (by
      have : 32 < UInt256.size := by decide
      omega)
  change (UInt256.ofNat fp + UInt256.ofNat out.size).sub (UInt256.ofNat fp) = UInt256.ofNat out.size at hdiff
  have r626 := nestedCaller_block_613_fallthrough (by simp; omega)
    (by rw [slt_lit_one_low (by decide) (by simpa only [hdiff, ulit_toNat' out.size (by norm_num [UInt256.size] at *; omega)] using hout)]; decide) rd
  have r346 := nestedCaller_block_626 (by simp; omega) (by jump_dest) r626
  exact nestedCaller_block_346 (by simp; omega) r346

/-- Read the decoded word, pass the compiler's uint256 validator, and return from
`sample` to its real internal continuation. -/
theorem decodedReturn {ee g s0 mem aw out world k C fp gas i target saved w}
    (hlen : saved.length + 24 ≤ 1024) (hfp : fp < UInt256.size)
    (houtlo : 32 ≤ out.size) (houthi : out.size < 2 ^ 138)
    (hload : memLoad (UInt256.ofNat fp) aw mem = w)
    (hregion : fp + 32 ≤ aw.toNat * 32)
    (rd : RD nestedCallerBytecode ee g s0 ⟨613⟩
      ([UInt256.ofNat fp, UInt256.ofNat fp + UInt256.ofNat out.size, ⟨336⟩, gas, ⟨0⟩, i, target, ⟨135⟩] ++ saved)
      mem aw out world k C) :
    ∃ k' C', RD nestedCallerBytecode ee g s0 ⟨135⟩ (w :: saved) mem aw out world k' C' := by
  have hou : out.size < UInt256.size := by norm_num [UInt256.size] at *; omega
  have hos : out.size < 2 ^ 255 := by norm_num at *; omega
  have hdiff := usub_uadd_lit_cancel_mod (base := fp) (n := out.size) hfp hou
  change (UInt256.ofNat fp + UInt256.ofNat out.size).sub (UInt256.ofNat fp) = UInt256.ofNat out.size at hdiff
  have r634 := nestedCaller_block_613_taken (by simp; omega)
    (by rw [slt_lit_zero (by decide) (by simpa only [hdiff, ulit_toNat' out.size hou] using houtlo)
      (by simpa only [hdiff, ulit_toNat' out.size hou] using hos)]; decide) (by jump_dest) rd
  have r593 := nestedCaller_block_634 (by simp; omega) (by jump_dest) r634
  simp only [word_add_zero] at r593
  have r449 := nestedCaller_block_593 (by simp; omega) (by jump_dest) r593
  rw [hload, expand_eq (by simpa only [ulit_toNat' fp hfp] using hregion)] at r449
  have r440 := nestedCaller_block_449 (by simp; omega) (by jump_dest) r449
  have r458 := nestedCaller_block_440 (by simp; omega) (by jump_dest) r440
  have r468 := nestedCaller_block_458_taken (by simp; omega) (by rw [uInt256_eq_self]; decide) (by jump_dest) r458
  have r607 := nestedCaller_block_468 (by simp; omega) (by jump_dest) r468
  have r647 := nestedCaller_block_607 (by simp; omega) (by jump_dest) r607
  have r336 := nestedCaller_block_647 (by simp; omega) (by jump_dest) r647
  have r340 := nestedCaller_block_336 (by simp; omega) r336
  exact ⟨_, _, nestedCaller_block_340 (by simp; omega) (by jump_dest) r340⟩

end NestedCaller
