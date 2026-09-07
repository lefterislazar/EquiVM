import Examples.NestedCaller.Spec
import Reasoning.CallMemory
import Reasoning.CallRefinement
import Reasoning.SummaryPatterns

namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

/-- One call's returned-data allocation, including word rounding and input scratch. -/
def allocationStride : ℕ := 2 ^ 138 + 64
def allocationBound (n : ℕ) : ℕ := 128 + n * allocationStride

def MemoryAt (n : ℕ) (mem : ByteArray) (aw : UInt256) : Prop :=
  ∃ fp : ℕ, 128 ≤ fp ∧ fp ≤ allocationBound n ∧ 96 ≤ mem.size ∧
    mem.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray ∧
    3 ≤ aw.toNat ∧ aw.toNat ≤ allocationBound n

theorem memoryAt_mono {n mem aw} (h : MemoryAt n mem aw) : MemoryAt (n + 1) mem aw := by
  rcases h with ⟨fp, hlo, hhi, hsize, hread, hawlo, hawhi⟩
  refine ⟨fp, hlo, ?_, hsize, hread, hawlo, ?_⟩ <;>
    simp only [allocationBound, Nat.add_mul, Nat.one_mul] at * <;> omega

theorem allocationBound_small {n : ℕ} (h : n ≤ 32) : allocationBound n < 2 ^ 144 := by
  norm_num [allocationBound, allocationStride] at *
  omega

theorem memoryAt_initial : MemoryAt 0 solcFreePtrMem ⟨3⟩ := by
  exact ⟨128, by decide, by decide, by simp only [solcFreePtrMem_size, le_refl],
    solcFreePtrMem_read64, by decide, by decide⟩

def probeWord : UInt256 := solcLeftAlignedSelectorWord ⟨3674743872⟩
noncomputable def selectorMem (mem : ByteArray) (fp : ℕ) : ByteArray :=
  probeWord.toByteArray.write 0 mem fp 32
noncomputable def argumentMem (mem : ByteArray) (fp : ℕ) (i : UInt256) : ByteArray :=
  i.toByteArray.write 0 (selectorMem mem fp) (fp + 4) 32

theorem selectorMem_size (mem : ByteArray) (fp : ℕ) : fp + 32 ≤ (selectorMem mem fp).size :=
  toByteArray_write_size_ge_off_add32_unbounded _ _ _

theorem argumentMem_size (mem : ByteArray) (fp : ℕ) (i : UInt256) :
    fp + 36 ≤ (argumentMem mem fp i).size := by
  have := toByteArray_write_size_ge_off_add32_unbounded i (selectorMem mem fp) (fp + 4)
  simpa only [Nat.add_assoc] using this

theorem argumentMem_read64 {mem : ByteArray} {fp : ℕ} (i : UInt256)
    (hfp : 128 ≤ fp) (hsize : 96 ≤ mem.size) :
    (argumentMem mem fp i).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  rw [argumentMem, write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by have := selectorMem_size mem fp; omega) (by omega)]
  exact toByteArray_write_read_below_of_gap_unbounded _ _ _ _ hsize (by omega)

theorem argumentMem_encode (mem : ByteArray) (fp : ℕ) (i : UInt256) :
    (argumentMem mem fp i).readWithPadding fp 36 = probeSelector ++ i.toByteArray := by
  have hsize := argumentMem_size mem fp i
  have hsel := selectorMem_size mem fp
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split _ fp 4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  congr 1
  · rw [argumentMem, write32_read_below_len _ _ _ _ _ (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by decide) (by decide)]
    have h := toByteArray_write_read_window_of_gap_unbounded probeWord mem fp 0 4
      (by decide) (by decide) (by decide)
    simp only [Nat.add_zero] at h
    rw [show selectorMem mem fp = probeWord.toByteArray.write 0 mem fp 32 from rfl, h]
    native_decide
  · exact toByteArray_write_read_back_of_gap_unbounded _ _ _

/-- Word rounding of a returned byte count stays between the count and count+31. -/
theorem returnRound_bounds {out : ByteArray} (h : out.size < 2 ^ 138) :
    let rounded := UInt256.land (UInt256.add (UInt256.ofNat out.size) ⟨31⟩) (UInt256.lnot ⟨31⟩)
    out.size ≤ rounded.toNat ∧ rounded.toNat ≤ out.size + 31 := by
  dsimp only
  have hn : out.size < UInt256.size := by
    have : 2 ^ 138 < UInt256.size := by decide
    omega
  have hsum : out.size + 31 < UInt256.size := by
    have : 2 ^ 138 + 31 < UInt256.size := by decide
    omega
  rw [uland_toNat, lnot31_toNat]
  have ha : (UInt256.add (UInt256.ofNat out.size) ⟨31⟩).toNat = out.size + 31 :=
    uadd_ofNat_toNat hn (by decide) hsum
  rw [ha, nat_land_mask _ hsum]
  omega


/-- Fixed-size memory regions already covered by active words do not expand memory. -/
theorem expand_eq {aw off len : UInt256} (h : off.toNat + len.toNat ≤ aw.toNat * 32) :
    Reasoning.Reach.M aw off len = aw := by
  unfold Reasoning.Reach.M
  rw [memoryExpansion_eq_of_bounds _ _ _ (Or.inr h), u256_ofNat_toNat]

theorem mload64_eq {mem : ByteArray} {aw : UInt256} {fp : ℕ}
    (hsize : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray)
    (hlo : 3 ≤ aw.toNat) (hhi : aw.toNat < 2 ^ 144) :
    memLoad ⟨64⟩ aw mem = UInt256.ofNat fp := by
  apply mloadWordValue_of_readWithPadding (by exact Nat.lt_of_lt_of_le (by decide) hsize) ?_ hread
  change ¬ 64 ≥ (aw * ⟨32⟩).toNat
  rw [umul_toNat _ _ (by change aw.toNat * 32 < UInt256.size; norm_num [UInt256.size] at *; omega)]
  change ¬ 64 ≥ aw.toNat * 32
  omega

def inputWords (aw : UInt256) (fp : ℕ) : UInt256 :=
  UInt256.ofNat (max aw.toNat ((fp + 67) / 32))

theorem inputWords_toNat {aw : UInt256} {fp : ℕ} (hfp : fp < 2 ^ 144) :
    (inputWords aw fp).toNat = max aw.toNat ((fp + 67) / 32) := by
  apply ulit_toNat'
  apply max_lt aw.val.isLt
  norm_num [UInt256.size] at *
  omega

theorem inputWords_bounds {n aw fp} (hn : n ≤ 16)
    (haw : aw.toNat ≤ allocationBound n) (hfp : fp ≤ allocationBound n) :
    aw.toNat ≤ (inputWords aw fp).toNat ∧ fp + 36 ≤ (inputWords aw fp).toNat * 32 ∧
    (inputWords aw fp).toNat ≤ allocationBound (n + 1) := by
  have hb := allocationBound_small (n := n) (by omega)
  rw [inputWords_toNat (by omega)]
  have hstep : allocationBound n ≤ allocationBound (n + 1) := by
    simp only [allocationBound, Nat.add_mul, Nat.one_mul]; omega
  have hspace : fp + 67 ≤ allocationBound (n + 1) * 32 := by
    simp only [allocationBound, allocationStride, Nat.add_mul, Nat.one_mul] at *
    omega
  constructor
  · exact le_max_left _ _
  constructor
  · have := le_max_right aw.toNat ((fp + 67) / 32); omega
  · apply max_le (by omega); omega

theorem inputWords_eq {aw : UInt256} {fp : ℕ} (hfp : fp < 2 ^ 144) :
    Reasoning.Reach.M (Reasoning.Reach.M aw (UInt256.ofNat fp) ⟨32⟩)
      (UInt256.ofNat (fp + 4)) ⟨32⟩ = inputWords aw fp := by
  have hb : fp + 67 < UInt256.size := by norm_num [UInt256.size] at *; omega
  have hfirst : max aw.toNat ((fp + 63) / 32) < UInt256.size :=
    max_lt aw.val.isLt (by omega)
  unfold Reasoning.Reach.M MachineState.M
  simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl]
  rw [ulit_toNat' fp (by omega), ulit_toNat' (fp + 4) (by omega)]
  change UInt256.ofNat (max (UInt256.ofNat (max aw.toNat ((fp + 63) / 32))).toNat
    ((fp + 67) / 32)) = inputWords aw fp
  rw [ulit_toNat' _ hfirst]
  unfold inputWords
  congr 1
  omega


noncomputable def copiedMem (mem : ByteArray) (fp : ℕ) (i : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (argumentMem mem fp i) fp (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

def nextPointer (fp : ℕ) (out : ByteArray) : UInt256 :=
  UInt256.ofNat fp + UInt256.land (UInt256.ofNat out.size + ⟨31⟩) (UInt256.lnot ⟨31⟩)

noncomputable def decodedMem (mem : ByteArray) (fp : ℕ) (i : UInt256) (out : ByteArray) : ByteArray :=
  (nextPointer fp out).toByteArray.write 0 (copiedMem mem fp i out) 64 32

theorem copiedMem_facts {mem fp i out} (hfp : fp < 2 ^ 144) (hout : out.size < 2 ^ 138) :
    (copiedMem mem fp i out).size = (argumentMem mem fp i).size ∧
    (∀ read, read + 32 ≤ fp → (copiedMem mem fp i out).readWithPadding read 32 =
      (argumentMem mem fp i).readWithPadding read 32) ∧
    (32 ≤ out.size → (copiedMem mem fp i out).readWithPadding fp 32 = out.extract 0 32) := by
  have hfpu : fp < UInt256.size := by norm_num [UInt256.size] at *; omega
  have h := callOutputFacts (argumentMem mem fp i) out (UInt256.ofNat fp) ⟨32⟩
    (by norm_num [UInt256.size] at *; omega)
    (by rw [ulit_toNat' fp hfpu]; have := argumentMem_size mem fp i; change fp + 32 ≤ _; omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ulit_toNat' fp hfpu] using h.size
  · simpa only [ulit_toNat' fp hfpu] using h.readBelow
  · simpa only [ulit_toNat' fp hfpu] using h.readWord (by decide)

/-- Decode allocation restores the loop's memory invariant. Its bound depends on
how many calls may already have occurred, not on a chosen callee or output length. -/
theorem decodedMem_facts {n mem aw fp i out} (hn : n ≤ 16)
    (hfp : 128 ≤ fp) (hfphi : fp ≤ allocationBound n)
    (hawlo : 3 ≤ aw.toNat) (hawhi : aw.toNat ≤ allocationBound n)
    (hout : out.size < 2 ^ 138) (hword : 32 ≤ out.size) :
    MemoryAt (n + 1) (decodedMem mem fp i out) (inputWords aw fp) ∧
    (decodedMem mem fp i out).readWithPadding fp 32 = out.extract 0 32 ∧
    fp + 32 ≤ (decodedMem mem fp i out).size := by
  have hb := allocationBound_small (n := n) (by omega)
  have hb' := allocationBound_small (n := n + 1) (by omega)
  have hcopy := copiedMem_facts (mem := mem) (i := i) (by omega : fp < 2 ^ 144) hout
  have hsize : fp + 36 ≤ (copiedMem mem fp i out).size := by
    rw [hcopy.1]; exact argumentMem_size mem fp i
  have haw := inputWords_bounds hn hawhi hfphi
  have hr := returnRound_bounds hout
  let rounded := UInt256.land (UInt256.ofNat out.size + ⟨31⟩) (UInt256.lnot ⟨31⟩)
  change out.size ≤ rounded.toNat ∧ rounded.toNat ≤ out.size + 31 at hr
  have hpbound : fp + rounded.toNat ≤ allocationBound (n + 1) := by
    simp only [allocationBound, allocationStride, Nat.add_mul, Nat.one_mul] at *
    omega
  have hpu : fp + rounded.toNat < UInt256.size := by
    have : 2 ^ 144 < UInt256.size := by decide
    omega
  have hptr : (nextPointer fp out).toNat = fp + rounded.toNat := by
    unfold nextPointer
    rw [uadd_toNat, ulit_toNat' fp (by omega), Nat.mod_eq_of_lt hpu]
  have hmsize : (decodedMem mem fp i out).size = (copiedMem mem fp i out).size := by
    apply toByteArray_write32_size_of_le _ _ _ _ _ rfl (by omega) (by omega)
  refine ⟨⟨(nextPointer fp out).toNat, ?_, ?_, ?_, ?_, ?_, haw.2.2⟩, ?_, ?_⟩
  · rw [hptr]; omega
  · rw [hptr]; exact hpbound
  · rw [hmsize]; omega
  · rw [u256_ofNat_toNat]
    exact toByteArray_write32_read_back _ _ _ (by omega)
  · omega
  · rw [decodedMem, write32_read_above _ _ 64 fp (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]
    exact hcopy.2.2 hword
  · rw [hmsize]; omega


theorem wordExpansion_toNat {aw : UInt256} {fp : ℕ} (hfp : fp < 2 ^ 144) :
    (Reasoning.Reach.M aw (UInt256.ofNat fp) ⟨32⟩).toNat = max aw.toNat ((fp + 63) / 32) := by
  have hb : fp + 63 < UInt256.size := by norm_num [UInt256.size] at *; omega
  unfold Reasoning.Reach.M MachineState.M
  simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl, ulit_toNat' fp (by omega)]
  exact ulit_toNat' _ (max_lt aw.val.isLt (by omega))

end NestedCaller
