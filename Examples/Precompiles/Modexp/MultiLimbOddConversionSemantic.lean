import Examples.Precompiles.Modexp.MultiLimbOddBranchContract
import Examples.Precompiles.Modexp.MultiLimbMemoryModel

/-!
# Memory semantics of `bytesToLimbs`

These lemmas show that generated conversion loads and stores preserve the active-word counter when
both accesses are already inside the allocated EVM memory extent. This includes implicit zero
payload words which need not be materialized in the concrete `ByteArray`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbOddConversionSemantic

open Modexp.MultiLimbGenerated
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The generated full-word source address is the corresponding 32-byte chunk counted backwards
from the end of the source byte array. -/
theorem fullWordReadAddress_toNat
    {dataPtr dataLen i : Nat}
    (hlen : dataLen ≤ 1024) (hi : 32 * (i + 1) ≤ dataLen)
    (hfit : dataPtr + 32 + dataLen < UInt256.size) :
    (fullWordReadAddress (UInt256.ofNat i) (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen)).toNat = dataPtr + 32 + dataLen - 32 * (i + 1) := by
  have hiWord : i < UInt256.size := by omega
  have hi1Word : i + 1 < UInt256.size := by omega
  have hlenWord : dataLen < UInt256.size := by omega
  have hptrWord : dataPtr < UInt256.size := by omega
  have hmulWord : 32 * (i + 1) < UInt256.size := by omega
  have hadd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat i
  have hshift : (UInt256.ofNat (i + 1)).shiftLeft ⟨5⟩ =
      UInt256.ofNat (32 * (i + 1)) := shiftLeft5_ofNat_eq hmulWord
  have hsub :
      (UInt256.ofNat dataLen - UInt256.ofNat (32 * (i + 1))).toNat =
        dataLen - 32 * (i + 1) := by
    change (UInt256.sub (UInt256.ofNat dataLen)
      (UInt256.ofNat (32 * (i + 1)))).toNat = _
    rw [usub_ofNat_lit_toNat hi hlenWord]
  have hfirst : dataPtr + (dataLen - 32 * (i + 1)) < UInt256.size := by omega
  have hsecond : dataPtr + (dataLen - 32 * (i + 1)) + 32 < UInt256.size := by omega
  unfold fullWordReadAddress fullWordReadOffset
  rw [hadd, hshift, uadd_toNat, uadd_toNat, hsub,
    UInt256.toNat_ofNat_of_lt hptrWord, show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hsecond]
  omega

/-- The generated full-word destination address is the `i`th word-array payload slot. -/
theorem fullWordWriteAddress_toNat
    {limbsPtr i : Nat}
    (hfit : limbsPtr + 32 + 32 * (i + 1) < UInt256.size) :
    (fullWordWriteAddress (UInt256.ofNat i) (UInt256.ofNat limbsPtr)).toNat =
      limbsPtr + 32 + 32 * i := by
  have hiWord : i < UInt256.size := by omega
  have hptrWord : limbsPtr < UInt256.size := by omega
  have hmulWord : 32 * i < UInt256.size := by omega
  have hshift : (UInt256.ofNat i).shiftLeft ⟨5⟩ = UInt256.ofNat (32 * i) :=
    shiftLeft5_ofNat_eq hmulWord
  have hfirst : limbsPtr + 32 * i < UInt256.size := by omega
  have hsecond : limbsPtr + 32 * i + 32 < UInt256.size := by omega
  unfold fullWordWriteAddress
  rw [hshift, uadd_toNat, uadd_toNat, UInt256.toNat_ofNat_of_lt hptrWord,
    UInt256.toNat_ofNat_of_lt hmulWord, show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hsecond]
  omega

/-- The optional source load starts at the byte-array payload. -/
theorem partialWordReadAddress_toNat
    {dataPtr : Nat} (hfit : dataPtr + 32 < UInt256.size) :
    (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat = dataPtr + 32 := by
  unfold partialWordReadAddress
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 by decide, Nat.mod_eq_of_lt hfit]

/-- The optional most-significant limb follows all complete destination limbs. -/
theorem partialWordWriteAddress_toNat
    {limbsPtr dataLen : Nat} (hlen : dataLen ≤ 1024)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size) :
    (partialWordWriteAddress (UInt256.ofNat dataLen) (UInt256.ofNat limbsPtr)).toNat =
      limbsPtr + 32 + 32 * (dataLen / 32) := by
  rw [partialWordWriteAddress, wordClearedRemainder_eq hlen]
  have hptr : limbsPtr < UInt256.size := by omega
  have hcleared : 32 * (dataLen / 32) < UInt256.size := by omega
  have hfirst : limbsPtr + 32 * (dataLen / 32) < UInt256.size := by omega
  have hsecond : limbsPtr + 32 * (dataLen / 32) + 32 < UInt256.size := by omega
  rw [uadd_toNat, uadd_toNat, UInt256.toNat_ofNat_of_lt hptr,
    UInt256.toNat_ofNat_of_lt hcleared, show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [Nat.mod_eq_of_lt hfirst, Nat.mod_eq_of_lt hsecond]
  omega

/-- A bounded sequence of full-word conversion stores does not change the concrete memory size. -/
theorem fullWordIterate_memory_size
    (dataPtr dataLen limbsPtr : UInt256) (count : Nat) (state : FullWordState)
    (hin : ∀ q, q < count →
      let current := fullWordIterate dataPtr dataLen limbsPtr q state
      (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤ current.memory.size) :
    (fullWordIterate dataPtr dataLen limbsPtr count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen limbsPtr state
      have hfirst := hin 0 (by omega)
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        exact write_size_of_inBounds_from _ _ 0 _ 32 (by decide)
          (by rw [toByteArray_size]) hfirst
      have hin' : ∀ q, q < count →
          let current := fullWordIterate dataPtr dataLen limbsPtr q next
          (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, fullWordIterate_advance] using hin (q + 1) (by omega)
      have hrest := ih next hin'
      simpa only [next, fullWordIterate] using hrest.trans hnextSize

/-- Full-word conversion stores above a fixed 32-byte window preserve that window. -/
theorem fullWordIterate_read_below
    (dataPtr dataLen limbsPtr : UInt256) (count : Nat) (state : FullWordState)
    (read : Nat)
    (hin : ∀ q, q < count →
      let current := fullWordIterate dataPtr dataLen limbsPtr q state
      (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤ current.memory.size)
    (habove : ∀ q, q < count →
      let current := fullWordIterate dataPtr dataLen limbsPtr q state
      read + 32 ≤ (fullWordWriteAddress current.index limbsPtr).toNat) :
    (fullWordIterate dataPtr dataLen limbsPtr count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen limbsPtr state
      let dest := (fullWordWriteAddress state.index limbsPtr).toNat
      have hfirstIn : dest + 32 ≤ state.memory.size := by
        simpa only [dest, fullWordIterate] using hin 0 (by omega)
      have hfirstAbove : read + 32 ≤ dest := by
        simpa only [dest, fullWordIterate] using habove 0 (by omega)
      have hfirst : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory, dest]
        exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
          (by omega) hfirstAbove
      have hin' : ∀ q, q < count →
          let current := fullWordIterate dataPtr dataLen limbsPtr q next
          (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, fullWordIterate_advance] using hin (q + 1) (by omega)
      have habove' : ∀ q, q < count →
          let current := fullWordIterate dataPtr dataLen limbsPtr q next
          read + 32 ≤ (fullWordWriteAddress current.index limbsPtr).toNat := by
        intro q hq
        simpa only [next, fullWordIterate_advance] using habove (q + 1) (by omega)
      have hrest := ih next hin' habove'
      simpa only [next, fullWordIterate] using hrest.trans hfirst

@[simp] theorem fullWordIterate_add
    (dataPtr dataLen limbsPtr : UInt256) (a b : Nat) (state : FullWordState) :
    fullWordIterate dataPtr dataLen limbsPtr (a + b) state =
      fullWordIterate dataPtr dataLen limbsPtr b
        (fullWordIterate dataPtr dataLen limbsPtr a state) := by
  induction a generalizing state with
  | zero => simp only [Nat.zero_add, fullWordIterate]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [fullWordIterate]
      exact ih (fullWordAdvance dataPtr dataLen limbsPtr state)

/-- If every syntactic destination of a bounded iteration lies in the initial memory, all
intermediate memories retain that initial size. -/
theorem fullWordIterate_memory_size_of_bound
    (dataPtr dataLen limbsPtr : UInt256) (count : Nat) (state : FullWordState)
    (hbound : ∀ q, q < count →
      (fullWordWriteAddress (state.index + UInt256.ofNat q) limbsPtr).toNat + 32 ≤
        state.memory.size) :
    (fullWordIterate dataPtr dataLen limbsPtr count state).memory.size =
      state.memory.size := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen limbsPtr state
      have hfirst : (fullWordWriteAddress state.index limbsPtr).toNat + 32 ≤
          state.memory.size := by
        have hzero : state.index + UInt256.ofNat 0 = state.index := by
          rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by apply u256_inj; rfl,
            u256_add_comm, u256_zero_add]
        simpa only [hzero] using hbound 0 (by omega)
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        exact write_size_of_inBounds_from _ _ 0 _ 32 (by decide)
          (by rw [toByteArray_size]) hfirst
      have hbound' : ∀ j, j < count →
          (fullWordWriteAddress (next.index + UInt256.ofNat j) limbsPtr).toNat + 32 ≤
            next.memory.size := by
        intro j hj
        rw [hnextSize]
        dsimp only [next, fullWordAdvance]
        rw [u256_add_assoc, u256_one_add_ofNat]
        exact hbound (j + 1) (by omega)
      have hrest := ih next hbound'
      simpa only [next, fullWordIterate] using hrest.trans hnextSize

/-- Every prefix of a syntactically in-bounds full-word conversion has the initial memory size. -/
theorem fullWordIterate_memory_size_prefix
    (dataPtr dataLen limbsPtr : UInt256) (count : Nat) (state : FullWordState)
    (hbound : ∀ q, q < count →
      (fullWordWriteAddress (state.index + UInt256.ofNat q) limbsPtr).toNat + 32 ≤
        state.memory.size) :
    ∀ q, q ≤ count →
      (fullWordIterate dataPtr dataLen limbsPtr q state).memory.size = state.memory.size := by
  intro q hq
  apply fullWordIterate_memory_size_of_bound
  intro j hj
  exact hbound j (by omega)

/-- When the destination payload is initially implicit, generated stores materialize it one
contiguous word at a time. -/
theorem fullWordIterate_memory_size_contiguous
    (dataPtr dataLen : UInt256) (limbsPtr start count : Nat) (state : FullWordState)
    (hindex : state.index = UInt256.ofNat start)
    (hsize : state.memory.size = limbsPtr + 32 + 32 * start)
    (hfit : limbsPtr + 32 + 32 * (start + count) < UInt256.size) :
    (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count state).memory.size =
      limbsPtr + 32 + 32 * (start + count) := by
  induction count generalizing state start with
  | zero => simpa using hsize
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen (UInt256.ofNat limbsPtr) state
      have hdest : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat =
          limbsPtr + 32 + 32 * start := by
        rw [hindex]
        exact fullWordWriteAddress_toNat (by omega)
      have hnextSize : next.memory.size = limbsPtr + 32 + 32 * (start + 1) := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        apply toByteArray_write32_size_of_ge _ _ _ state.memory.size
          (limbsPtr + 32 + 32 * (start + 1)) rfl
        · rw [hdest, hsize]
        · rw [hdest, hsize, Nat.sub_self]
          exact lt_usize 0 (by norm_num)
        · omega
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next, fullWordAdvance]
        rw [hindex, u256_add_comm, u256_one_add_ofNat]
      have hrest := ih (start + 1) next hnextIndex hnextSize (by omega)
      simpa only [next, fullWordIterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Contiguous destination extension preserves an older in-bounds source word below the payload. -/
theorem fullWordIterate_read_below_contiguous
    (dataPtr dataLen : UInt256) (limbsPtr start count : Nat) (state : FullWordState)
    (read : Nat)
    (hindex : state.index = UInt256.ofNat start)
    (hsize : state.memory.size = limbsPtr + 32 + 32 * start)
    (hread : read + 32 ≤ state.memory.size)
    (hbelow : read + 32 ≤ limbsPtr + 32 + 32 * start)
    (hfit : limbsPtr + 32 + 32 * (start + count) < UInt256.size) :
    (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count state).memory.readWithPadding
        read 32 = state.memory.readWithPadding read 32 := by
  induction count generalizing state start with
  | zero => rfl
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen (UInt256.ofNat limbsPtr) state
      have hdest : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat =
          limbsPtr + 32 + 32 * start := by
        rw [hindex]
        exact fullWordWriteAddress_toNat (by omega)
      have hgap : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat -
          state.memory.size < USize.size := by
        rw [hdest, hsize, Nat.sub_self]
        exact lt_usize 0 (by norm_num)
      have hfirst : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        exact toByteArray_write_read_below_of_gap _ _ _ _ hread
          (by rw [hdest]; exact hbelow) hgap
      have hnextSize : next.memory.size = limbsPtr + 32 + 32 * (start + 1) := by
        exact fullWordIterate_memory_size_contiguous dataPtr dataLen limbsPtr start 1 state
          hindex hsize (by omega)
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next, fullWordAdvance]
        rw [hindex, u256_add_comm, u256_one_add_ofNat]
      have hrest := ih (start + 1) next hnextIndex hnextSize
        (by rw [hnextSize]; omega) (by omega) (by omega)
      simpa only [next, fullWordIterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hrest.trans hfirst

/-- Contiguous destination extension preserves an arbitrary older padded slice below the payload. -/
theorem fullWordIterate_read_below_len_contiguous
    (dataPtr dataLen : UInt256) (limbsPtr start count : Nat) (state : FullWordState)
    (read len : Nat)
    (hindex : state.index = UInt256.ofNat start)
    (hsize : state.memory.size = limbsPtr + 32 + 32 * start)
    (hread : read + len ≤ state.memory.size)
    (hbelow : read + len ≤ limbsPtr + 32 + 32 * start)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hfit : limbsPtr + 32 + 32 * (start + count) < UInt256.size) :
    (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count state).memory.readWithPadding
        read len = state.memory.readWithPadding read len := by
  induction count generalizing state start with
  | zero => rfl
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen (UInt256.ofNat limbsPtr) state
      have hdest : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat =
          limbsPtr + 32 + 32 * start := by
        rw [hindex]
        exact fullWordWriteAddress_toNat (by omega)
      have hgap : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat -
          state.memory.size < USize.size := by
        rw [hdest, hsize, Nat.sub_self]
        exact lt_usize 0 (by norm_num)
      have hfirst : next.memory.readWithPadding read len =
          state.memory.readWithPadding read len := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        exact toByteArray_write_read_below_len_padded_of_gap _ _ _ _ _
          (by rw [hdest]; exact hbelow) hpos hlen64 hgap
      have hnextSize : next.memory.size = limbsPtr + 32 + 32 * (start + 1) := by
        exact fullWordIterate_memory_size_contiguous dataPtr dataLen limbsPtr start 1 state
          hindex hsize (by omega)
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next, fullWordAdvance]
        rw [hindex, u256_add_comm, u256_one_add_ofNat]
      have hrest := ih (start + 1) next hnextIndex hnextSize
        (by rw [hnextSize]; omega) (by omega) (by omega)
      simpa only [next, fullWordIterate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hrest.trans hfirst

/-- Every slot produced by an arbitrary bounded full-word conversion equals the concrete load at
the corresponding generated iteration. -/
theorem fullWordIterate_written_word
    (dataPtr dataLen : UInt256) (limbsPtr start count : Nat)
    (state : FullWordState) (value : Nat → Nat)
    (hindex : state.index = UInt256.ofNat start)
    (hfit : limbsPtr + 32 + 32 * (start + count) < UInt256.size)
    (hcapacity : limbsPtr + 32 + 32 * (start + count) ≤ state.memory.size)
    (hload : ∀ q, q < count →
      let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) q state
      (fullWordReadValue current.memory current.activeWords current.index dataPtr dataLen).toNat =
        value q) :
    ∀ q, q < count →
      MultiLimbMemoryModel.memoryWordNat
        (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count state).memory
        (limbsPtr + 32 + 32 * (start + q)) = value q := by
  induction count generalizing state start value with
  | zero => simp
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen (UInt256.ofNat limbsPtr) state
      have hstartFit : limbsPtr + 32 + 32 * (start + 1) < UInt256.size := by omega
      have hdest : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat =
          limbsPtr + 32 + 32 * start := by
        rw [hindex]
        exact fullWordWriteAddress_toNat (by omega)
      have hfirstIn : limbsPtr + 32 + 32 * start + 32 ≤ state.memory.size := by omega
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp only [next, fullWordAdvance, fullWordIterationMemory]
        exact write_size_of_inBounds_from _ _ 0 _ 32 (by decide)
          (by rw [toByteArray_size]) (by rw [hdest]; omega)
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next, fullWordAdvance]
        rw [hindex, u256_add_comm, u256_one_add_ofNat]
      have hboundNext : ∀ j, j < count →
          (fullWordWriteAddress (next.index + UInt256.ofNat j)
            (UInt256.ofNat limbsPtr)).toNat + 32 ≤ next.memory.size := by
        intro j hj
        have hadd : UInt256.ofNat (start + 1) + UInt256.ofNat j =
            UInt256.ofNat (start + 1 + j) := by
          apply u256_inj
          change (UInt256.add (UInt256.ofNat (start + 1)) (UInt256.ofNat j)).toNat = _
          rw [uadd_ofNat_toNat (by omega) (by omega) (by omega),
            UInt256.toNat_ofNat_of_lt (by omega)]
        rw [hnextIndex, hadd, fullWordWriteAddress_toNat (by omega), hnextSize]
        omega
      have hsizeNext : ∀ j, j ≤ count →
          (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next).memory.size =
            next.memory.size :=
        fullWordIterate_memory_size_prefix _ _ _ _ _ hboundNext
      have hinNext : ∀ j, j < count →
          let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next
          (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
            current.memory.size := by
        intro j hj
        dsimp only
        have hcurrentIndex :
            (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next).index =
              next.index + UInt256.ofNat j := fullWordIterate_index _ _ _ _ _
        rw [hcurrentIndex, hsizeNext j (by omega)]
        exact hboundNext j hj
      have haboveNext : ∀ j, j < count →
          let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next
          limbsPtr + 32 + 32 * start + 32 ≤
            (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat := by
        intro j hj
        dsimp only
        rw [fullWordIterate_index, hnextIndex]
        have hadd : UInt256.ofNat (start + 1) + UInt256.ofNat j =
            UInt256.ofNat (start + 1 + j) := by
          apply u256_inj
          change (UInt256.add (UInt256.ofNat (start + 1)) (UInt256.ofNat j)).toNat = _
          rw [uadd_ofNat_toNat (by omega) (by omega) (by omega),
            UInt256.toNat_ofNat_of_lt (by omega)]
        rw [hadd, fullWordWriteAddress_toNat (by omega)]
        omega
      have hfirstStored : MultiLimbMemoryModel.memoryWordNat next.memory
          (limbsPtr + 32 + 32 * start) = value 0 := by
        rw [← hdest]
        have hgap : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat -
            state.memory.size < USize.size := by
          rw [Nat.sub_eq_zero_of_le (by rw [hdest]; omega)]
          exact lt_usize 0 (by norm_num)
        rw [show next.memory = fullWordIterationMemory state.memory state.activeWords
          state.index dataPtr dataLen (UInt256.ofNat limbsPtr) by rfl,
          MultiLimbMemoryModel.fullWordIterationMemory_word _ _ _ _ _ _ hgap,
          show (fullWordReadValue state.memory state.activeWords state.index dataPtr dataLen).toNat =
            value 0 by simpa only [fullWordIterate] using hload 0 (by omega)]
      have hfirstFinal : MultiLimbMemoryModel.memoryWordNat
          (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count next).memory
          (limbsPtr + 32 + 32 * start) = value 0 := by
        unfold MultiLimbMemoryModel.memoryWordNat
        rw [fullWordIterate_read_below _ _ _ _ _ _ hinNext haboveNext]
        exact hfirstStored
      have hloadNext : ∀ j, j < count →
          let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next
          (fullWordReadValue current.memory current.activeWords current.index dataPtr dataLen).toNat =
            (fun q => value (q + 1)) j := by
        intro j hj
        simpa only [next, fullWordIterate_advance, Nat.add_comm] using
          hload (j + 1) (by omega)
      have hrest := ih (state := next) (start := start + 1)
        (value := fun q => value (q + 1)) hnextIndex (by omega)
        (by rw [hnextSize]; omega) hloadNext
      intro q hq
      rw [show fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) (count + 1) state =
          fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count next by rfl]
      cases q with
      | zero => simpa using hfirstFinal
      | succ q =>
          have hr := hrest q (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

/-- Contiguous payload materialization has the same per-slot semantics as the in-bounds case. -/
theorem fullWordIterate_written_word_contiguous
    (dataPtr dataLen : UInt256) (limbsPtr start count : Nat)
    (state : FullWordState) (value : Nat → Nat)
    (hindex : state.index = UInt256.ofNat start)
    (hsize : state.memory.size = limbsPtr + 32 + 32 * start)
    (hfit : limbsPtr + 32 + 32 * (start + count) < UInt256.size)
    (hload : ∀ q, q < count →
      let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) q state
      (fullWordReadValue current.memory current.activeWords current.index dataPtr dataLen).toNat =
        value q) :
    ∀ q, q < count →
      MultiLimbMemoryModel.memoryWordNat
        (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count state).memory
        (limbsPtr + 32 + 32 * (start + q)) = value q := by
  induction count generalizing state start value with
  | zero => simp
  | succ count ih =>
      let next := fullWordAdvance dataPtr dataLen (UInt256.ofNat limbsPtr) state
      have hdest : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat =
          limbsPtr + 32 + 32 * start := by
        rw [hindex]
        exact fullWordWriteAddress_toNat (by omega)
      have hnextSize : next.memory.size = limbsPtr + 32 + 32 * (start + 1) := by
        exact fullWordIterate_memory_size_contiguous dataPtr dataLen limbsPtr start 1 state
          hindex hsize (by omega)
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next, fullWordAdvance]
        rw [hindex, u256_add_comm, u256_one_add_ofNat]
      have hfirstStored : MultiLimbMemoryModel.memoryWordNat next.memory
          (limbsPtr + 32 + 32 * start) = value 0 := by
        rw [← hdest]
        have hgap : (fullWordWriteAddress state.index (UInt256.ofNat limbsPtr)).toNat -
            state.memory.size < USize.size := by
          rw [hdest, hsize, Nat.sub_self]
          exact lt_usize 0 (by norm_num)
        rw [show next.memory = fullWordIterationMemory state.memory state.activeWords
          state.index dataPtr dataLen (UInt256.ofNat limbsPtr) by rfl,
          MultiLimbMemoryModel.fullWordIterationMemory_word _ _ _ _ _ _ hgap,
          show (fullWordReadValue state.memory state.activeWords state.index dataPtr dataLen).toNat =
            value 0 by simpa only [fullWordIterate] using hload 0 (by omega)]
      have hfirstFinal : MultiLimbMemoryModel.memoryWordNat
          (fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count next).memory
          (limbsPtr + 32 + 32 * start) = value 0 := by
        unfold MultiLimbMemoryModel.memoryWordNat
        rw [fullWordIterate_read_below_contiguous dataPtr dataLen limbsPtr (start + 1)
          count next (limbsPtr + 32 + 32 * start) hnextIndex hnextSize
          (by rw [hnextSize]; omega) (by omega) (by omega)]
        exact hfirstStored
      have hloadNext : ∀ j, j < count →
          let current := fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) j next
          (fullWordReadValue current.memory current.activeWords current.index dataPtr dataLen).toNat =
            (fun q => value (q + 1)) j := by
        intro j hj
        simpa only [next, fullWordIterate_advance, Nat.add_comm] using
          hload (j + 1) (by omega)
      have hrest := ih (state := next) (start := start + 1)
        (value := fun q => value (q + 1)) hnextIndex hnextSize (by omega) hloadNext
      intro q hq
      rw [show fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) (count + 1) state =
          fullWordIterate dataPtr dataLen (UInt256.ofNat limbsPtr) count next by rfl]
      cases q with
      | zero => simpa using hfirstFinal
      | succ q =>
          have hr := hrest q (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

/-- The complete full-word phase stores exactly the low-to-high 32-byte chunks of the original
big-endian source payload. -/
theorem fullWordIterate_word_eq_source
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * (dataLen / 32) ≤ mem.size)
    (hmemActive : mem.size ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    ∀ q, q < dataLen / 32 →
      MultiLimbMemoryModel.memoryWordNat
        (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) (dataLen / 32) (fullWordInitialState mem aw)).memory
        (limbsPtr + 32 + 32 * q) =
      Model.bytesToNatPadded mem
        (dataPtr + 32 + dataLen - 32 * (q + 1)) 32 := by
  let initial := fullWordInitialState mem aw
  have hindex (j : Nat) :
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).index = UInt256.ofNat j := by
    rw [fullWordIterate_index]
    change (⟨0⟩ : UInt256) + UInt256.ofNat j = UInt256.ofNat j
    exact u256_zero_add _
  have hwriteBound : ∀ j, j < dataLen / 32 →
      (fullWordWriteAddress (initial.index + UInt256.ofNat j)
        (UInt256.ofNat limbsPtr)).toNat + 32 ≤ initial.memory.size := by
    intro j hj
    change (fullWordWriteAddress ((⟨0⟩ : UInt256) + UInt256.ofNat j)
      (UInt256.ofNat limbsPtr)).toNat + 32 ≤ mem.size
    rw [u256_zero_add, fullWordWriteAddress_toNat (by omega)]
    omega
  have hsizePrefix : ∀ j, j ≤ dataLen / 32 →
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).memory.size = mem.size := by
    simpa only [initial, fullWordInitialState] using
      fullWordIterate_memory_size_prefix (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) (UInt256.ofNat limbsPtr) (dataLen / 32) initial
        hwriteBound
  have haccess : ∀ j, j < dataLen / 32 →
      let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial
      (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
          (UInt256.ofNat dataLen)).toNat + 32 ≤ 32 * aw.toNat ∧
        (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
          32 * aw.toNat := by
    intro j hj
    dsimp only
    rw [hindex]
    constructor
    · rw [fullWordReadAddress_toNat hlen (by
          have hm := Nat.mul_div_le dataLen 32
          omega) (by omega)]
      omega
    · rw [fullWordWriteAddress_toNat (by omega)]
      omega
  have hawPrefix (j : Nat) (hj : j ≤ dataLen / 32) :
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).activeWords = aw := by
    induction j with
    | zero => rfl
    | succ j ih =>
        let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) j initial
        have ha := haccess j (by omega)
        have hcurrentAw : current.activeWords = aw := ih (by omega)
        have hreadAw : fullWordReadActiveWords current.activeWords current.index
            (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) = current.activeWords := by
          unfold fullWordReadActiveWords
          rw [machineM_eq_of_access (by simpa only [current, hcurrentAw] using ha.1),
            u256_ofNat_toNat]
        have hwriteAccess :
            (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
              32 * current.activeWords.toNat := by
          simpa only [current, hcurrentAw] using ha.2
        have hstep : (fullWordAdvance (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) current).activeWords = current.activeWords := by
          dsimp only [fullWordAdvance]
          unfold fullWordIterationActiveWords
          rw [hreadAw, machineM_eq_of_access hwriteAccess, u256_ofNat_toNat]
        have hsucc : fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) (j + 1) initial =
          fullWordAdvance (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) current := by
          rw [fullWordIterate_add]
          rfl
        rw [hsucc, hstep, hcurrentAw]
  have hload : ∀ j, j < dataLen / 32 →
      let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial
      (fullWordReadValue current.memory current.activeWords current.index
        (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)).toNat =
      Model.bytesToNatPadded mem
        (dataPtr + 32 + dataLen - 32 * (j + 1)) 32 := by
    intro j hj
    dsimp only
    let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr) j initial
    let source := dataPtr + 32 + dataLen - 32 * (j + 1)
    have hchunk : 32 * (j + 1) ≤ dataLen := by
      have hm := Nat.mul_div_le dataLen 32
      omega
    have haddr : (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen)).toNat = source := by
      dsimp only [current, source]
      rw [hindex]
      exact fullWordReadAddress_toNat hlen hchunk (by omega)
    have hcurrentSize : current.memory.size = mem.size := by
      exact hsizePrefix j (by omega)
    have hcurrentAw : current.activeWords = aw := hawPrefix j (by omega)
    have hin : ∀ t, t < j →
        let s := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) t initial
        (fullWordWriteAddress s.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
          s.memory.size := by
      intro t ht
      dsimp only
      rw [hindex, fullWordWriteAddress_toNat (by omega), hsizePrefix t (by omega)]
      omega
    have habove : ∀ t, t < j →
        let s := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) t initial
        source + 32 ≤
          (fullWordWriteAddress s.index (UInt256.ofNat limbsPtr)).toNat := by
      intro t ht
      dsimp only
      rw [hindex, fullWordWriteAddress_toNat (by omega)]
      dsimp only [source]
      omega
    have hsourceRead : current.memory.readWithPadding source 32 =
        mem.readWithPadding source 32 := by
      simpa only [current, initial, fullWordInitialState] using
        fullWordIterate_read_below (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) j initial source hin habove
    have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
    have hnotActive : ¬ fullWordReadAddress current.index (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) ≥ aw * ⟨32⟩ := by
      intro hge
      have hgeNat : (aw * ⟨32⟩).toNat ≤
          (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
            (UInt256.ofNat dataLen)).toNat := hge
      rw [hawMul, haddr] at hgeNat
      omega
    have hreadValue := MultiLimbMemoryModel.fullWordReadValue_toNat_eq_model
      current.memory aw current.index (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
      (by rw [haddr, hcurrentSize]; omega) hnotActive (by rw [haddr]; omega)
    rw [hcurrentAw]
    rw [hreadValue, haddr]
    apply model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by decide)
    exact hsourceRead
  have hwritten := fullWordIterate_written_word
    (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32)
    initial (fun q => Model.bytesToNatPadded mem
      (dataPtr + 32 + dataLen - 32 * (q + 1)) 32)
    (by rfl) (by omega)
    (by simpa only [initial, fullWordInitialState, Nat.zero_add] using hcapacity) hload
  intro q hq
  simpa only [initial, Nat.zero_add] using hwritten q hq

/-- The same source-chunk theorem for Solidity's actual representation, where the allocated
payload is active but initially implicit and each store extends the concrete byte array. -/
theorem fullWordIterate_word_eq_source_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hsize : mem.size = limbsPtr + 32)
    (hactive : limbsPtr + 32 + 32 * (dataLen / 32) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    ∀ q, q < dataLen / 32 →
      MultiLimbMemoryModel.memoryWordNat
        (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) (dataLen / 32) (fullWordInitialState mem aw)).memory
        (limbsPtr + 32 + 32 * q) =
      Model.bytesToNatPadded mem
        (dataPtr + 32 + dataLen - 32 * (q + 1)) 32 := by
  let initial := fullWordInitialState mem aw
  have hindex (j : Nat) :
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).index = UInt256.ofNat j := by
    rw [fullWordIterate_index]
    change (⟨0⟩ : UInt256) + UInt256.ofNat j = UInt256.ofNat j
    exact u256_zero_add _
  have hsizePrefix (j : Nat) (hj : j ≤ dataLen / 32) :
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).memory.size = limbsPtr + 32 + 32 * j := by
    exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen) limbsPtr 0 j initial rfl (by simpa [initial] using hsize)
      (by omega) |>.trans (by simp)
  have haccess : ∀ j, j < dataLen / 32 →
      let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial
      (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
          (UInt256.ofNat dataLen)).toNat + 32 ≤ 32 * aw.toNat ∧
        (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
          32 * aw.toNat := by
    intro j hj
    dsimp only
    rw [hindex]
    constructor
    · rw [fullWordReadAddress_toNat hlen (by
          have hm := Nat.mul_div_le dataLen 32
          omega) (by omega)]
      omega
    · rw [fullWordWriteAddress_toNat (by omega)]
      omega
  have hawPrefix (j : Nat) (hj : j ≤ dataLen / 32) :
      (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial).activeWords = aw := by
    induction j with
    | zero => rfl
    | succ j ih =>
        let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) j initial
        have ha := haccess j (by omega)
        have hcurrentAw : current.activeWords = aw := ih (by omega)
        have hreadAw : fullWordReadActiveWords current.activeWords current.index
            (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) = current.activeWords := by
          unfold fullWordReadActiveWords
          rw [machineM_eq_of_access (by simpa only [current, hcurrentAw] using ha.1),
            u256_ofNat_toNat]
        have hwriteAccess :
            (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
              32 * current.activeWords.toNat := by
          simpa only [current, hcurrentAw] using ha.2
        have hstep : (fullWordAdvance (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) current).activeWords = current.activeWords := by
          dsimp only [fullWordAdvance]
          unfold fullWordIterationActiveWords
          rw [hreadAw, machineM_eq_of_access hwriteAccess, u256_ofNat_toNat]
        have hsucc : fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) (j + 1) initial =
          fullWordAdvance (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) current := by
          rw [fullWordIterate_add]
          rfl
        rw [hsucc, hstep, hcurrentAw]
  have hload : ∀ j, j < dataLen / 32 →
      let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) j initial
      (fullWordReadValue current.memory current.activeWords current.index
        (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)).toNat =
      Model.bytesToNatPadded mem
        (dataPtr + 32 + dataLen - 32 * (j + 1)) 32 := by
    intro j hj
    dsimp only
    let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr) j initial
    let source := dataPtr + 32 + dataLen - 32 * (j + 1)
    have hchunk : 32 * (j + 1) ≤ dataLen := by
      have hm := Nat.mul_div_le dataLen 32
      omega
    have haddr : (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen)).toNat = source := by
      dsimp only [current, source]
      rw [hindex]
      exact fullWordReadAddress_toNat hlen hchunk (by omega)
    have hcurrentSize : current.memory.size = limbsPtr + 32 + 32 * j :=
      hsizePrefix j (by omega)
    have hcurrentAw : current.activeWords = aw := hawPrefix j (by omega)
    have hsourceRead : current.memory.readWithPadding source 32 =
        mem.readWithPadding source 32 := by
      simpa only [current, initial, fullWordInitialState] using
        fullWordIterate_read_below_contiguous (UInt256.ofNat dataPtr)
          (UInt256.ofNat dataLen) limbsPtr 0 j initial source rfl
          (by simpa only [initial, fullWordInitialState, Nat.zero_add] using hsize)
          (by change source + 32 ≤ mem.size; rw [hsize]; dsimp only [source]; omega)
          (by dsimp only [source]; omega) (by omega)
    have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
    have hnotActive : ¬ fullWordReadAddress current.index (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) ≥ aw * ⟨32⟩ := by
      intro hge
      have hgeNat : (aw * ⟨32⟩).toNat ≤
          (fullWordReadAddress current.index (UInt256.ofNat dataPtr)
            (UInt256.ofNat dataLen)).toNat := hge
      rw [hawMul, haddr] at hgeNat
      omega
    have hreadValue := MultiLimbMemoryModel.fullWordReadValue_toNat_eq_model
      current.memory aw current.index (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
      (by rw [haddr, hcurrentSize]; dsimp only [source]; omega) hnotActive
      (by rw [haddr]; exact lt_of_lt_of_le (by dsimp only [source]; omega) hmem64.le)
    rw [hcurrentAw, hreadValue, haddr]
    apply model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by decide)
    exact hsourceRead
  have hwritten := fullWordIterate_written_word_contiguous
    (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32)
    initial (fun q => Model.bytesToNatPadded mem
      (dataPtr + 32 + dataLen - 32 * (q + 1)) 32)
    rfl (by simpa only [initial, fullWordInitialState, Nat.zero_add] using hsize)
    (by omega) hload
  intro q hq
  simpa only [initial, Nat.zero_add] using hwritten q hq

/-- One full-word conversion iteration preserves active words when its source and destination are
already active. -/
theorem fullWordIterationActiveWords_eq
    (aw i dataPtr dataLen limbsPtr : UInt256)
    (hread : (fullWordReadAddress i dataPtr dataLen).toNat + 32 ≤ 32 * aw.toNat)
    (hwrite : (fullWordWriteAddress i limbsPtr).toNat + 32 ≤ 32 * aw.toNat) :
    fullWordIterationActiveWords aw i dataPtr dataLen limbsPtr = aw := by
  unfold fullWordIterationActiveWords fullWordReadActiveWords
  rw [machineM_eq_of_access hread, u256_ofNat_toNat,
    machineM_eq_of_access hwrite, u256_ofNat_toNat]

/-- Every active-word counter in a bounded full-word conversion remains the initial counter. -/
theorem fullWordIterate_activeWords_eq
    (dataPtr dataLen limbsPtr : UInt256) (n : Nat) (state : FullWordState)
    (haccess : ∀ j, j < n →
      let current := fullWordIterate dataPtr dataLen limbsPtr j state
      (fullWordReadAddress current.index dataPtr dataLen).toNat + 32 ≤
          32 * state.activeWords.toNat ∧
        (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤
          32 * state.activeWords.toNat) :
    (fullWordIterate dataPtr dataLen limbsPtr n state).activeWords =
      state.activeWords := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := fullWordAdvance dataPtr dataLen limbsPtr state
      have hfirst := haccess 0 (by omega)
      have hnextAw : next.activeWords = state.activeWords := by
        simpa only [next, fullWordAdvance] using
          fullWordIterationActiveWords_eq state.activeWords state.index dataPtr dataLen limbsPtr
            hfirst.1 hfirst.2
      have hrestAccess : ∀ j, j < n →
          let current := fullWordIterate dataPtr dataLen limbsPtr j next
          (fullWordReadAddress current.index dataPtr dataLen).toNat + 32 ≤
              32 * next.activeWords.toNat ∧
            (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤
              32 * next.activeWords.toNat := by
        intro j hj
        rw [hnextAw]
        simpa only [next, fullWordIterate_advance] using haccess (j + 1) (by omega)
      have hrest := ih next hrestAccess
      rw [show fullWordIterate dataPtr dataLen limbsPtr (n + 1) state =
          fullWordIterate dataPtr dataLen limbsPtr n next by rfl,
        hrest, hnextAw]

/-- The optional partial-limb conversion likewise preserves active words. -/
theorem partialWordActiveWords_eq
    (aw dataPtr dataLen limbsPtr : UInt256)
    (hread : (partialWordReadAddress dataPtr).toNat + 32 ≤ 32 * aw.toNat)
    (hwrite : (partialWordWriteAddress dataLen limbsPtr).toNat + 32 ≤
      32 * aw.toNat) :
    partialWordActiveWords aw dataPtr dataLen limbsPtr = aw := by
  unfold partialWordActiveWords partialWordReadActiveWords
  rw [machineM_eq_of_access hread, u256_ofNat_toNat,
    machineM_eq_of_access hwrite, u256_ofNat_toNat]

/-- A complete generated conversion preserves active words under explicit access geometry for all
full iterations and the optional partial iteration. -/
theorem bytesToLimbsActiveWords_eq
    (mem : ByteArray) (aw dataPtr limbsPtr : UInt256) (dataLen : Nat)
    (hfull : ∀ j, j < dataLen / 32 →
      let current := fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
        (fullWordInitialState mem aw)
      (fullWordReadAddress current.index dataPtr (UInt256.ofNat dataLen)).toNat + 32 ≤
          32 * aw.toNat ∧
        (fullWordWriteAddress current.index limbsPtr).toNat + 32 ≤
          32 * aw.toNat)
    (hpartialRead : dataLen % 32 ≠ 0 →
      (partialWordReadAddress dataPtr).toNat + 32 ≤ 32 * aw.toNat)
    (hpartialWrite : dataLen % 32 ≠ 0 →
      (partialWordWriteAddress (UInt256.ofNat dataLen) limbsPtr).toNat + 32 ≤
        32 * aw.toNat) :
    MultiLimbGenerated.bytesToLimbsActiveWords mem aw dataPtr limbsPtr dataLen = aw := by
  let final := fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr
    (dataLen / 32) (fullWordInitialState mem aw)
  have hfullAw : final.activeWords = aw := by
    simpa only [final, fullWordInitialState] using
      fullWordIterate_activeWords_eq dataPtr (UInt256.ofNat dataLen) limbsPtr
        (dataLen / 32) (fullWordInitialState mem aw) hfull
  unfold MultiLimbGenerated.bytesToLimbsActiveWords bytesToLimbsFullState
  change bytesToLimbsSuffixActiveWords final.activeWords dataPtr limbsPtr dataLen = aw
  rw [hfullAw]
  by_cases hrem : dataLen % 32 = 0
  · simp [bytesToLimbsSuffixActiveWords, hrem]
  · simp only [bytesToLimbsSuffixActiveWords, hrem, ↓reduceIte]
    exact partialWordActiveWords_eq aw dataPtr (UInt256.ofNat dataLen) limbsPtr
      (hpartialRead hrem) (hpartialWrite hrem)

/-- The active-word counter returned by `new uint256[](words)` covers its complete payload and is
representable as an EVM byte extent. -/
theorem newWordArrayWords_range
    (aw : UInt256) (fp words : Nat)
    (hwords : 0 < words)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize words + 31 < UInt256.size) :
    fp + 32 + 32 * words ≤ 32 * (newWordArrayWords aw fp words).toNat ∧
      (newWordArrayWords aw fp words).toNat * 32 < UInt256.size := by
  have hstoreFit : fp + 32 + 31 < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hstoreMFit := machineM_mul32_lt_size hawFit hstoreFit
  have hstoreMLt : MachineState.M aw.toNat fp 32 < UInt256.size := by
    have hle := Nat.mul_le_mul_left (MachineState.M aw.toNat fp 32)
      (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hstoreMFit
  have hstoreNat : (newBytesStoreWords aw fp).toNat =
      MachineState.M aw.toNat fp 32 := by
    unfold newBytesStoreWords
    rw [UInt256.toNat_ofNat_of_lt hstoreMLt]
  have hpayloadFit : fp + 32 + 32 * words + 31 < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hfinalMFit :
      MachineState.M (newBytesStoreWords aw fp).toNat
          (fp + 32) (wordArrayPayloadSize words) * 32 < UInt256.size := by
    apply machineM_mul32_lt_size
    · simpa only [hstoreNat] using hstoreMFit
    · simpa only [wordArrayPayloadSize] using hpayloadFit
  have hfinalMLt :
      MachineState.M (newBytesStoreWords aw fp).toNat
          (fp + 32) (wordArrayPayloadSize words) < UInt256.size := by
    have hle := Nat.mul_le_mul_left
      (MachineState.M (newBytesStoreWords aw fp).toNat
        (fp + 32) (wordArrayPayloadSize words)) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hfinalMFit
  have hfinalNat : (newWordArrayWords aw fp words).toNat =
      MachineState.M (newBytesStoreWords aw fp).toNat
        (fp + 32) (wordArrayPayloadSize words) := by
    unfold newWordArrayWords
    rw [UInt256.toNat_ofNat_of_lt hfinalMLt]
  constructor
  · rw [hfinalNat]
    simpa only [wordArrayPayloadSize] using
      (machineM_access_le (s := (newBytesStoreWords aw fp).toNat)
        (off := fp + 32) (len := 32 * words) (by omega))
  · rwa [hfinalNat]

/-- Under the allocated-array geometry, the full-word conversion phase preserves concrete memory
size. -/
theorem bytesToLimbsFullState_memory_size_eq
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size)
    (hcapacity : limbsPtr + 32 + 32 * (dataLen / 32) ≤ mem.size) :
    (bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).memory.size = mem.size := by
  let initial := fullWordInitialState mem aw
  have hbound : ∀ j, j < dataLen / 32 →
      (fullWordWriteAddress (initial.index + UInt256.ofNat j)
        (UInt256.ofNat limbsPtr)).toNat + 32 ≤ initial.memory.size := by
    intro j hj
    change (fullWordWriteAddress ((⟨0⟩ : UInt256) + UInt256.ofNat j)
      (UInt256.ofNat limbsPtr)).toNat + 32 ≤ mem.size
    rw [u256_zero_add, fullWordWriteAddress_toNat (by omega)]
    omega
  unfold bytesToLimbsFullState
  simpa only [initial] using fullWordIterate_memory_size_of_bound
    (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) (UInt256.ofNat limbsPtr)
      (dataLen / 32) initial hbound

/-- The full-word phase also preserves the active-word counter when the source and allocated
destination are covered by the caller's active extent. -/
theorem bytesToLimbsFullState_activeWords_eq_of_geometry
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * (dataLen / 32) ≤ mem.size)
    (hactive : mem.size ≤ 32 * aw.toNat)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size) :
    (bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).activeWords = aw := by
  apply fullWordIterate_activeWords_eq
  intro j hj
  dsimp only
  rw [fullWordIterate_index]
  simp only [fullWordInitialState, u256_zero_add]
  constructor
  · rw [fullWordReadAddress_toNat hlen (by
        have hm := Nat.mul_div_le dataLen 32
        omega) (by omega)]
    omega
  · rw [fullWordWriteAddress_toNat (by omega)]
    omega

/-- On the non-aligned path, the concrete optional destination limb is exactly the leading source
prefix after the generated right shift. -/
theorem bytesToLimbsMemory_partial_word_eq_source
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024) (hrem : dataLen % 32 ≠ 0)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ mem.size)
    (hactive : mem.size ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryWordNat
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      (limbsPtr + 32 + 32 * (dataLen / 32)) =
    Model.bytesToNatPadded mem (dataPtr + 32) (dataLen % 32) := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
  have hfullFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by omega
  have hfullCapacity : limbsPtr + 32 + 32 * (dataLen / 32) ≤ mem.size := by omega
  have hfullSize : full.memory.size = mem.size := by
    exact bytesToLimbsFullState_memory_size_eq mem aw dataPtr limbsPtr dataLen
      hfullFit hfullCapacity
  have hfullAw : full.activeWords = aw := by
    exact bytesToLimbsFullState_activeWords_eq_of_geometry mem aw dataPtr limbsPtr dataLen
      hlen hsourceBefore hfullCapacity hactive hfullFit
  have hreadAddr : (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat = dataPtr + 32 :=
    partialWordReadAddress_toNat (by omega)
  have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
    partialWordWriteAddress_toNat hlen (by omega)
  have hreadAccess : (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat + 32 ≤
      32 * full.activeWords.toNat := by rw [hreadAddr, hfullAw]; omega
  have hwriteAccess : (partialWordWriteAddress (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr)).toNat + 32 ≤ 32 * full.activeWords.toNat := by
    rw [hwriteAddr, hfullAw]
    omega
  have hsourceRead : full.memory.readWithPadding (dataPtr + 32) 32 =
      mem.readWithPadding (dataPtr + 32) 32 := by
    let initial := fullWordInitialState mem aw
    have hin : ∀ j, j < dataLen / 32 →
        let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) j initial
        (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat + 32 ≤
          current.memory.size := by
      intro j hj
      dsimp only
      rw [fullWordIterate_index]
      simp only [initial, fullWordInitialState, u256_zero_add]
      rw [fullWordWriteAddress_toNat (by omega)]
      have hs := fullWordIterate_memory_size_prefix
        (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen) (UInt256.ofNat limbsPtr)
        (dataLen / 32) initial (by
          intro t ht
          change (fullWordWriteAddress ((⟨0⟩ : UInt256) + UInt256.ofNat t)
            (UInt256.ofNat limbsPtr)).toNat + 32 ≤ mem.size
          rw [u256_zero_add, fullWordWriteAddress_toNat (by omega)]
          omega) j (by omega)
      have hs' :
          (fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
            (UInt256.ofNat limbsPtr) j
            { index := ⟨0⟩, memory := mem, activeWords := aw }).memory.size = mem.size := by
        simpa only [initial, fullWordInitialState] using hs
      rw [hs']
      omega
    have habove : ∀ j, j < dataLen / 32 →
        let current := fullWordIterate (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
          (UInt256.ofNat limbsPtr) j initial
        dataPtr + 32 + 32 ≤
          (fullWordWriteAddress current.index (UInt256.ofNat limbsPtr)).toNat := by
      intro j hj
      dsimp only
      rw [fullWordIterate_index]
      simp only [initial, fullWordInitialState, u256_zero_add]
      rw [fullWordWriteAddress_toNat (by omega)]
      omega
    simpa only [full, bytesToLimbsFullState, initial] using
      fullWordIterate_read_below (UInt256.ofNat dataPtr) (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr) (dataLen / 32) initial (dataPtr + 32) hin habove
  have hawMul : (full.activeWords * (⟨32⟩ : UInt256)).toNat =
      full.activeWords.toNat * 32 := by
    have hfitAw : full.activeWords.toNat * 32 < UInt256.size := by rw [hfullAw]; exact hawFit
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := full.activeWords) (b := (⟨32⟩ : UInt256)) hfitAw
  have hnotActive : ¬ partialWordReadAddress (UInt256.ofNat dataPtr) ≥
      full.activeWords * ⟨32⟩ := by
    intro hge
    have hn : (full.activeWords * ⟨32⟩).toNat ≤
        (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat := hge
    rw [hawMul, hreadAddr, hfullAw] at hn
    omega
  have hpartialValue := MultiLimbMemoryModel.partialWordValue_toNat_eq_model
    full.memory full.activeWords (UInt256.ofNat dataPtr)
      (UInt256.ofNat (dataLen % 32))
      (by rw [hreadAddr, hfullSize]; omega) hnotActive (by rw [hreadAddr]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
  have hremNat : (UInt256.ofNat (dataLen % 32)).toNat = dataLen % 32 :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hsourceValue :
      Model.bytesToNatPadded full.memory (dataPtr + 32) (dataLen % 32) =
        Model.bytesToNatPadded mem (dataPtr + 32) (dataLen % 32) := by
    apply model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by omega)
    have hpref := congrArg (fun b : ByteArray => b.extract 0 (dataLen % 32)) hsourceRead
    have hfull32 : full.memory.readWithPadding (dataPtr + 32) 32 =
        full.memory.extract (dataPtr + 32) (dataPtr + 32 + 32) :=
      readWithPadding_eq_extract _ _ (by rw [hfullSize]; omega)
    have hmem32 : mem.readWithPadding (dataPtr + 32) 32 =
        mem.extract (dataPtr + 32) (dataPtr + 32 + 32) :=
      readWithPadding_eq_extract _ _ (by omega)
    rw [hfull32, hmem32] at hpref
    change (full.memory.extract (dataPtr + 32) (dataPtr + 32 + 32)).extract
        0 (dataLen % 32) =
      (mem.extract (dataPtr + 32) (dataPtr + 32 + 32)).extract 0 (dataLen % 32) at hpref
    rw [extract_extract_BA, extract_extract_BA] at hpref
    rw [readWithPadding_eq_extract' _ _ _ (by omega) (by omega)
        (by rw [hfullSize]; omega),
      readWithPadding_eq_extract' _ _ _ (by omega) (by omega) (by omega)]
    have hmin : min (dataPtr + 32 + dataLen % 32) (dataPtr + 32 + 32) =
        dataPtr + 32 + dataLen % 32 := Nat.min_eq_left (by omega)
    rw [hmin] at hpref
    exact hpref
  unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
  simp only [hrem, ↓reduceIte]
  rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
  rw [← hwriteAddr]
  have hgap : (partialWordWriteAddress (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr)).toNat - full.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by rw [hwriteAddr, hfullSize, hceil] at *; omega)]
    exact lt_usize 0 (by norm_num)
  rw [MultiLimbMemoryModel.partialWordMemory_word _ _ _ _ _ _ hgap,
    hpartialValue, hreadAddr, hremNat, hsourceValue]

/-- The optional top-limb store is above every full destination limb, so all full chunks retain
their exact source values in the complete conversion memory. -/
theorem bytesToLimbsMemory_full_word_eq_source
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen q : Nat)
    (hlen : dataLen ≤ 1024) (hq : q < dataLen / 32)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ mem.size)
    (hactive : mem.size ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryWordNat
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      (limbsPtr + 32 + 32 * q) =
    Model.bytesToNatPadded mem (dataPtr + 32 + dataLen - 32 * (q + 1)) 32 := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hfullCapacity : limbsPtr + 32 + 32 * (dataLen / 32) ≤ mem.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullValue := fullWordIterate_word_eq_source mem aw dataPtr limbsPtr dataLen hlen
    hsourceBefore hfullCapacity hactive hawFit hfullFit hmem64 q hq
  by_cases hrem : dataLen % 32 = 0
  · unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    exact hfullValue
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
    have hfullSize : full.memory.size = mem.size :=
      bytesToLimbsFullState_memory_size_eq mem aw dataPtr limbsPtr dataLen
        hfullFit hfullCapacity
    have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
      partialWordWriteAddress_toNat hlen (by omega)
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
    unfold MultiLimbMemoryModel.memoryWordNat partialWordMemory
    rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
      (by rw [hwriteAddr, hfullSize, hceil] at *; omega)
      (by rw [hwriteAddr]; omega)]
    exact hfullValue

/-- The complete concrete destination payload is exactly the trusted pure little-endian splitter. -/
theorem bytesToLimbsMemory_limbs_eq_pure
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ mem.size)
    (hactive : mem.size ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryLimbs
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      limbsPtr ((dataLen + 31) / 32) =
    bytesToLimbsPure mem (dataPtr + 32) dataLen := by
  apply List.ext_getElem
  · simp
  · intro i hiConcrete hiPure
    simp only [MultiLimbMemoryModel.memoryLimbs, List.getElem_ofFn]
    by_cases hfull : i < dataLen / 32
    · rw [bytesToLimbsMemory_full_word_eq_source mem aw dataPtr limbsPtr dataLen i
        hlen hfull hsourceBefore hcapacity hactive hawFit hfit hmem64]
      exact (bytesToLimbsPure_getElem_full mem (dataPtr + 32) dataLen i hfull).symm
    · by_cases hrem : dataLen % 32 = 0
      · have hceil : (dataLen + 31) / 32 = dataLen / 32 := by omega
        simp only [MultiLimbMemoryModel.memoryLimbs_length, hceil] at hiConcrete
        omega
      · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
        simp only [MultiLimbMemoryModel.memoryLimbs_length, hceil] at hiConcrete
        have hi : i = dataLen / 32 := by omega
        subst i
        rw [bytesToLimbsMemory_partial_word_eq_source mem aw dataPtr limbsPtr dataLen
          hlen hrem hsourceBefore hcapacity hactive hawFit hfit hmem64]
        exact (bytesToLimbsPure_getElem_partial mem (dataPtr + 32) dataLen hrem).symm

/-- Consequently, the concrete converted array denotes exactly the original big-endian source
value. -/
theorem bytesToLimbsMemory_value_eq_model
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hcapacity : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ mem.size)
    (hactive : mem.size ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      limbsPtr ((dataLen + 31) / 32)) =
    Model.bytesToNatPadded mem (dataPtr + 32) dataLen := by
  rw [bytesToLimbsMemory_limbs_eq_pure mem aw dataPtr limbsPtr dataLen hlen
    hsourceBefore hcapacity hactive hawFit hfit hmem64]
  exact limbsToNat_bytesToLimbsPure mem (dataPtr + 32) dataLen

/-- Active-word stability for an implicit contiguous destination payload. -/
theorem bytesToLimbsFullState_activeWords_eq_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hactive : limbsPtr + 32 + 32 * (dataLen / 32) ≤ 32 * aw.toNat)
    (hfit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size) :
    (bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).activeWords = aw := by
  apply fullWordIterate_activeWords_eq
  intro j hj
  dsimp only
  rw [fullWordIterate_index]
  simp only [fullWordInitialState, u256_zero_add]
  constructor
  · rw [fullWordReadAddress_toNat hlen (by
        have hm := Nat.mul_div_le dataLen 32
        omega) (by omega)]
    omega
  · rw [fullWordWriteAddress_toNat (by omega)]
    omega

/-- Full destination slots retain their source values when the payload was initially implicit. -/
theorem bytesToLimbsMemory_full_word_eq_source_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen q : Nat)
    (hlen : dataLen ≤ 1024) (hq : q < dataLen / 32)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hsize : mem.size = limbsPtr + 32)
    (hactive : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryWordNat
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      (limbsPtr + 32 + 32 * q) =
    Model.bytesToNatPadded mem (dataPtr + 32 + dataLen - 32 * (q + 1)) 32 := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hqActive : limbsPtr + 32 + 32 * (dataLen / 32) ≤ 32 * aw.toNat := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hqFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullValue := fullWordIterate_word_eq_source_contiguous mem aw dataPtr limbsPtr
    dataLen hlen hsourceBefore hsize hqActive hawFit hqFit hmem64 q hq
  by_cases hrem : dataLen % 32 = 0
  · unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    exact hfullValue
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
    have hfullSize : full.memory.size = limbsPtr + 32 + 32 * (dataLen / 32) := by
      exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
        rfl (by simpa [hsize]) (by omega) |>.trans (by simp)
    have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
      partialWordWriteAddress_toNat hlen (by omega)
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
    unfold MultiLimbMemoryModel.memoryWordNat partialWordMemory
    rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
      (by rw [hwriteAddr, hfullSize]) (by rw [hwriteAddr]; omega)]
    exact hfullValue

/-- The optional top slot also has its exact source-prefix value in the implicit-payload case. -/
theorem bytesToLimbsMemory_partial_word_eq_source_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024) (hrem : dataLen % 32 ≠ 0)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hsize : mem.size = limbsPtr + 32)
    (hactive : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryWordNat
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      (limbsPtr + 32 + 32 * (dataLen / 32)) =
    Model.bytesToNatPadded mem (dataPtr + 32) (dataLen % 32) := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
  have hqActive : limbsPtr + 32 + 32 * (dataLen / 32) ≤ 32 * aw.toNat := by omega
  have hqFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by omega
  have hfullSize : full.memory.size = limbsPtr + 32 + 32 * (dataLen / 32) := by
    exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
      rfl (by simpa [hsize]) (by omega) |>.trans (by simp)
  have hfullAw : full.activeWords = aw :=
    bytesToLimbsFullState_activeWords_eq_contiguous mem aw dataPtr limbsPtr dataLen hlen
      hsourceBefore hqActive hqFit
  have hreadAddr : (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat = dataPtr + 32 :=
    partialWordReadAddress_toNat (by omega)
  have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
    partialWordWriteAddress_toNat hlen (by omega)
  have hsourceRead : full.memory.readWithPadding (dataPtr + 32) 32 =
      mem.readWithPadding (dataPtr + 32) 32 := by
    simpa only [full, bytesToLimbsFullState, fullWordInitialState] using
      fullWordIterate_read_below_contiguous (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
        (dataPtr + 32) rfl (by simpa [hsize])
        (by change dataPtr + 32 + 32 ≤ mem.size; rw [hsize]; omega)
        (by omega) (by omega)
  have hawMul : (full.activeWords * (⟨32⟩ : UInt256)).toNat =
      full.activeWords.toNat * 32 := by
    have hfitAw : full.activeWords.toNat * 32 < UInt256.size := by rw [hfullAw]; exact hawFit
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := full.activeWords) (b := (⟨32⟩ : UInt256)) hfitAw
  have hnotActive : ¬ partialWordReadAddress (UInt256.ofNat dataPtr) ≥
      full.activeWords * ⟨32⟩ := by
    intro hge
    have hn : (full.activeWords * ⟨32⟩).toNat ≤
        (partialWordReadAddress (UInt256.ofNat dataPtr)).toNat := hge
    rw [hawMul, hreadAddr, hfullAw] at hn
    omega
  have hpartialValue := MultiLimbMemoryModel.partialWordValue_toNat_eq_model
    full.memory full.activeWords (UInt256.ofNat dataPtr) (UInt256.ofNat (dataLen % 32))
      (by rw [hreadAddr, hfullSize]; omega) hnotActive
      (by rw [hreadAddr]; exact lt_of_lt_of_le (by omega) hmem64.le)
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
  have hremNat : (UInt256.ofNat (dataLen % 32)).toNat = dataLen % 32 :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hsourceValue : Model.bytesToNatPadded full.memory (dataPtr + 32) (dataLen % 32) =
      Model.bytesToNatPadded mem (dataPtr + 32) (dataLen % 32) := by
    apply model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by omega)
    have hpref := congrArg (fun b : ByteArray => b.extract 0 (dataLen % 32)) hsourceRead
    have hfull32 : full.memory.readWithPadding (dataPtr + 32) 32 =
        full.memory.extract (dataPtr + 32) (dataPtr + 32 + 32) :=
      readWithPadding_eq_extract _ _ (by rw [hfullSize]; omega)
    have hmem32 : mem.readWithPadding (dataPtr + 32) 32 =
        mem.extract (dataPtr + 32) (dataPtr + 32 + 32) :=
      readWithPadding_eq_extract _ _ (by rw [hsize]; omega)
    rw [hfull32, hmem32] at hpref
    change (full.memory.extract (dataPtr + 32) (dataPtr + 32 + 32)).extract
        0 (dataLen % 32) =
      (mem.extract (dataPtr + 32) (dataPtr + 32 + 32)).extract 0 (dataLen % 32) at hpref
    rw [extract_extract_BA, extract_extract_BA] at hpref
    rw [readWithPadding_eq_extract' _ _ _ (by omega) (by omega)
        (by rw [hfullSize]; omega),
      readWithPadding_eq_extract' _ _ _ (by omega) (by omega) (by rw [hsize]; omega)]
    have hmin : min (dataPtr + 32 + dataLen % 32) (dataPtr + 32 + 32) =
        dataPtr + 32 + dataLen % 32 := Nat.min_eq_left (by omega)
    rw [hmin] at hpref
    exact hpref
  unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
  simp only [hrem, ↓reduceIte]
  rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl, ← hwriteAddr]
  have hgap : (partialWordWriteAddress (UInt256.ofNat dataLen)
      (UInt256.ofNat limbsPtr)).toNat - full.memory.size < USize.size := by
    rw [hwriteAddr, hfullSize, Nat.sub_self]
    exact lt_usize 0 (by norm_num)
  rw [MultiLimbMemoryModel.partialWordMemory_word _ _ _ _ _ _ hgap,
    hpartialValue, hreadAddr, hremNat, hsourceValue]

/-- Complete concrete/pure payload equality for the allocator's implicit contiguous payload. -/
theorem bytesToLimbsMemory_limbs_eq_pure_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hsize : mem.size = limbsPtr + 32)
    (hactive : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    MultiLimbMemoryModel.memoryLimbs
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      limbsPtr ((dataLen + 31) / 32) =
    bytesToLimbsPure mem (dataPtr + 32) dataLen := by
  apply List.ext_getElem
  · simp
  · intro i hiConcrete hiPure
    simp only [MultiLimbMemoryModel.memoryLimbs, List.getElem_ofFn]
    by_cases hfull : i < dataLen / 32
    · rw [bytesToLimbsMemory_full_word_eq_source_contiguous mem aw dataPtr limbsPtr
        dataLen i hlen hfull hsourceBefore hsize hactive hawFit hfit hmem64]
      exact (bytesToLimbsPure_getElem_full mem (dataPtr + 32) dataLen i hfull).symm
    · by_cases hrem : dataLen % 32 = 0
      · have hceil : (dataLen + 31) / 32 = dataLen / 32 := by omega
        simp only [MultiLimbMemoryModel.memoryLimbs_length, hceil] at hiConcrete
        omega
      · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
        simp only [MultiLimbMemoryModel.memoryLimbs_length, hceil] at hiConcrete
        have hi : i = dataLen / 32 := by omega
        subst i
        rw [bytesToLimbsMemory_partial_word_eq_source_contiguous mem aw dataPtr limbsPtr
          dataLen hlen hrem hsourceBefore hsize hactive hawFit hfit hmem64]
        exact (bytesToLimbsPure_getElem_partial mem (dataPtr + 32) dataLen hrem).symm

/-- The allocator representation therefore denotes exactly its original big-endian source. -/
theorem bytesToLimbsMemory_value_eq_model_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hsize : mem.size = limbsPtr + 32)
    (hactive : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size)
    (hmem64 : mem.size < 2 ^ 64) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr) dataLen)
      limbsPtr ((dataLen + 31) / 32)) =
    Model.bytesToNatPadded mem (dataPtr + 32) dataLen := by
  rw [bytesToLimbsMemory_limbs_eq_pure_contiguous mem aw dataPtr limbsPtr dataLen hlen
    hsourceBefore hsize hactive hawFit hfit hmem64]
  exact limbsToNat_bytesToLimbsPure mem (dataPtr + 32) dataLen

/-- Complete conversion materializes exactly the rounded payload extent. -/
theorem bytesToLimbsMemory_size_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsize : mem.size = limbsPtr + 32)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size) :
    (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).size = limbsPtr + 32 + 32 * ((dataLen + 31) / 32) := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hqFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullSize : full.memory.size = limbsPtr + 32 + 32 * (dataLen / 32) := by
    exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
      rfl (by simpa [hsize]) (by simpa using hqFit) |>.trans (by simp)
  by_cases hrem : dataLen % 32 = 0
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 := by omega
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    simpa only [full, hceil] using hfullSize
  · have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
    have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
      partialWordWriteAddress_toNat hlen (by omega)
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
    unfold partialWordMemory
    apply toByteArray_write32_size_of_ge _ _ _ full.memory.size
      (limbsPtr + 32 + 32 * ((dataLen + 31) / 32)) rfl
    · rw [hwriteAddr, hfullSize]
    · rw [hwriteAddr, hfullSize, Nat.sub_self]
      exact lt_usize 0 (by norm_num)
    · omega

/-- Complete contiguous conversion preserves every older in-bounds word below the new payload. -/
theorem bytesToLimbsMemory_read_below_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen read : Nat)
    (hlen : dataLen ≤ 1024)
    (hsize : mem.size = limbsPtr + 32)
    (hread : read + 32 ≤ mem.size)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size) :
    (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).readWithPadding read 32 = mem.readWithPadding read 32 := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hqFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullSize : full.memory.size = limbsPtr + 32 + 32 * (dataLen / 32) := by
    exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
      rfl (by simpa [hsize]) (by simpa using hqFit) |>.trans (by simp)
  have hfullRead : full.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
    simpa only [full] using
      fullWordIterate_read_below_contiguous (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32)
        (fullWordInitialState mem aw) read rfl (by simpa [hsize]) hread
        (by simpa [hsize] using hread) (by simpa using hqFit)
  by_cases hrem : dataLen % 32 = 0
  · unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    exact hfullRead
  · have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
      partialWordWriteAddress_toNat hlen (by omega)
    have hpartialRead :
        (partialWordMemory full.memory full.activeWords (UInt256.ofNat dataPtr)
          (UInt256.ofNat dataLen) (UInt256.ofNat (dataLen % 32))
          (UInt256.ofNat limbsPtr)).readWithPadding read 32 =
        full.memory.readWithPadding read 32 := by
      unfold partialWordMemory
      exact toByteArray_write_read_below_of_gap _ _ _ _
        (by rw [hfullSize]; omega)
        (by rw [hwriteAddr, hsize] at *; omega)
        (by rw [hwriteAddr, hfullSize, Nat.sub_self]; exact lt_usize 0 (by norm_num))
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
    exact hpartialRead.trans hfullRead

/-- Complete contiguous conversion preserves an arbitrary older bounded padded slice. -/
theorem bytesToLimbsMemory_read_below_len_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen read len : Nat)
    (hdataLen : dataLen ≤ 1024)
    (hsize : mem.size = limbsPtr + 32)
    (hread : read + len ≤ mem.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size) :
    (bytesToLimbsMemory mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen).readWithPadding read len = mem.readWithPadding read len := by
  let full := bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
    (UInt256.ofNat limbsPtr) dataLen
  have hqFit : limbsPtr + 32 + 32 * (dataLen / 32) < UInt256.size := by
    have hle : dataLen / 32 ≤ (dataLen + 31) / 32 := Nat.div_le_div_right (by omega)
    omega
  have hfullSize : full.memory.size = limbsPtr + 32 + 32 * (dataLen / 32) := by
    exact fullWordIterate_memory_size_contiguous (UInt256.ofNat dataPtr)
      (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32) (fullWordInitialState mem aw)
      rfl (by simpa [hsize]) (by simpa using hqFit) |>.trans (by simp)
  have hfullRead : full.memory.readWithPadding read len = mem.readWithPadding read len := by
    simpa only [full] using
      fullWordIterate_read_below_len_contiguous (UInt256.ofNat dataPtr)
        (UInt256.ofNat dataLen) limbsPtr 0 (dataLen / 32)
        (fullWordInitialState mem aw) read len rfl (by simpa [hsize]) hread
        (by simpa [hsize] using hread) hpos hlen64 (by simpa using hqFit)
  by_cases hrem : dataLen % 32 = 0
  · unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    exact hfullRead
  · have hwriteAddr : (partialWordWriteAddress (UInt256.ofNat dataLen)
        (UInt256.ofNat limbsPtr)).toNat = limbsPtr + 32 + 32 * (dataLen / 32) :=
      partialWordWriteAddress_toNat hdataLen (by omega)
    have hpartialRead :
        (partialWordMemory full.memory full.activeWords (UInt256.ofNat dataPtr)
          (UInt256.ofNat dataLen) (UInt256.ofNat (dataLen % 32))
          (UInt256.ofNat limbsPtr)).readWithPadding read len =
        full.memory.readWithPadding read len := by
      unfold partialWordMemory
      exact toByteArray_write_read_below_len_padded_of_gap _ _ _ _ _
        (by rw [hwriteAddr, hsize] at *; omega) hpos hlen64
        (by rw [hwriteAddr, hfullSize, Nat.sub_self]; exact lt_usize 0 (by norm_num))
    unfold bytesToLimbsMemory bytesToLimbsSuffixMemory
    simp only [hrem, ↓reduceIte]
    rw [← show full = bytesToLimbsFullState mem aw (UInt256.ofNat dataPtr)
      (UInt256.ofNat limbsPtr) dataLen by rfl]
    exact hpartialRead.trans hfullRead

/-- Complete conversion also retains the allocator's active-word counter. -/
theorem bytesToLimbsActiveWords_eq_contiguous
    (mem : ByteArray) (aw : UInt256) (dataPtr limbsPtr dataLen : Nat)
    (hlen : dataLen ≤ 1024)
    (hsourceBefore : dataPtr + 32 + dataLen ≤ limbsPtr)
    (hactive : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) ≤ 32 * aw.toNat)
    (hfit : limbsPtr + 32 + 32 * ((dataLen + 31) / 32) < UInt256.size) :
    bytesToLimbsActiveWords mem aw (UInt256.ofNat dataPtr) (UInt256.ofNat limbsPtr)
      dataLen = aw := by
  apply bytesToLimbsActiveWords_eq
  · intro j hj
    dsimp only
    rw [fullWordIterate_index]
    simp only [fullWordInitialState, u256_zero_add]
    constructor
    · rw [fullWordReadAddress_toNat hlen (by
          have hm := Nat.mul_div_le dataLen 32
          omega) (by omega)]
      omega
    · rw [fullWordWriteAddress_toNat (by omega)]
      omega
  · intro hrem
    rw [partialWordReadAddress_toNat (by omega)]
    omega
  · intro hrem
    rw [partialWordWriteAddress_toNat hlen (by omega)]
    have hceil : (dataLen + 31) / 32 = dataLen / 32 + 1 := by omega
    omega

end Modexp.MultiLimbOddConversionSemantic
