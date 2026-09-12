import Benchmarks.Dss.Flapper.Bids
import Benchmarks.Dss.Flapper.File
import Benchmarks.Dss.Flapper.RuntimeBlocks_006
import Benchmarks.Dss.Flapper.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperTickIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperTickBaseSlot (idWord : UInt256) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 1) idWord

def flapperTickPackedSlot (idWord : UInt256) : UInt256 :=
  flapperTickBaseSlot idWord + UInt256.ofNat 2

def flapperTickPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperTickPackedSlot (flapperTickIdWord I))

def flapperTickTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperTickPackedWord σ I) flapperUint48Shift160)

def flapperTickEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperTickPackedWord σ I) flapperUint48Shift208)

def flapperTickTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Shift)

def flapperTickTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def flapperTickNowWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperTickTimestampWord I) flapperUint48Mask

def flapperTickNewEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask (flapperTickTimestampWord I + flapperTickTauWord σ I)

def flapperTickPackedEndWord (old newEnd : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))
    (UInt256.mul flapperUint48Shift208
      (UInt256.land newEnd flapperUint48Mask))

def flapperTickLocals (idWord : UInt256) : Store :=
  (∅ : Store).insert "id" (.int (Int.ofNat idWord.toNat))

def flapperTickLocalsEnd (idWord endWord : UInt256) : Store :=
  (flapperTickLocals idWord).insert "end_" (.int (Int.ofNat endWord.toNat))

def flapperTickPackedWordOfState (evm : EVM.State) (idWord : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (flapperTickPackedSlot idWord)

def flapperTickTicWordOfState (evm : EVM.State) (idWord : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.div (flapperTickPackedWordOfState evm idWord) flapperUint48Shift160)
    flapperUint48Mask

def flapperTickEndWordOfState (evm : EVM.State) (idWord : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.div (flapperTickPackedWordOfState evm idWord) flapperUint48Shift208)
    flapperUint48Mask

def flapperTickTauWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
      flapperUint48Shift)
    flapperUint48Mask

def flapperTickTimestampWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

def flapperTickNowWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land (flapperTickTimestampWordOfState evm) flapperUint48Mask

def flapperTickNewEndWordOfState (evm : EVM.State) : UInt256 :=
  UInt256.land
    (flapperTickTimestampWordOfState evm + flapperTickTauWordOfState evm)
    flapperUint48Mask

theorem flapperLow208Mask_mod_eq_land (w : UInt256) :
    w.toNat % 2 ^ 208 =
      (UInt256.land w (UInt256.ofNat (2 ^ 208 - 1))).toNat := by
  rw [uland_toNat]
  have hmask : (UInt256.ofNat (2 ^ 208 - 1)).toNat = 2 ^ 208 - 1 := by
    native_decide
  rw [hmask]
  exact (nat_land_mask_eq_mod w.toNat 208).symm

theorem flapperUint48Mask_clean_word (w : UInt256) :
    UInt256.land (UInt256.land w flapperUint48Mask) flapperUint48Mask =
      UInt256.land w flapperUint48Mask :=
  flapperUint48Mask_clean_right_file w

theorem flapperUint48Low_add_mod
    (a b : UInt256) (hb : b.toNat < 2 ^ 48) :
    (((UInt256.land a flapperUint48Mask).toNat + b.toNat) % 2 ^ 48) =
      (UInt256.land (a + b) flapperUint48Mask).toNat := by
  calc
    ((UInt256.land a flapperUint48Mask).toNat + b.toNat) % 2 ^ 48 =
        (a.toNat % 2 ^ 48 + b.toNat % 2 ^ 48) % 2 ^ 48 := by
      rw [flapperUint48Mask_mod_eq_land a, Nat.mod_eq_of_lt hb]
    _ = (a.toNat + b.toNat) % 2 ^ 48 := by
      have hmodA :
          a.toNat % 2 ^ 48 % 2 ^ 48 = a.toNat % 2 ^ 48 := by
        exact Nat.mod_eq_of_lt
          (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48))
      have hmodB :
          b.toNat % 2 ^ 48 % 2 ^ 48 = b.toNat % 2 ^ 48 := by
        exact Nat.mod_eq_of_lt
          (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 48))
      simpa [hmodA, hmodB] using
        (Nat.add_mod a.toNat b.toNat (2 ^ 48)).symm
    _ = ((a.toNat + b.toNat) % UInt256.size) % 2 ^ 48 := by
      rw [Nat.mod_mod_of_dvd]
      exact ⟨2 ^ 208, by norm_num [UInt256.size, Nat.pow_add]⟩
    _ = (a + b).toNat % 2 ^ 48 := by
      rw [uadd_toNat]
    _ = (UInt256.land (a + b) flapperUint48Mask).toNat := by
      rw [flapperUint48Mask_mod_eq_land]

theorem flapperStorageLocStore_uint48_offset26 (evm : EVM.State)
    (slot val : UInt256) :
    storageLocStore evm (uint48Loc slot ⟨26, by decide⟩ (by decide))
        (.int (Int.ofNat (UInt256.land val flapperUint48Mask).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))
          (UInt256.mul flapperUint48Shift208
            (UInt256.land val flapperUint48Mask)))) := by
  unfold storageLocStore storageLocWriteWord uint48Loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let low := UInt256.land val flapperUint48Mask
  have htakeOldLen :
      ((EVM.Word.toBytesLEWithSizeProof old).1.take 26).length = 26 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof old).2]
    norm_num
  have htakeLowLen :
      ((EVM.Word.toBytesLEWithSizeProof low).1.take 6).length = 6 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof low).2]
    norm_num
  have hlowLt : low.toNat < 2 ^ 48 := by
    simpa [low] using flapperUint48Word_lt val
  have hlowClean : UInt256.land low flapperUint48Mask = low := by
    simpa [low] using flapperUint48Mask_clean_word val
  have hmulLt : low.toNat * 2 ^ 208 < UInt256.size := by
    calc
      low.toNat * 2 ^ 208 < 2 ^ 48 * 2 ^ 208 :=
        Nat.mul_lt_mul_of_pos_right hlowLt (by norm_num)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
      _ = UInt256.size := by rfl
  have hmulLt' : 2 ^ 208 * low.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hmulLt
  have hsumLt : old.toNat % 2 ^ 208 + low.toNat * 2 ^ 208 < UInt256.size := by
    have holdLowLe : old.toNat % 2 ^ 208 ≤ 2 ^ 208 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 208))
    have hlowLe : low.toNat ≤ 2 ^ 48 - 1 := Nat.le_pred_of_lt hlowLt
    have hlowTerm : low.toNat * 2 ^ 208 ≤ (2 ^ 48 - 1) * 2 ^ 208 :=
      Nat.mul_le_mul_right _ hlowLe
    have hmax : (2 ^ 208 - 1) + (2 ^ 48 - 1) * 2 ^ 208 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have holdLowLt : old.toNat % 2 ^ 208 < 2 ^ 208 :=
    Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 208)
  congr 2
  apply u256_inj
  change fromBytes'
      (List.take 26 (EVM.Word.toBytesLEWithSizeProof old).1 ++
        List.take 6 (EVM.Word.toBytesLEWithSizeProof low).1 ++
        List.drop 32 (EVM.Word.toBytesLEWithSizeProof old).1) =
      (UInt256.lor
        (UInt256.land old (UInt256.sub flapperUint48Shift208 (UInt256.ofNat 1)))
        (UInt256.mul flapperUint48Shift208 low)).toNat
  rw [fromBytes'_append, fromBytes'_append,
    fromBytes'_take_wordLE_land_mask old 26 (by decide),
    fromBytes'_take_wordLE_land_mask low 6 (by decide),
    fromBytes'_drop_wordLE, List.length_append, htakeOldLen, htakeLowLen]
  rw [show 2 ^ (8 * 26) = 2 ^ 208 by norm_num]
  rw [show 2 ^ (8 * (26 + 6)) = 2 ^ 256 by norm_num]
  rw [show 256 ^ 32 = 2 ^ 256 by norm_num]
  have hdivOld : UInt256.toNat old / 2 ^ 256 = 0 := by
    exact Nat.div_eq_of_lt old.val.isLt
  rw [hdivOld]
  rw [Nat.mul_zero, Nat.add_zero]
  rw [show UInt256.ofNat (2 ^ (8 * 6) - 1) = flapperUint48Mask by native_decide]
  rw [hlowClean]
  rw [show flapperUint48Shift208 = UInt256.ofNat (2 ^ 208) by decide]
  rw [show UInt256.sub (UInt256.ofNat (2 ^ 208)) (UInt256.ofNat 1) =
      UInt256.ofNat (2 ^ 208 - 1) by native_decide]
  rw [u256_lor_toNat, u256_mul_toNat]
  rw [show (UInt256.ofNat (2 ^ 208)).toNat = 2 ^ 208 by native_decide]
  rw [Nat.mod_eq_of_lt hmulLt']
  rw [← flapperLow208Mask_mod_eq_land old]
  rw [Nat.mul_comm (2 ^ 208) low.toNat]
  rw [nat_lor_shift_add (old.toNat % 2 ^ 208) low.toNat 208 holdLowLt]
  rw [Nat.mod_eq_of_lt hsumLt]

theorem flapperTickMappingHashSlot (idWord : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0
          (idWord.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
      flapperTickBaseSlot idWord := by
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem idWord (UInt256.ofNat 1) mem) =
      flapperTickBaseSlot idWord
  unfold keccakWord flapperTickBaseSlot solcMappingSlot
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 64).toNat = 64 by decide,
    twoWordHashMem_read0_64_any]
  exact mappingSlot_single idWord (UInt256.ofNat 1)

theorem flapperX_tick_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4586⟩
      [flapperTickIdWord I, UInt256.ofNat 360, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd855⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 32)
      (by simpa using hsz36) hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd877 := flapperRuntimeBlocks.flapperRuntime_block_855_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond (by jump_dest) rd855
  have rd4586 := flapperRuntimeBlocks.flapperRuntime_block_877
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd877
  exact ⟨_, _, by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_877_stack,
      flapperTickIdWord, calldataWord,
      show (UInt256.ofNat 4).toNat = 4 by decide] using rd4586⟩

theorem flapperX_tick_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd855⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 1 := by
    apply ult_one
    rw [usub_ofNat_word_toNat
      (c := UInt256.ofNat 4)
      (by change 4 ≤ I.calldata.size; omega) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd873 := flapperRuntimeBlocks.flapperRuntime_block_855_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd855
  exact flapperRuntimeBlocks.flapperRuntime_block_873
    (R := flapperRuntimeBlocks.flapperRuntime_block_855_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_855_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd873

theorem flapperX_tick_end_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hend : ¬ (flapperTickEndWord σ I).toNat < (flapperTickTimestampWord I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4586⟩ := flapperX_tick_decode_ok
    (g := g) hsize hsz36 hreach
  have hhash :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I) solcFreePtrMem
  have hlt :
      UInt256.lt (flapperTickEndWord σ I) (flapperTickTimestampWord I) =
        UInt256.ofNat 0 := by
    exact ult_zero (by omega)
  have hcond :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) = UInt256.ofNat 0 := by
    rw [hhash, u256_add_comm]
    simpa [flapperTickEndWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperTickTimestampWord, flapperUint48Mask, flapperUint48Shift208] using hlt
  obtain ⟨_, _, rd4627⟩ := flapperRuntimeBlocks.flapperRuntime_block_4586_fallthrough
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd4586
  exact flapperRuntimeBlocks.flapperRuntime_block_4627
    (R := [flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd4627

theorem flapperX_tick_tic_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hend : (flapperTickEndWord σ I).toNat < (flapperTickTimestampWord I).toNat)
    (htic : flapperTickTicWord σ I ≠ UInt256.ofNat 0)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4586⟩ := flapperX_tick_decode_ok
    (g := g) hsize hsz36 hreach
  have hhash0 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I) solcFreePtrMem
  have hlt :
      UInt256.lt (flapperTickEndWord σ I) (flapperTickTimestampWord I) =
        UInt256.ofNat 1 := by
    exact ult_one hend
  have hcondEnd :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    rw [hhash0, u256_add_comm]
    simpa [flapperTickEndWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperTickTimestampWord, flapperUint48Mask, flapperUint48Shift208] using
      (by rw [hlt]; decide : UInt256.lt (flapperTickEndWord σ I)
        (flapperTickTimestampWord I) ≠ UInt256.ofNat 0)
  obtain ⟨_, _, rd4694⟩ := flapperRuntimeBlocks.flapperRuntime_block_4586_taken
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondEnd (by jump_dest) rd4586
  have hhash1 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I)
      (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
        (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
  have hcondTic :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0
                        (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                          (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) =
        UInt256.ofNat 0 := by
    rw [hhash1, u256_add_comm]
    simpa [flapperTickTicWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperUint48Mask, flapperUint48Shift160] using
      isZero_eq_zero_of_ne htic
  obtain ⟨_, _, rd4733⟩ := flapperRuntimeBlocks.flapperRuntime_block_4694_fallthrough
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTic rd4694
  exact flapperRuntimeBlocks.flapperRuntime_block_4733
    (R := [flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd4733

theorem flapperX_tick_overflow_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hend : (flapperTickEndWord σ I).toNat < (flapperTickTimestampWord I).toNat)
    (htic : flapperTickTicWord σ I = UInt256.ofNat 0)
    (hwrap : (flapperTickNewEndWord σ I).toNat < (flapperTickNowWord I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4586⟩ := flapperX_tick_decode_ok
    (g := g) hsize hsz36 hreach
  have hhash0 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I) solcFreePtrMem
  have hlt :
      UInt256.lt (flapperTickEndWord σ I) (flapperTickTimestampWord I) =
        UInt256.ofNat 1 := by
    exact ult_one hend
  have hcondEnd :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    rw [hhash0, u256_add_comm]
    simpa [flapperTickEndWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperTickTimestampWord, flapperUint48Mask, flapperUint48Shift208] using
      (by rw [hlt]; decide : UInt256.lt (flapperTickEndWord σ I)
        (flapperTickTimestampWord I) ≠ UInt256.ofNat 0)
  obtain ⟨_, _, rd4694⟩ := flapperRuntimeBlocks.flapperRuntime_block_4586_taken
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondEnd (by jump_dest) rd4586
  have hhash1 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I)
      (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
        (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
  have hcondTic :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0
                        (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                          (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) ≠
        UInt256.ofNat 0 := by
    have hz : UInt256.isZero (flapperTickTicWord σ I) ≠ UInt256.ofNat 0 := by
      rw [htic]
      decide
    rw [hhash1, u256_add_comm]
    simpa [flapperTickTicWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperUint48Mask, flapperUint48Shift160] using hz
  obtain ⟨_, _, rd4809⟩ := flapperRuntimeBlocks.flapperRuntime_block_4694_taken
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTic (by jump_dest) rd4694
  obtain ⟨_, _, rd4936⟩ := flapperRuntimeBlocks.flapperRuntime_block_4809
    (R := [flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4809
  have hltWrap :
      UInt256.lt (flapperTickNewEndWord σ I) (flapperTickNowWord I) =
        UInt256.ofNat 1 := by
    exact ult_one hwrap
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              ((UInt256.ofNat I.header.timestamp) +
                (UInt256.land (UInt256.ofNat 281474976710655)
                  (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5))
                    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))))
              (UInt256.ofNat 281474976710655))
            (UInt256.land (UInt256.ofNat I.header.timestamp)
              (UInt256.ofNat 281474976710655))) = UInt256.ofNat 0 := by
    rw [show UInt256.land
          ((UInt256.ofNat I.header.timestamp) +
            (UInt256.land (UInt256.ofNat 281474976710655)
              (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5))
                (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))))
          (UInt256.ofNat 281474976710655) =
        flapperTickNewEndWord σ I by
      simp [flapperTickNewEndWord, flapperTickTimestampWord, flapperTickTauWord,
        flapperUint48Mask, flapperUint48Shift, u256_land_comm]]
    simpa [flapperTickNowWord, flapperTickTimestampWord, flapperUint48Mask] using
      (by rw [hltWrap]; decide :
        UInt256.isZero
          (UInt256.lt (flapperTickNewEndWord σ I) (flapperTickNowWord I)) =
            UInt256.ofNat 0)
  have rd4959 := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough
    (x0 := flapperTickTauWord σ I) (x1 := flapperTickTimestampWord I)
    (R := [UInt256.ofNat 4838, flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa [flapperTickTauWord, flapperTickTimestampWord, flapperUint48Mask,
      flapperUint48Shift] using hcondWrap)
    rd4936
  exact flapperRuntimeBlocks.flapperRuntime_block_4959
    (R := flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack
      (x0 := flapperTickTauWord σ I) (x1 := flapperTickTimestampWord I)
      (R := [UInt256.ofNat 4838, flapperTickIdWord I, UInt256.ofNat 360, sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_4936_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd4959

theorem flapperX_tick_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hend : (flapperTickEndWord σ I).toNat < (flapperTickTimestampWord I).toNat)
    (htic : flapperTickTicWord σ I = UInt256.ofNat 0)
    (hwrap : ¬ (flapperTickNewEndWord σ I).toNat < (flapperTickNowWord I).toNat)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (flapperTickPackedSlot (flapperTickIdWord I))
        (flapperTickPackedEndWord (flapperTickPackedWord σ I)
          (flapperTickNewEndWord σ I)))
      ByteArray.empty := by
  obtain ⟨_, _, rd4586⟩ := flapperX_tick_decode_ok
    (g := g) hsize hsz36 hreach
  have hhash0 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I) solcFreePtrMem
  have hlt :
      UInt256.lt (flapperTickEndWord σ I) (flapperTickTimestampWord I) =
        UInt256.ofNat 1 := by
    exact ult_one hend
  have hcondEnd :
      UInt256.lt
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0 solcFreePtrMem
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))))
          (UInt256.ofNat I.header.timestamp) ≠ UInt256.ofNat 0 := by
    rw [hhash0, u256_add_comm]
    simpa [flapperTickEndWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperTickTimestampWord, flapperUint48Mask, flapperUint48Shift208] using
      (by rw [hlt]; decide : UInt256.lt (flapperTickEndWord σ I)
        (flapperTickTimestampWord I) ≠ UInt256.ofNat 0)
  obtain ⟨_, _, rd4694⟩ := flapperRuntimeBlocks.flapperRuntime_block_4586_taken
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondEnd (by jump_dest) rd4586
  have hhash1 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I)
      (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
        (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
  have hcondTic :
      UInt256.isZero
          (UInt256.land (UInt256.ofNat 281474976710655)
            (UInt256.div
              (storageRead I.codeOwner σ
                ((UInt256.ofNat 2) +
                  (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 1).toByteArray.write 0
                      ((flapperTickIdWord I).toByteArray.write 0
                        (flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                          (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32))))
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) ≠
        UInt256.ofNat 0 := by
    have hz : UInt256.isZero (flapperTickTicWord σ I) ≠ UInt256.ofNat 0 := by
      rw [htic]
      decide
    rw [hhash1, u256_add_comm]
    simpa [flapperTickTicWord, flapperTickPackedWord, flapperTickPackedSlot,
      flapperUint48Mask, flapperUint48Shift160] using hz
  obtain ⟨_, _, rd4809⟩ := flapperRuntimeBlocks.flapperRuntime_block_4694_taken
    (x0 := flapperTickIdWord I) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondTic (by jump_dest) rd4694
  obtain ⟨_, _, rd4936⟩ := flapperRuntimeBlocks.flapperRuntime_block_4809
    (R := [flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4809
  have hltWrap :
      UInt256.lt (flapperTickNewEndWord σ I) (flapperTickNowWord I) =
        UInt256.ofNat 0 := by
    exact ult_zero (by omega)
  have hcondWrap :
      UInt256.isZero
          (UInt256.lt
            (UInt256.land
              ((UInt256.ofNat I.header.timestamp) +
                (UInt256.land (UInt256.ofNat 281474976710655)
                  (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5))
                    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))))
              (UInt256.ofNat 281474976710655))
            (UInt256.land (UInt256.ofNat I.header.timestamp)
              (UInt256.ofNat 281474976710655))) ≠ UInt256.ofNat 0 := by
    rw [show UInt256.land
          ((UInt256.ofNat I.header.timestamp) +
            (UInt256.land (UInt256.ofNat 281474976710655)
              (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5))
                (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))))
          (UInt256.ofNat 281474976710655) =
        flapperTickNewEndWord σ I by
      simp [flapperTickNewEndWord, flapperTickTimestampWord, flapperTickTauWord,
        flapperUint48Mask, flapperUint48Shift, u256_land_comm]]
    simpa [flapperTickNowWord, flapperTickTimestampWord, flapperUint48Mask] using
      (by rw [hltWrap]; decide :
        UInt256.isZero
          (UInt256.lt (flapperTickNewEndWord σ I) (flapperTickNowWord I)) ≠
            UInt256.ofNat 0)
  have rd4930 := flapperRuntimeBlocks.flapperRuntime_block_4936_taken
    (x0 := flapperTickTauWord σ I) (x1 := flapperTickTimestampWord I)
    (R := [UInt256.ofNat 4838, flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa [flapperTickTauWord, flapperTickTimestampWord, flapperUint48Mask,
      flapperUint48Shift] using hcondWrap)
    (by jump_dest) rd4936
  have rd4838 := flapperRuntimeBlocks.flapperRuntime_block_4930
    (x0 := flapperTickTimestampWord I + flapperTickTauWord σ I)
    (x1 := flapperTickTauWord σ I) (x2 := flapperTickTimestampWord I)
    (x3 := UInt256.ofNat 4838)
    (R := [flapperTickIdWord I, UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4930
  have hhash2 :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 1).toByteArray.write 0
            ((flapperTickIdWord I).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_4694_taken_memory
                (mem := flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
                  (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
                (x0 := flapperTickIdWord I))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperTickBaseSlot (flapperTickIdWord I) :=
    flapperTickMappingHashSlot (flapperTickIdWord I)
      (flapperRuntimeBlocks.flapperRuntime_block_4694_taken_memory
        (mem := flapperRuntimeBlocks.flapperRuntime_block_4586_taken_memory
          (mem := solcFreePtrMem) (x0 := flapperTickIdWord I))
        (x0 := flapperTickIdWord I))
  have hnewClean :
      UInt256.land (flapperTickNewEndWord σ I) flapperUint48Mask =
        flapperTickNewEndWord σ I := by
    rw [flapperTickNewEndWord]
    rw [u256_land_comm flapperUint48Mask
      (flapperTickTimestampWord I + flapperTickTauWord σ I)]
    exact flapperUint48Mask_clean_right_file
      (flapperTickTimestampWord I + flapperTickTauWord σ I)
  obtain ⟨_, _, rd360raw⟩ := flapperRuntimeBlocks.flapperRuntime_block_4838
    (x0 := flapperTickTimestampWord I + flapperTickTauWord σ I)
    (x1 := flapperTickIdWord I) (x2 := UInt256.ofNat 360)
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm (by jump_dest) rd4838
  have hret := flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel])
    (by simp only [List.length_singleton]; omega)
    rd360raw
  have hnewActual :
      UInt256.land flapperUint48Mask
          (flapperTickTauWord σ I + flapperTickTimestampWord I) =
        flapperTickNewEndWord σ I := by
    rw [u256_add_comm (flapperTickTauWord σ I) (flapperTickTimestampWord I)]
    simp [flapperTickNewEndWord]
  simpa [flapperRuntimeBlocks.flapperRuntime_block_4838_stack,
    flapperTickPackedSlot, flapperTickPackedWord, flapperTickPackedEndWord,
    flapperUint48Shift208, hhash2, hnewActual, hnewClean, u256_add_comm] using hret

theorem flapperDispatch_tick {cd : ByteArray}
    (hsel : ((⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some tickTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
      tendTransition])
    (post := [ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
    · rw [flapperFileSelectorBytes, hcd]; decide
    · rw [flapperFillSelectorBytes, hcd]; decide
    · rw [flapperGemSelectorBytes, hcd]; decide
    · rw [flapperKickSelectorBytes, hcd]; decide
    · rw [flapperKicksSelectorBytes, hcd]; decide
    · rw [flapperLidSelectorBytes, hcd]; decide
    · rw [flapperLiveSelectorBytes, hcd]; decide
    · rw [flapperRelySelectorBytes, hcd]; decide
    · rw [flapperTauSelectorBytes, hcd]; decide
    · rw [flapperTendSelectorBytes, hcd]; decide
  · rw [flapperTickSelectorBytes]
    exact hsel

theorem flapperDecode_tick_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata =
      some (flapperTickLocals (flapperTickIdWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata =
    some (flapperTickLocals (flapperTickIdWord I))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      flapperTickIdWord I := by
    simpa [flapperTickIdWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["id"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (start := 0) htake4]
  change decodeCalldata.insertValues ["id"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)]
      ∅ =
    some (flapperTickLocals (flapperTickIdWord I))
  rw [hword4]
  simp [decodeCalldata.insertValues, flapperTickLocals]

theorem flapperDecode_tick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["id"] [abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["id"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short
    (mode := DecodeMode.legacySolc05) (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperTickEnd_eval (evm : EVM.State) (idWord : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (flapperTickEndWordOfState evm idWord).toNat)) := by
  let locals := flapperTickLocals idWord
  let erEnd : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "end"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTickLocals]
  have herEnd :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "end") = .ok erEnd := by
    simp [locals, erEnd, flapperTickLocals, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, bidsF, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have htyEnd : storageTypeAt? contract.storage erEnd =
      some (.elem (.int uint48Int)) := by
    simp [erEnd, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocEnd : config.storage.layout erEnd =
      fun _ => some (uint48Loc (flapperTickPackedSlot idWord)
        ⟨26, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erEnd,
      bidsBase, mapSlot, solcMappingSlot, flapperTickPackedSlot, flapperTickBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)
    rfl
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herEnd)
    (hty := htyEnd) (hloc := hlocEnd), flapperStorageLocLoad_uint48_offset26]
  simp [locals, flapperTickEndWordOfState, flapperTickPackedWordOfState,
    flapperTickPackedSlot]

theorem flapperTickTic_eval (evm : EVM.State) (idWord : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (flapperTickTicWordOfState evm idWord).toNat)) := by
  let locals := flapperTickLocals idWord
  let erTic : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "tic"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTickLocals]
  have herTic :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "id") "tic") = .ok erTic := by
    simp [locals, erTic, flapperTickLocals, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, bidsF, evalExpr?, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have htyTic : storageTypeAt? contract.storage erTic =
      some (.elem (.int uint48Int)) := by
    simp [erTic, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocTic : config.storage.layout erTic =
      fun _ => some (uint48Loc (flapperTickPackedSlot idWord)
        ⟨20, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTic,
      bidsBase, mapSlot, solcMappingSlot, flapperTickPackedSlot, flapperTickBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide)
    rfl
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herTic)
    (hty := htyTic) (hloc := hlocTic), flapperStorageLocLoad_uint48_offset20]
  simp [locals, flapperTickTicWordOfState, flapperTickPackedWordOfState,
    flapperTickPackedSlot]

theorem flapperTickTau_eval (evm : EVM.State) (idWord : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.storage tauRef) =
      .ok (.int (Int.ofNat (flapperTickTauWordOfState evm).toNat)) := by
  let locals := flapperTickLocals idWord
  let erTau : EvaledStorageRef := { base := "tau", steps := [] }
  have hbase : locals.get? "tau" = none := by
    simp [locals, flapperTickLocals]
  have herTau : evalStorageRef config { contract := contract, locals := locals } evm
      tauRef = .ok erTau := by
    simp [locals, erTau, evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind,
      pure, bind]
  have htyTau : storageTypeAt? contract.storage erTau =
      some (.elem (.int uint48Int)) := by
    simp [erTau, contract, storageDecls, storageTypeAt?, uint48St]
  have hlocTau : config.storage.layout erTau =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTau]
  rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herTau)
    (hty := htyTau) (hloc := hlocTau), flapperStorageLocLoad_uint48_offset6]
  simp [locals, flapperTickTauWordOfState, show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide]

theorem flapperTickNow48_eval (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (flapperTickNowWordOfState evm).toNat)) := by
  have hmod :
      (Int.ofNat (flapperTickTimestampWordOfState evm).toNat) % uint48Modulus =
        Int.ofNat (flapperTickNowWordOfState evm).toNat := by
    rw [uint48Modulus]
    change (Int.ofNat (flapperTickTimestampWordOfState evm).toNat) %
        (Int.ofNat ((2 : Nat) ^ 48)) =
      Int.ofNat (flapperTickNowWordOfState evm).toNat
    calc
      (Int.ofNat (flapperTickTimestampWordOfState evm).toNat) %
          (Int.ofNat ((2 : Nat) ^ 48)) =
        Int.ofNat ((flapperTickTimestampWordOfState evm).toNat % (2 : Nat) ^ 48) := by
          exact (Int.natCast_emod (flapperTickTimestampWordOfState evm).toNat
            ((2 : Nat) ^ 48)).symm
      _ = Int.ofNat (flapperTickNowWordOfState evm).toNat := by
        exact congrArg Int.ofNat
          (flapperUint48Mask_mod_eq_land (flapperTickTimestampWordOfState evm))
  have hnonzero : uint48Modulus ≠ 0 := by
    norm_num [uint48Modulus]
  simp only [now48, wrap48, evalExpr?, envValue, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  change (if uint48Modulus = 0 then EvalResult.revert
    else EvalResult.ok
      (Value.int (Int.ofNat (flapperTickTimestampWordOfState evm).toNat % uint48Modulus))) =
    EvalResult.ok (Value.int (Int.ofNat (flapperTickNowWordOfState evm).toNat))
  rw [if_neg hnonzero, hmod]

theorem flapperTickNewEnd_eval (evm : EVM.State) (idWord : UInt256) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (wrap48 (.binary .add now48 (.storage tauRef))) =
      .ok (.int (Int.ofNat (flapperTickNewEndWordOfState evm).toNat)) := by
  let nowWord := flapperTickNowWordOfState evm
  let tauWord := flapperTickTauWordOfState evm
  have htauLt : tauWord.toNat < 2 ^ 48 := by
    simpa [tauWord, flapperTickTauWordOfState] using
      flapperUint48Word_lt
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
          flapperUint48Shift)
  have hmod :
      (Int.ofNat nowWord.toNat + Int.ofNat tauWord.toNat) % uint48Modulus =
        Int.ofNat (flapperTickNewEndWordOfState evm).toNat := by
    rw [uint48Modulus]
    change (Int.ofNat (nowWord.toNat + tauWord.toNat)) %
        (Int.ofNat ((2 : Nat) ^ 48)) =
      Int.ofNat (flapperTickNewEndWordOfState evm).toNat
    calc
      (Int.ofNat (nowWord.toNat + tauWord.toNat)) %
          (Int.ofNat ((2 : Nat) ^ 48)) =
        Int.ofNat ((nowWord.toNat + tauWord.toNat) % (2 : Nat) ^ 48) := by
          exact (Int.natCast_emod (nowWord.toNat + tauWord.toNat)
            ((2 : Nat) ^ 48)).symm
      _ = Int.ofNat (flapperTickNewEndWordOfState evm).toNat := by
        exact congrArg Int.ofNat
          (by
            simpa [nowWord, tauWord, flapperTickNowWordOfState,
              flapperTickNewEndWordOfState] using
              flapperUint48Low_add_mod
                (flapperTickTimestampWordOfState evm)
                (flapperTickTauWordOfState evm) htauLt)
  have hnonzero : uint48Modulus ≠ 0 := by
    norm_num [uint48Modulus]
  simp only [wrap48, evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [flapperTickNow48_eval evm (flapperTickLocals idWord)]
  have hTauEval := flapperTickTau_eval evm idWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTauEval
  rw [hTauEval]
  change (if uint48Modulus = 0 then EvalResult.revert
    else EvalResult.ok (Value.int
      ((Int.ofNat nowWord.toNat + Int.ofNat tauWord.toNat) % uint48Modulus))) =
    EvalResult.ok (Value.int (Int.ofNat (flapperTickNewEndWordOfState evm).toNat))
  rw [if_neg hnonzero, hmod]

theorem flapperTickIntZeroBeq_true (w : UInt256) (h : w = UInt256.ofNat 0) :
    ((Value.int (Int.ofNat w.toNat)) == Value.int 0) = true := by
  subst w
  decide

theorem flapperTickIntZeroBeq_false (w : UInt256) (h : w ≠ UInt256.ofNat 0) :
    ((Value.int (Int.ofNat w.toNat)) == Value.int 0) = false := by
  cases hbeq : ((Value.int (Int.ofNat w.toNat)) == Value.int 0)
  · rfl
  · exact False.elim <| h <| by
      have hval := beq_iff_eq.mp hbeq
      injection hval with hint
      apply u256_inj
      simpa using hint

theorem flapperTickEndGuard_eval_true (evm : EVM.State) (idWord : UInt256)
    (hend :
      (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool true) := by
  have hEndEval := flapperTickEnd_eval evm idWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      (flapperTickEndWordOfState evm idWord).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperTickTimestampWordOfState] using hend
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperTickEndGuard_eval_false (evm : EVM.State) (idWord : UInt256)
    (hend :
      ¬ (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
      .ok (.bool false) := by
  have hEndEval := flapperTickEnd_eval evm idWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndEval
  have hprop :
      ¬ (flapperTickEndWordOfState evm idWord).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
    simpa [flapperTickTimestampWordOfState] using hend
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndEval]
  simp [envValue, hprop]

theorem flapperTickTicGuard_eval_true (evm : EVM.State) (idWord : UInt256)
    (htic : flapperTickTicWordOfState evm idWord = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool true) := by
  have hTicEval := flapperTickTic_eval evm idWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_true (flapperTickTicWordOfState evm idWord) htic]

theorem flapperTickTicGuard_eval_false (evm : EVM.State) (idWord : UInt256)
    (htic : flapperTickTicWordOfState evm idWord ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := flapperTickLocals idWord } evm
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
      .ok (.bool false) := by
  have hTicEval := flapperTickTic_eval evm idWord
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hTicEval
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hTicEval]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [flapperTickIntZeroBeq_false (flapperTickTicWordOfState evm idWord) htic]

theorem flapperTickEndLocal_eval (evm : EVM.State) (idWord endWord : UInt256) :
    evalExpr? config
        { contract := contract, locals := flapperTickLocalsEnd idWord endWord } evm
        (.var "end_") =
      .ok (.int (Int.ofNat endWord.toNat)) := by
  unfold evalExpr?
  change EvalResult.ofOption EvalError.unboundVariable
      ((flapperTickLocalsEnd idWord endWord).get? "end_") =
    .ok (.int (Int.ofNat endWord.toNat))
  rw [flapperTickLocalsEnd]
  rw [store_get_self]
  rfl

theorem flapperTickCheckedGuard_eval_true (evm : EVM.State) (idWord : UInt256)
    (hwrap :
      ¬ (flapperTickNewEndWordOfState evm).toNat <
        (flapperTickNowWordOfState evm).toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperTickLocalsEnd idWord (flapperTickNewEndWordOfState evm) } evm
        (.binary .ge (.var "end_") now48) =
      .ok (.bool true) := by
  have hEndLocal := flapperTickEndLocal_eval evm idWord (flapperTickNewEndWordOfState evm)
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndLocal
  have hNowEval := flapperTickNow48_eval evm
    (flapperTickLocalsEnd idWord (flapperTickNewEndWordOfState evm))
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndLocal, hNowEval]
  have hgeNat :
      (flapperTickNowWordOfState evm).toNat ≤
        (flapperTickNewEndWordOfState evm).toNat := by
    omega
  simpa [hgeNat]

theorem flapperTickCheckedGuard_eval_false (evm : EVM.State) (idWord : UInt256)
    (hwrap :
      (flapperTickNewEndWordOfState evm).toNat <
        (flapperTickNowWordOfState evm).toNat) :
    evalExpr? config
        { contract := contract,
          locals := flapperTickLocalsEnd idWord (flapperTickNewEndWordOfState evm) } evm
        (.binary .ge (.var "end_") now48) =
      .ok (.bool false) := by
  have hEndLocal := flapperTickEndLocal_eval evm idWord (flapperTickNewEndWordOfState evm)
  simp only [evalExpr?, EvalResult.bind, bind, pure] at hEndLocal
  have hNowEval := flapperTickNow48_eval evm
    (flapperTickLocalsEnd idWord (flapperTickNewEndWordOfState evm))
  simp only [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hEndLocal, hNowEval]
  have hnotNat :
      ¬ (flapperTickNowWordOfState evm).toNat ≤
        (flapperTickNewEndWordOfState evm).toNat := by
    omega
  simpa [hnotNat]

theorem flapperTickAssignEnd (evm : EVM.State) (idWord endWord : UInt256)
    (hclean : UInt256.land endWord flapperUint48Mask = endWord) :
    assignStorageRef? config
      { contract := contract, locals := flapperTickLocalsEnd idWord endWord } evm
      .storage (bidsF (.var "id") "end") (.int (Int.ofNat endWord.toNat)) =
      .ok ({ contract := contract, locals := flapperTickLocalsEnd idWord endWord },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (flapperTickPackedSlot idWord)
          (flapperTickPackedEndWord (flapperTickPackedWordOfState evm idWord) endWord)) := by
  let locals := flapperTickLocalsEnd idWord endWord
  let solm : Frame := { contract := contract, locals := locals }
  let erEnd : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "end"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals, flapperTickLocalsEnd, flapperTickLocals]
  have hgetId : locals.get? "id" = some (.int (Int.ofNat idWord.toNat)) := by
    change (flapperTickLocalsEnd idWord endWord).get? "id" =
      some (.int (Int.ofNat idWord.toNat))
    rw [flapperTickLocalsEnd]
    rw [store_get_ne (flapperTickLocals idWord) (k := "end_") (a := "id")
      (.int (Int.ofNat endWord.toNat)) (by decide)]
    exact store_get_self (∅ : Store) "id" (.int (Int.ofNat idWord.toNat))
  have hgetIdElem : locals["id"]? = some (.int (Int.ofNat idWord.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetId
  have herEnd : evalStorageRef config solm evm
      (bidsF (.var "id") "end") = .ok erEnd := by
    simp [solm, erEnd, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure,
      bind, hgetIdElem]
  have htyEnd : storageTypeAt? contract.storage erEnd =
      some (.elem (.int uint48Int)) := by
    simp [erEnd, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocEnd : config.storage.layout erEnd =
      fun _ => some (uint48Loc (flapperTickPackedSlot idWord)
        ⟨26, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erEnd,
      bidsBase, mapSlot, solcMappingSlot, flapperTickPackedSlot, flapperTickBaseSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)
    rfl
  have hstore :
      storageLocStore evm
          (uint48Loc (flapperTickPackedSlot idWord) ⟨26, by decide⟩ (by decide))
          (.int (Int.ofNat endWord.toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTickPackedSlot idWord)
          (flapperTickPackedEndWord (flapperTickPackedWordOfState evm idWord)
            endWord)) := by
    simpa [flapperTickPackedEndWord, flapperTickPackedWordOfState, hclean] using
      flapperStorageLocStore_uint48_offset26 evm (flapperTickPackedSlot idWord) endWord
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
      (hbase := hbase) (her := herEnd) (hty := htyEnd) (hloc := hlocEnd)
      (hstore := hstore)

theorem flapperTickBodyRevertsEnd (evm : EVM.State) (idWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hend :
      ¬ (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat) :
    ExecTransitionBody config contract evm (flapperTickLocals idWord)
      tickTransition.body .reverted := by
  let locals := flapperTickLocals idWord
  let solm : Frame := { contract := contract, locals := locals }
  have hguardEnd :
      evalExpr? config solm evm
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
    simpa [solm, locals] using
      flapperTickEndGuard_eval_false evm idWord hend
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tickTransition, nonpayable, checkedAdd48Into, solm, locals] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consRevert (ExecStmt.requireFalse hguardEnd)

theorem flapperTickBodyRevertsTic (evm : EVM.State) (idWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hend :
      (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat)
    (htic : flapperTickTicWordOfState evm idWord ≠ UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperTickLocals idWord)
      tickTransition.body .reverted := by
  let locals := flapperTickLocals idWord
  let solm : Frame := { contract := contract, locals := locals }
  have hguardEnd :
      evalExpr? config solm evm
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
    simpa [solm, locals] using
      flapperTickEndGuard_eval_true evm idWord hend
  have hguardTic :
      evalExpr? config solm evm
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool false) := by
    simpa [solm, locals] using
      flapperTickTicGuard_eval_false evm idWord htic
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tickTransition, nonpayable, checkedAdd48Into, solm, locals] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardEnd) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hguardTic)

theorem flapperTickBodyRevertsOverflow (evm : EVM.State) (idWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hend :
      (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat)
    (htic : flapperTickTicWordOfState evm idWord = UInt256.ofNat 0)
    (hwrap :
      (flapperTickNewEndWordOfState evm).toNat <
        (flapperTickNowWordOfState evm).toNat) :
    ExecTransitionBody config contract evm (flapperTickLocals idWord)
      tickTransition.body .reverted := by
  let locals := flapperTickLocals idWord
  let newEnd := flapperTickNewEndWordOfState evm
  let localsEnd := flapperTickLocalsEnd idWord newEnd
  let solm : Frame := { contract := contract, locals := locals }
  let solmEnd : Frame := { contract := contract, locals := localsEnd }
  have hguardEnd :
      evalExpr? config solm evm
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
    simpa [solm, locals] using
      flapperTickEndGuard_eval_true evm idWord hend
  have hguardTic :
      evalExpr? config solm evm
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
    simpa [solm, locals] using
      flapperTickTicGuard_eval_true evm idWord htic
  have hlet :
      evalExpr? config solm evm (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat newEnd.toNat)) := by
    simpa [solm, locals, newEnd] using
      flapperTickNewEnd_eval evm idWord
  have hguardWrap :
      evalExpr? config solmEnd evm (.binary .ge (.var "end_") now48) =
        .ok (.bool false) := by
    simpa [solmEnd, localsEnd, newEnd] using
      flapperTickCheckedGuard_eval_false evm idWord hwrap
  exact ExecFuncBody.execBlockRevert <| by
    simpa [tickTransition, nonpayable, checkedAdd48Into, solm, solmEnd,
      locals, localsEnd, newEnd] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardEnd) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hguardTic) <|
            ExecBlock.consNormal (ExecStmt.letDecl hlet) <|
              ExecBlock.consRevert (ExecStmt.requireFalse hguardWrap)

theorem flapperTickBodyReturns (evm : EVM.State) (idWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hend :
      (flapperTickEndWordOfState evm idWord).toNat <
        (flapperTickTimestampWordOfState evm).toNat)
    (htic : flapperTickTicWordOfState evm idWord = UInt256.ofNat 0)
    (hwrap :
      ¬ (flapperTickNewEndWordOfState evm).toNat <
        (flapperTickNowWordOfState evm).toNat) :
    ExecTransitionBody config contract evm (flapperTickLocals idWord)
      tickTransition.body
      (.returned
        { contract := contract,
          locals := flapperTickLocalsEnd idWord (flapperTickNewEndWordOfState evm) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (flapperTickPackedSlot idWord)
          (flapperTickPackedEndWord (flapperTickPackedWordOfState evm idWord)
            (flapperTickNewEndWordOfState evm)))
        none) := by
  let locals := flapperTickLocals idWord
  let newEnd := flapperTickNewEndWordOfState evm
  let localsEnd := flapperTickLocalsEnd idWord newEnd
  let solm : Frame := { contract := contract, locals := locals }
  let solmEnd : Frame := { contract := contract, locals := localsEnd }
  let evm' :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (flapperTickPackedSlot idWord)
      (flapperTickPackedEndWord (flapperTickPackedWordOfState evm idWord) newEnd)
  have hguardEnd :
      evalExpr? config solm evm
          (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
    simpa [solm, locals] using
      flapperTickEndGuard_eval_true evm idWord hend
  have hguardTic :
      evalExpr? config solm evm
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
    simpa [solm, locals] using
      flapperTickTicGuard_eval_true evm idWord htic
  have hlet :
      evalExpr? config solm evm (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat newEnd.toNat)) := by
    simpa [solm, locals, newEnd] using
      flapperTickNewEnd_eval evm idWord
  have hguardWrap :
      evalExpr? config solmEnd evm (.binary .ge (.var "end_") now48) =
        .ok (.bool true) := by
    simpa [solmEnd, localsEnd, newEnd] using
      flapperTickCheckedGuard_eval_true evm idWord hwrap
  have hnewClean : UInt256.land newEnd flapperUint48Mask = newEnd := by
    simpa [newEnd, flapperTickNewEndWordOfState] using
      flapperUint48Mask_clean_right_file
        (flapperTickTimestampWordOfState evm + flapperTickTauWordOfState evm)
  have hassignBlock :
      ExecBlock config solmEnd evm [ .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        (.ok solmEnd evm') := by
    simpa [solmEnd, evm', localsEnd, newEnd] using
      assignStorageBlock
        (flapperTickEndLocal_eval evm idWord newEnd)
        (flapperTickAssignEnd evm idWord newEnd hnewClean)
  exact ExecFuncBody.execBlockOK <| by
    simpa [tickTransition, nonpayable, checkedAdd48Into, solm, solmEnd,
      locals, localsEnd, newEnd, evm'] using
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hguardEnd) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hguardTic) <|
            ExecBlock.consNormal (ExecStmt.letDecl hlet) <|
              ExecBlock.consNormal (ExecStmt.requireTrue hguardWrap) hassignBlock

theorem flapperTickBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 15))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨855⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I
    (⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_tick (cd := I.calldata) hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_tick_ok (I := I) hsz36
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let idWord := flapperTickIdWord I
    have hslotPackedEq :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperTickPackedSlot idWord) =
          storageRead I.codeOwner σ_evm (flapperTickPackedSlot idWord) := by
      simpa [evmSolm, initState, idWord] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (flapperTickPackedSlot idWord)
    have hslotTauEq :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (UInt256.ofNat 5) =
          storageRead I.codeOwner σ_evm (UInt256.ofNat 5) := by
      simpa [evmSolm, initState] using
        flapperInitStorageLoad_eq
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hAccounts (UInt256.ofNat 5)
    have hpackedEq :
        flapperTickPackedWordOfState evmSolm idWord =
          flapperTickPackedWord σ_evm I := by
      simpa [flapperTickPackedWordOfState, flapperTickPackedWord, idWord] using
        hslotPackedEq
    have htimestampEq :
        flapperTickTimestampWordOfState evmSolm = flapperTickTimestampWord I := by
      simp [flapperTickTimestampWordOfState, flapperTickTimestampWord, evmSolm,
        initState]
    have hticEq :
        flapperTickTicWordOfState evmSolm idWord =
          flapperTickTicWord σ_evm I := by
      rw [flapperTickTicWordOfState, flapperTickTicWord, hpackedEq]
      exact u256_land_comm
        (UInt256.div (flapperTickPackedWord σ_evm I) flapperUint48Shift160)
        flapperUint48Mask
    have hendEq :
        flapperTickEndWordOfState evmSolm idWord =
          flapperTickEndWord σ_evm I := by
      rw [flapperTickEndWordOfState, flapperTickEndWord, hpackedEq]
      exact u256_land_comm
        (UInt256.div (flapperTickPackedWord σ_evm I) flapperUint48Shift208)
        flapperUint48Mask
    have htauEq :
        flapperTickTauWordOfState evmSolm =
          flapperTickTauWord σ_evm I := by
      rw [flapperTickTauWordOfState, flapperTickTauWord]
      rw [hslotTauEq]
      exact u256_land_comm
        (UInt256.div (storageRead I.codeOwner σ_evm (UInt256.ofNat 5))
          flapperUint48Shift)
        flapperUint48Mask
    have hnowEq :
        flapperTickNowWordOfState evmSolm = flapperTickNowWord I := by
      simp [flapperTickNowWordOfState, flapperTickNowWord, htimestampEq]
    have hnewEq :
        flapperTickNewEndWordOfState evmSolm =
          flapperTickNewEndWord σ_evm I := by
      rw [flapperTickNewEndWordOfState, flapperTickNewEndWord, htimestampEq, htauEq]
      exact u256_land_comm
        (flapperTickTimestampWord I + flapperTickTauWord σ_evm I)
        flapperUint48Mask
    have henc : returnEquiv ByteArray.empty none tickTransition.returnType := by
      simpa [tickTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl rfl encodeReturnValues_nil)
    by_cases hend :
        (flapperTickEndWord σ_evm I).toNat < (flapperTickTimestampWord I).toNat
    · have hendSolm :
          (flapperTickEndWordOfState evmSolm idWord).toNat <
            (flapperTickTimestampWordOfState evmSolm).toNat := by
        simpa [hendEq, htimestampEq] using hend
      by_cases htic : flapperTickTicWord σ_evm I = UInt256.ofNat 0
      · have hticSolm :
            flapperTickTicWordOfState evmSolm idWord = UInt256.ofNat 0 := by
          simpa [hticEq] using htic
        by_cases hwrap :
            (flapperTickNewEndWord σ_evm I).toNat < (flapperTickNowWord I).toNat
        · have hwrapSolm :
              (flapperTickNewEndWordOfState evmSolm).toNat <
                (flapperTickNowWordOfState evmSolm).toNat := by
            simpa [hnewEq, hnowEq] using hwrap
          have hbody :
              ExecTransitionBody config contract evmSolm (flapperTickLocals idWord)
                tickTransition.body .reverted := by
            simpa [evmSolm, idWord] using
              flapperTickBodyRevertsOverflow evmSolm idWord
                (by simp only [evmSolm, initState]; exact hwv)
                hendSolm hticSolm hwrapSolm
          exact (flapperX_tick_overflow_revert (g := Sat256.ofUInt256 g) hsize hsz36
              hend htic hwrap hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hwrapSolm :
              ¬ (flapperTickNewEndWordOfState evmSolm).toNat <
                (flapperTickNowWordOfState evmSolm).toNat := by
            intro hbad
            exact hwrap (by simpa [hnewEq, hnowEq] using hbad)
          let evmWord :=
            flapperTickPackedEndWord (flapperTickPackedWord σ_evm I)
              (flapperTickNewEndWord σ_evm I)
          let solmWord :=
            flapperTickPackedEndWord (flapperTickPackedWordOfState evmSolm idWord)
              (flapperTickNewEndWordOfState evmSolm)
          have hwordEq : solmWord = evmWord := by
            simp [solmWord, evmWord, hpackedEq, hnewEq]
          have hbody :
              ExecTransitionBody config contract evmSolm (flapperTickLocals idWord)
                tickTransition.body
                (.returned
                  { contract := contract,
                    locals := flapperTickLocalsEnd idWord
                      (flapperTickNewEndWordOfState evmSolm) }
                  (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                    (flapperTickPackedSlot idWord) solmWord)
                  none) := by
            simpa [evmSolm, idWord, solmWord] using
              flapperTickBodyReturns evmSolm idWord
                (by simp only [evmSolm, initState]; exact hwv)
                hendSolm hticSolm hwrapSolm
          have hCreated :
              cA =
                (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                  (flapperTickPackedSlot idWord) solmWord).createdAccounts := by
            rw [storageStore_createdAccounts]
            simp [evmSolm, initState]
          have hAccounts' :
              accountMapEquiv
                (storageWrite I.codeOwner σ_evm
                  (flapperTickPackedSlot (flapperTickIdWord I)) evmWord)
                (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
                  (flapperTickPackedSlot idWord) solmWord).accountMap := by
            rw [storageWrite_eq, storageStore_accountMap]
            simpa [evmSolm, initState, idWord, hwordEq] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (flapperTickPackedSlot idWord) evmWord hAccounts
          have hx := flapperX_tick_ok (g := Sat256.ofUInt256 g) hsize hsz36 hperm
            hend htic hwrap hreach
          simpa [evmWord] using
            hx.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated
              hAccounts' henc
      · have hticSolm :
            flapperTickTicWordOfState evmSolm idWord ≠ UInt256.ofNat 0 := by
          intro hbad
          exact htic (by simpa [hticEq] using hbad)
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperTickLocals idWord)
              tickTransition.body .reverted := by
          simpa [evmSolm, idWord] using
            flapperTickBodyRevertsTic evmSolm idWord
              (by simp only [evmSolm, initState]; exact hwv)
              hendSolm hticSolm
        exact (flapperX_tick_tic_revert (g := Sat256.ofUInt256 g) hsize hsz36
            hend htic hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hendSolm :
          ¬ (flapperTickEndWordOfState evmSolm idWord).toNat <
            (flapperTickTimestampWordOfState evmSolm).toNat := by
        intro hbad
        exact hend (by simpa [hendEq, htimestampEq] using hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperTickLocals idWord)
            tickTransition.body .reverted := by
        simpa [evmSolm, idWord] using
          flapperTickBodyRevertsEnd evmSolm idWord
            (by simp only [evmSolm, initState]; exact hwv) hendSolm
      exact (flapperX_tick_end_revert (g := Sat256.ofUInt256 g) hsize hsz36
          hend hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_tick_none_short (I := I) hsz4 hshort
    have hrev := flapperX_tick_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
