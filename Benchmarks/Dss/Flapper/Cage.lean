import Benchmarks.Dss.Flapper.File
import Benchmarks.Dss.Flapper.Vat
import Benchmarks.Dss.Flapper.RuntimeBlocks_005
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flapper

def flapperCageRadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperCageLocals (rad : UInt256) : Store :=
  (∅ : Store).insert "rad" (.int (Int.ofNat rad.toNat))

def flapperCageLiveWorld (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  storageWrite I.codeOwner σ (UInt256.ofNat 7) (UInt256.ofNat 0)

def flapperCageVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (storageRead I.codeOwner (flapperCageLiveWorld σ I) (UInt256.ofNat 2))
    solcAddrMask

abbrev flapperCageMoveSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)

def flapperCageAuthMem (I : ExecutionEnv) : ByteArray :=
  flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory
    (ee := I) (mem := solcFreePtrMem)

def flapperCageCallMemSelector (I : ExecutionEnv) : ByteArray :=
  flapperCageMoveSelectorWord.toByteArray.write 0 (flapperCageAuthMem I) 128 32

def flapperCageCallMemThis (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (flapperCageCallMemSelector I) 132 32

def flapperCageCallMemSender (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0
    (flapperCageCallMemThis I) 164 32

def flapperCageMoveCallMem (I : ExecutionEnv) (rad : UInt256) : ByteArray :=
  rad.toByteArray.write 0 (flapperCageCallMemSender I) 196 32

def flapperCageCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [UInt256.ofNat 228, UInt256.ofNat 3140843579, flapperCageVatWord σ I,
    flapperCageRadWord I, UInt256.ofNat 360, sel]

theorem flapperCageAuthHashMem_eq (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory
        (ee := I) (mem := solcFreePtrMem) =
      twoWordHashMem (flapperRelyAuthWord I) (UInt256.ofNat 0) solcFreePtrMem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory,
    flapperRelyAuthWord, twoWordHashMem, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperCageAuthHashSlot (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory
          (ee := I) (mem := solcFreePtrMem)) =
      flapperRelyAuthSlot I := by
  rw [flapperCageAuthHashMem_eq]
  simpa [flapperRelyAuthSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyAuthWord I)
      (UInt256.ofNat 0) solcFreePtrMem

theorem flapperCageAuthMem_size (I : ExecutionEnv) :
    (flapperCageAuthMem I).size = 96 := by
  rw [flapperCageAuthMem, flapperCageAuthHashMem_eq]
  exact twoWordHashMem_size_96 (flapperRelyAuthWord I) (UInt256.ofNat 0)
    solcFreePtrMem_size

theorem flapperCageAuthMem_read64 (I : ExecutionEnv) :
    (flapperCageAuthMem I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  rw [flapperCageAuthMem, flapperCageAuthHashMem_eq]
  simpa using twoWordHashMem_read64 (flapperRelyAuthWord I) (UInt256.ofNat 0)
    solcFreePtrMem_size solcFreePtrMem_read64

@[simp] theorem flapperCageAuthMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (flapperCageAuthMem I) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [if_neg (by rw [flapperCageAuthMem_size I]; decide)]
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [flapperCageAuthMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem flapperCageRuntimeCallMem_eq (I : ExecutionEnv) (rad : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_3199_taken_memory
        (ee := I) (mem := flapperCageAuthMem I) (x0 := rad) =
      flapperCageMoveCallMem I rad := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3199_taken_memory,
    flapperCageMoveCallMem, flapperCageCallMemSender, flapperCageCallMemThis,
    flapperCageCallMemSelector, flapperCageMoveSelectorWord,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

theorem flapperCageMoveSelectorPrefix :
    flapperCageMoveSelectorWord.toByteArray.extract 0 4 = moveSelector := by
  native_decide

theorem flapperCageCallMemSelector_size_ge_160 (I : ExecutionEnv) :
    160 ≤ (flapperCageCallMemSelector I).size := by
  unfold flapperCageCallMemSelector
  exact toByteArray_write_size_ge_off_add32_unbounded flapperCageMoveSelectorWord
    (flapperCageAuthMem I) 128

theorem flapperCageCallMemThis_size_ge_164 (I : ExecutionEnv) :
    164 ≤ (flapperCageCallMemThis I).size := by
  unfold flapperCageCallMemThis
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (flapperCageCallMemSelector I) 132

theorem flapperCageCallMemSender_size_ge_196 (I : ExecutionEnv) :
    196 ≤ (flapperCageCallMemSender I).size := by
  unfold flapperCageCallMemSender
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.source.val)
    (flapperCageCallMemThis I) 164

theorem flapperCageMoveCallMem_size_ge_228 (I : ExecutionEnv) (rad : UInt256) :
    228 ≤ (flapperCageMoveCallMem I rad).size := by
  unfold flapperCageMoveCallMem
  exact toByteArray_write_size_ge_off_add32_unbounded rad
    (flapperCageCallMemSender I) 196

theorem flapperCageMoveCallMem_read64 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 128) := by
  unfold flapperCageMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded rad _ 196 64
    (by
      have h := flapperCageCallMemSender_size_ge_196 I
      omega)
    (by omega)]
  unfold flapperCageCallMemSender
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val) _ 164 64
    (by
      have h := flapperCageCallMemThis_size_ge_164 I
      omega)
    (by omega)]
  unfold flapperCageCallMemThis
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val) _ 132 64
    (by
      have h := flapperCageCallMemSelector_size_ge_160 I
      omega)
    (by omega)]
  unfold flapperCageCallMemSelector
  rw [toByteArray_write_read_below_of_gap_unbounded flapperCageMoveSelectorWord _
    128 64
    (by rw [flapperCageAuthMem_size I])
    (by omega)]
  exact flapperCageAuthMem_read64 I

@[simp] theorem flapperCageMoveCallMem_mload64 (I : ExecutionEnv) (rad : UInt256) :
    memLoad (UInt256.ofNat 64) (flapperCageMoveCallMem I rad) =
      UInt256.ofNat 128 := by
  unfold memLoad
  rw [show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [if_neg (by
    have h := flapperCageMoveCallMem_size_ge_228 I rad
    omega)]
  rw [flapperCageMoveCallMem_read64]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

@[simp] theorem flapperCageMoveCallMem_expr_eq (I : ExecutionEnv) (rad : UInt256) :
    (rad.toByteArray.write 0
      ((UInt256.ofNat I.source.val).toByteArray.write 0
        ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
          ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
            (flapperCageAuthMem I) (UInt256.ofNat 128).toNat 32)
          ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat 32)
        ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat 32)
      ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat 32) =
      flapperCageMoveCallMem I rad := by
  simp [flapperCageMoveCallMem, flapperCageCallMemSender, flapperCageCallMemThis,
    flapperCageCallMemSelector, flapperCageMoveSelectorWord,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat = 132 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat = 164 by decide,
    show ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat = 196 by decide]

@[simp] theorem flapperCageMoveCallMem_expr_mload64 (I : ExecutionEnv) (rad : UInt256) :
    memLoad (UInt256.ofNat 64)
      (rad.toByteArray.write 0
        ((UInt256.ofNat I.source.val).toByteArray.write 0
          ((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
            ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0
              (flapperCageAuthMem I) (UInt256.ofNat 128).toNat 32)
            ((UInt256.ofNat 128) + (UInt256.ofNat 4)).toNat 32)
          ((UInt256.ofNat 128) + (UInt256.ofNat 36)).toNat 32)
        ((UInt256.ofNat 128) + (UInt256.ofNat 68)).toNat 32) =
      UInt256.ofNat 128 := by
  rw [flapperCageMoveCallMem_expr_eq]
  exact flapperCageMoveCallMem_mload64 I rad

theorem flapperCageMoveCallMem_read196 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 196 32 =
      UInt256.toByteArray rad := by
  unfold flapperCageMoveCallMem
  exact toByteArray_write_read_back_of_gap_unbounded rad _ 196

theorem flapperCageMoveCallMem_read164 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 164 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  unfold flapperCageMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded rad _ 196 164
    (by
      have h := flapperCageCallMemSender_size_ge_196 I
      omega)
    (by omega)]
  unfold flapperCageCallMemSender
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.source.val) (flapperCageCallMemThis I) 164

theorem flapperCageMoveCallMem_read132 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 132 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold flapperCageMoveCallMem
  rw [toByteArray_write_read_below_of_gap_unbounded rad _ 196 132
    (by
      have h := flapperCageCallMemSender_size_ge_196 I
      omega)
    (by omega)]
  unfold flapperCageCallMemSender
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val) _ 164 132
    (by
      have h := flapperCageCallMemThis_size_ge_164 I
      omega)
    (by omega)]
  unfold flapperCageCallMemThis
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.codeOwner.val) (flapperCageCallMemSelector I) 132

theorem flapperCageMoveCallMem_read128_4 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 128 4 = moveSelector := by
  unfold flapperCageMoveCallMem
  rw [toByteArray_write_read_below_len_of_gap rad _ 196 128 4
    (by
      have h := flapperCageCallMemSender_size_ge_196 I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperCageCallMemSender_size_ge_196 I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperCageCallMemSender
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.source.val) _ 164 128 4
    (by
      have h := flapperCageCallMemThis_size_ge_164 I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperCageCallMemThis_size_ge_164 I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperCageCallMemThis
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val) _ 132 128 4
    (by
      have h := flapperCageCallMemSelector_size_ge_160 I
      omega)
    (by omega) (by norm_num) (by norm_num)
    (by
      have h := flapperCageCallMemSelector_size_ge_160 I
      have hU : 0 < USize.size := by native_decide
      omega)]
  unfold flapperCageCallMemSelector
  rw [toByteArray_write_read_window_of_gap_unbounded flapperCageMoveSelectorWord
    (flapperCageAuthMem I) 128 0 4
    (by norm_num) (by norm_num) (by norm_num)]
  exact flapperCageMoveSelectorPrefix

theorem flapperCageMoveCallMem_read128_100 (I : ExecutionEnv) (rad : UInt256) :
    (flapperCageMoveCallMem I rad).readWithPadding 128 100 =
      moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (UInt256.ofNat I.source.val) ++ UInt256.toByteArray rad := by
  rw [show 100 = 4 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (flapperCageMoveCallMem I rad) 128 4 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperCageMoveCallMem_size_ge_228 I rad
      omega)]
  rw [show 96 = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (flapperCageMoveCallMem I rad) 132 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperCageMoveCallMem_size_ge_228 I rad
      omega)]
  rw [show 64 = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (flapperCageMoveCallMem I rad) 164 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := flapperCageMoveCallMem_size_ge_228 I rad
      omega)]
  rw [flapperCageMoveCallMem_read128_4, flapperCageMoveCallMem_read132,
    flapperCageMoveCallMem_read164, flapperCageMoveCallMem_read196]
  simp [ByteArray.append_assoc]

theorem flapperCageMoveEncode_eq (I : ExecutionEnv) (rad : UInt256) :
    config.externalABI.encode? "move"
        [.address I.codeOwner, .address I.source, .int (Int.ofNat rad.toNat)] =
      some ((flapperCageMoveCallMem I rad).readWithPadding 128 100) := by
  rw [flapperCageMoveCallMem_read128_100]
  have hrad :
      0 ≤ Int.ofNat rad.toNat ∧
        Int.ofNat rad.toNat < Int.ofNat (EVM.twoPow 256) := by
    constructor
    ·
      exact Int.natCast_nonneg rad.toNat
    ·
      have hltNat : rad.toNat < EVM.twoPow 256 := by
        change rad.val.val < EVM.twoPow 256
        exact rad.val.isLt
      exact Int.ofNat_lt.mpr hltNat
  change externalABI.encode? "move"
        [.address I.codeOwner, .address I.source, .int (Int.ofNat rad.toNat)] =
      some (moveSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) ++
        UInt256.toByteArray (UInt256.ofNat I.source.val) ++ UInt256.toByteArray rad)
  have hencOwner :
      encodeABIValue? addr (.address I.codeOwner) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) := by
    have hword : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by
      apply u256_inj
      unfold EVM.word EVM.uintN UInt256.ofNat UInt256.toNat
      simp only [Fin.ofNat]
      change I.codeOwner.val % EVM.twoPow 256 = I.codeOwner.val % UInt256.size
      simp [EVM.twoPow, UInt256.size]
    simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rw [hword]
  have hencSource :
      encodeABIValue? addr (.address I.source) =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) := by
    have hword : EVM.word I.source.val = UInt256.ofNat I.source.val := by
      apply u256_inj
      unfold EVM.word EVM.uintN UInt256.ofNat UInt256.toNat
      simp only [Fin.ofNat]
      change I.source.val % EVM.twoPow 256 = I.source.val % UInt256.size
      simp [EVM.twoPow, UInt256.size]
    simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rw [hword]
  have hencRad :
      encodeABIValue? uint256 (.int (Int.ofNat rad.toNat)) =
        some (EVM.Word.toBytesBE rad) := by
    have hword : EVM.word rad.toNat = rad := u256_ofNat_toNat rad
    have hltNat : rad.toNat < EVM.twoPow 256 := by
      change rad.val.val < EVM.twoPow 256
      exact rad.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hltNat]
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by
    native_decide
  have hdynAddr : isDynamicABIType addr = false := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by
    native_decide
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
          [.address I.codeOwner, .address I.source, .int (Int.ofNat rad.toNat)] =
        some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val) ++
          EVM.Word.toBytesBE (UInt256.ofNat I.source.val) ++ EVM.Word.toBytesBE rad) := by
    simp only [encodeABIValues?, encodeABIValuesFrom?, hhead, hencOwner, hencSource,
      hencRad, hdynAddr, hdynUint, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  unfold externalABI encodeCallWithSelector?
  simp only [hpayload, Option.bind, bind]
  rw [list_toByteArray_append, list_toByteArray_append]
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

theorem flapperX_cage_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨700⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3106)
      (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd700⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 32)
      (by simpa using hsz36) hsize
  have hcondLen :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd722 := flapperRuntimeBlocks.flapperRuntime_block_700_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd700
  have rd3106raw := flapperRuntimeBlocks.flapperRuntime_block_722
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd722
  exact ⟨_, _, by simpa [flapperCageRadWord, calldataWord] using rd3106raw⟩

theorem flapperX_cage_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨700⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd700⟩ := hreach
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
  have rd718 := flapperRuntimeBlocks.flapperRuntime_block_700_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd700
  exact flapperRuntimeBlocks.flapperRuntime_block_718
    (R := flapperRuntimeBlocks.flapperRuntime_block_700_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_700_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd718

theorem flapperX_cage_auth_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) ≠ UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3106) (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3106⟩ := hdecode
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              (flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory
                (ee := I) (mem := solcFreePtrMem)))) = UInt256.ofNat 0 := by
    rw [flapperCageAuthHashSlot]
    exact u256_eq_of_ne (by
      intro h
      exact hauth h.symm)
  obtain ⟨_, _, rd3130⟩ := flapperRuntimeBlocks.flapperRuntime_block_3106_fallthrough
    (R := flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondAuth rd3106
  exact flapperRuntimeBlocks.flapperRuntime_block_3130
    (R := flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3130

theorem flapperX_cage_auth_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hdecode : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3106) (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat 3199) (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      (flapperCageAuthMem I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3106⟩ := hdecode
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              (flapperRuntimeBlocks.flapperRuntime_block_3106_taken_memory
                (ee := I) (mem := solcFreePtrMem)))) ≠ UInt256.ofNat 0 := by
    rw [flapperCageAuthHashSlot]
    rw [hauth]
    decide
  obtain ⟨_, _, rd3199⟩ := flapperRuntimeBlocks.flapperRuntime_block_3106_taken
    (R := flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondAuth (by jump_dest) rd3106
  exact ⟨_, _, _, by simpa [flapperCageAuthMem] using rd3199⟩

theorem flapperX_cage_no_code_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hcodeSize :
      extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I) =
        UInt256.ofNat 0)
    (h3199 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3199)
      (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      (flapperCageAuthMem I) aw ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw3199, _, _, rd3199⟩ := h3199
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord
              (storageWrite I.codeOwner σ (UInt256.ofNat 7) (UInt256.ofNat 0))
              (UInt256.land
                (storageRead I.codeOwner
                  (storageWrite I.codeOwner σ (UInt256.ofNat 7) (UInt256.ofNat 0))
                  (UInt256.ofNat 2))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) = UInt256.ofNat 0 := by
    simpa [flapperCageLiveWorld, flapperCageVatWord, solcAddrMask] using
      (by rw [hcodeSize]; decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I))) =
            UInt256.ofNat 0)
  obtain ⟨_, _, rd3285⟩ := flapperRuntimeBlocks.flapperRuntime_block_3199_fallthrough
    (x0 := flapperCageRadWord I) (R := UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm hcondExt rd3199
  exact flapperRuntimeBlocks.flapperRuntime_block_3285
    (R := flapperRuntimeBlocks.flapperRuntime_block_3199_fallthrough_stack
      (ee := I) (mem := flapperCageAuthMem I) (σ := σ)
      (x0 := flapperCageRadWord I) (R := UInt256.ofNat 360 :: [sel]))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3199_fallthrough_stack,
        List.length_cons, List.length_nil]
      omega)
    rd3285

theorem flapperX_cage_call_boundary {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hcodeSize :
      extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I) ≠
        UInt256.ofNat 0)
    (h3199 : ∃ aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3199)
      (flapperCageRadWord I :: UInt256.ofNat 360 :: [sel])
      (flapperCageAuthMem I) aw ByteArray.empty (cA, σ) k C) :
    ∃ gasArg aw k C, RD flapperBytecode I g
      (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3292)
      (gasArg :: flapperCageVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
        UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
        flapperCageCallRest σ I sel)
      (flapperCageMoveCallMem I (flapperCageRadWord I)) aw ByteArray.empty
      (cA, flapperCageLiveWorld σ I) k C := by
  obtain ⟨aw, _, _, rd3199⟩ := h3199
  have hcondExt :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord
              (storageWrite I.codeOwner σ (UInt256.ofNat 7) (UInt256.ofNat 0))
              (UInt256.land
                (storageRead I.codeOwner
                  (storageWrite I.codeOwner σ (UInt256.ofNat 7) (UInt256.ofNat 0))
                  (UInt256.ofNat 2))
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    simpa [flapperCageLiveWorld, flapperCageVatWord, solcAddrMask] using
      (by
        rw [isZero_eq_zero_of_ne hcodeSize]
        decide :
        UInt256.isZero (UInt256.isZero
          (extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I))) ≠
            UInt256.ofNat 0)
  obtain ⟨aw3289, k3289, C3289, rd3289raw⟩ :=
    flapperRuntimeBlocks.flapperRuntime_block_3199_taken_packed
    (x0 := flapperCageRadWord I) (R := UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hperm hcondExt (by jump_dest) rd3199
  have rd3289 :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3289)
        (UInt256.isZero
            (extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I)) ::
          flapperCageVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperCageCallRest σ I sel)
        (flapperCageMoveCallMem I (flapperCageRadWord I)) aw3289 ByteArray.empty
        (cA, flapperCageLiveWorld σ I) k3289 C3289 := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3199_taken_stack,
      flapperRuntimeBlocks.flapperRuntime_block_3199_taken_memory,
      flapperCageLiveWorld, flapperCageVatWord, flapperCageRuntimeCallMem_eq,
      flapperCageCallRest, flapperCageAuthMem_mload64,
      show UInt256.sub (UInt256.ofNat 128) (UInt256.ofNat 128) = UInt256.ofNat 0 by
        decide,
      show UInt256.ofNat 0 + UInt256.ofNat 100 = UInt256.ofNat 100 by decide,
      show UInt256.ofNat 128 + UInt256.ofNat 100 = UInt256.ofNat 228 by decide]
      using rd3289raw
  have rd3291 := flapperRuntimeBlocks.flapperRuntime_block_3289
    (x0 := UInt256.isZero
      (extCodeSizeWord (flapperCageLiveWorld σ I) (flapperCageVatWord σ I)))
    (R := flapperCageVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
      UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
      flapperCageCallRest σ I sel)
    (by simp only [flapperCageCallRest, List.length_cons, List.length_nil]; omega)
    rd3289
  have rd3291' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3291)
        (flapperCageVatWord σ I :: UInt256.ofNat 0 :: UInt256.ofNat 128 ::
          UInt256.ofNat 100 :: UInt256.ofNat 128 :: UInt256.ofNat 0 ::
          flapperCageCallRest σ I sel)
        (flapperCageMoveCallMem I (flapperCageRadWord I)) aw3289 ByteArray.empty
        (cA, flapperCageLiveWorld σ I) (k3289 + 2) (C3289 + 3) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3289_stack] using rd3291
  obtain ⟨gasArg, rd3292raw⟩ := RD.rawGas rd3291' (by native_decide)
    (by simp only [flapperCageCallRest, List.length_cons, List.length_nil]; omega)
  refine ⟨gasArg, aw3289, k3289 + 2 + 1, C3289 + 3 + 2, ?_⟩
  simpa [flapperRuntimeBlocks.flapperRuntime_block_3289_stack,
    show UInt256.ofNat 3291 + ⟨1⟩ = UInt256.ofNat 3292 by native_decide]
    using rd3292raw

theorem flapperX_cage_call_failure {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3293)
      (UInt256.ofNat 0 :: flapperCageCallRest σ I sel) mem aw rdata world k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3300 := flapperRuntimeBlocks.flapperRuntime_block_3293_fallthrough
    (x0 := UInt256.ofNat 0) (R := flapperCageCallRest σ I sel)
    (by simp only [flapperCageCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) h
  exact flapperRuntimeBlocks.flapperRuntime_block_3300
    (R := flapperRuntimeBlocks.flapperRuntime_block_3293_fallthrough_stack
      (x0 := UInt256.ofNat 0) (R := flapperCageCallRest σ I sel))
    (by
      simp only [flapperRuntimeBlocks.flapperRuntime_block_3293_fallthrough_stack,
        flapperCageCallRest, List.length_cons, List.length_nil]
      omega)
    rd3300

theorem flapperX_cage_call_success {cA gh bl σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {σ : AccountMap}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3293)
      (UInt256.ofNat 1 :: flapperCageCallRest σ I sel) mem aw rdata world k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) world ByteArray.empty := by
  have rd3309 := flapperRuntimeBlocks.flapperRuntime_block_3293_taken
    (x0 := UInt256.ofNat 1) (R := flapperCageCallRest σ I sel)
    (by simp only [flapperCageCallRest, List.length_cons, List.length_nil]; omega)
    (by decide) (by jump_dest) h
  have rd3309' :
      RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3309)
        (UInt256.ofNat 0 :: flapperCageCallRest σ I sel) mem aw rdata world
        (k + 5) (C + 22) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3293_taken_stack,
      flapperCageCallRest] using rd3309
  have rd360 := flapperRuntimeBlocks.flapperRuntime_block_3309
    (x0 := UInt256.ofNat 0) (x1 := UInt256.ofNat 228)
    (x2 := UInt256.ofNat 3140843579) (x3 := flapperCageVatWord σ I)
    (x4 := flapperCageRadWord I) (x5 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd3309'
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel]) (by simp only [List.length_cons, List.length_nil]; omega) rd360

theorem flapperDispatch_cage {cd : ByteArray}
    (hsel : ((⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some cageTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition])
    (post := [dealTransition, denyTransition, fileTransition, fillTransition,
      gemTransition, kickTransition, kicksTransition, lidTransition, liveTransition,
      relyTransition, tauTransition, tendTransition, tickTransition, ttlTransition,
      vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
  · rw [flapperCageSelectorBytes]
    exact hsel

theorem flapperSelectorDispatch_cage {cd : ByteArray}
    (hsel : ((⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) == cd.extract 0 4) = true) :
    selectorDispatchMsg contract cd = some cageTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList]
  rw [show contract.transitions =
      [begTransition, bidsTransition] ++ cageTransition ::
        [dealTransition, denyTransition, fileTransition, fillTransition,
          gemTransition, kickTransition, kicksTransition, lidTransition, liveTransition,
          relyTransition, tauTransition, tendTransition, tickTransition, ttlTransition,
          vatTransition, wardsTransition, yankTransition] by rfl]
  refine dispatchList_eq_some_of_split ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
  · rw [flapperCageSelectorBytes]
    exact hsel

theorem flapperDecode_cage_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata =
      some (flapperCageLocals (flapperCageRadWord I)) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["rad"] [abiUInt256] I.calldata =
    some (flapperCageLocals (flapperCageRadWord I))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      flapperCageRadWord I := by
    simpa [flapperCageRadWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["rad"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (start := 0) htake4]
  change decodeCalldata.insertValues ["rad"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)]
      ∅ =
    some (flapperCageLocals (flapperCageRadWord I))
  rw [hword4]
  simp [decodeCalldata.insertValues, flapperCageLocals]

theorem flapperDecode_cage_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["rad"] [abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["rad"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short
    (mode := DecodeMode.legacySolc05) (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperCageAssignLive (evm : EVM.State) (rad : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := flapperCageLocals rad } evm
      .storage liveRef (.int 0) =
      .ok ({ contract := contract, locals := flapperCageLocals rad },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 7)
          (UInt256.ofNat 0)) := by
  let locals := flapperCageLocals rad
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef := { base := "live", steps := [] }
  have hbase : locals.get? "live" = none := by
    simp [locals, flapperCageLocals]
  have her : evalStorageRef config solm evm liveRef = .ok er := by
    simp [solm, er, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind,
      bind, pure]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er =
      fun _ => some (wordLoc (⟨7⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨7⟩ : UInt256)) (.int 0) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 7) (UInt256.ofNat 0)) := by
    simpa [wordLoc, uint256Loc, show (⟨7⟩ : UInt256) = UInt256.ofNat 7 by decide] using
      storageLocStore_uint256 evm (⟨7⟩ : UInt256) (UInt256.ofNat 0)
  simpa [solm, locals] using
    assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

theorem flapperCageVat_eval (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
          solcAddrMask).toNat)) := by
  let er : EvaledStorageRef := { base := "vat", steps := [] }
  have her : evalStorageRef config { contract := contract, locals := locals } evm vatRef =
      .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    decide
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨2⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := her)
    (hty := hty) (hloc := hloc), flapperStorageLocLoad_address]
  simp [show (⟨2⟩ : UInt256) = UInt256.ofNat 2 by decide]

theorem flapperCageExtCodeSizeWord_eval (evm : EVM.State) (targetWord : UInt256) :
    EVM.Word.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
          (fun acc => acc.code.size)) =
      extCodeSizeWord evm.accountMap targetWord := by
  unfold extCodeSizeWord State.lookupAccount
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find? (AccountAddress.ofNat targetWord.toNat) <;> rfl

theorem flapperCageExtGuard_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none)
    (hcodeSize :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
            solcAddrMask) ≠ UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  let targetWord :=
    UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
      solcAddrMask
  have hreceiver := flapperCageVat_eval evm locals hbase
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperCageExtCodeSizeWord_eval evm targetWord
  have hpos :
      0 <
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hcodeSize
    simpa [targetWord, hword] using
      (uint256_toNat_eq_zero (a := extCodeSizeWord evm.accountMap targetWord) (by
        rw [← hword]
        exact hzero))
  simp only [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hgt :
      decide (Int.ofNat
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat > 0) = true := by
    have hposInt :
        (0 : Int) <
          Int.ofNat
            (EVM.Word.ofNat
              ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
                (fun acc => acc.code.size))).toNat := by
      norm_num
      exact hpos
    exact decide_eq_true hposInt
  simpa [targetWord, hgt]

theorem flapperCageExtGuard_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vat" = none)
    (hcodeSize :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
            solcAddrMask) = UInt256.ofNat 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  let targetWord :=
    UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
      solcAddrMask
  have hreceiver := flapperCageVat_eval evm locals hbase
  have hword :
      EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size)) = extCodeSizeWord evm.accountMap targetWord :=
    flapperCageExtCodeSizeWord_eval evm targetWord
  have hzero :
      (EVM.Word.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hword, hcodeSize]
    rfl
  simp only [evalExpr?, hreceiver, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hgt :
      decide (Int.ofNat
        (EVM.Word.ofNat
          ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
            (fun acc => acc.code.size))).toNat > 0) = false := by
    exact decide_eq_false (by
      intro hpos
      rw [hzero] at hpos
      norm_num at hpos)
  simpa [targetWord, hgt]

theorem flapperCagePrefixOk (evm : EVM.State) (rad : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1) :
    ExecBlock config
      { contract := contract, locals := flapperCageLocals rad } evm
      (nonpayable ++ auth ++
        [ .assign .storage liveRef (.intLit 0) ])
      (.ok { contract := contract, locals := flapperCageLocals rad }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 7)
          (UInt256.ofNat 0))) := by
  let locals := flapperCageLocals rad
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperCageLocals]
  have hguard :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hrhs : evalExpr? config solm evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hassign :
      assignStorageRef? config solm evm .storage liveRef (.int 0) =
        .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 7) (UInt256.ofNat 0)) := by
    simpa [solm, locals] using flapperCageAssignLive evm rad
  simpa [nonpayable, auth, solm, locals] using
    nonpayableRequireAssignStorageBlock (cfg := config) (solm := solm)
      (evm := evm)
      (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (UInt256.ofNat 7) (UInt256.ofNat 0))
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0) (ref := liveRef) (value := .int 0)
      hwv hguard hrhs hassign

theorem flapperCageBodyRevertsAuth (evm : EVM.State) (rad : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm (flapperCageLocals rad)
      cageTransition.body .reverted := by
  let locals := flapperCageLocals rad
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals, flapperCageLocals]
  have hguard :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool false) := by
    exact flapperRelyAuthGuard_false evm locals hbaseWards hauth
  exact ExecFuncBody.execBlockRevert <| by
    simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts, locals, solm] using
      nonpayableSecondRequireReverts (cfg := config) (solm := solm) (evm := evm)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest :=
          [ .assign .storage liveRef (.intLit 0),
            .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
            .externalCall (.storage vatRef) "move" (.intLit 0)
              [thisAddr, sender, .var "rad"] "_moveRet" ])
        hwv hguard

theorem flapperCageBodyRevertsNoCode (evm : EVM.State) (rad : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1)
    (hcodeSize :
      extCodeSizeWord
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (UInt256.ofNat 7) (UInt256.ofNat 0)).accountMap
          (UInt256.land
            (Solm.EVM.storageLoad
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
                (UInt256.ofNat 7) (UInt256.ofNat 0))
              (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
                (UInt256.ofNat 7) (UInt256.ofNat 0)).executionEnv.codeOwner
              (UInt256.ofNat 2))
            solcAddrMask) = UInt256.ofNat 0) :
    ExecTransitionBody config contract evm (flapperCageLocals rad)
      cageTransition.body .reverted := by
  let locals := flapperCageLocals rad
  let solm : Frame := { contract := contract, locals := locals }
  let evmLive :=
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 7)
      (UInt256.ofNat 0)
  have hpref :
      ExecBlock config solm evm
        (nonpayable ++ auth ++
          [ .assign .storage liveRef (.intLit 0) ])
        (.ok solm evmLive) := by
    simpa [solm, locals, evmLive] using
      flapperCagePrefixOk evm rad hwv hauth
  have hbaseVat : locals.get? "vat" = none := by
    simp [locals, flapperCageLocals]
  have hguard :
      evalExpr? config solm evmLive
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    simpa [solm, locals, evmLive] using
      flapperCageExtGuard_false evmLive locals hbaseVat hcodeSize
  have htail :
      ExecBlock config solm evmLive
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [thisAddr, sender, .var "rad"] "_moveRet")
        .reverted := by
    simpa [checkedExternalCallStmts, solm, locals] using
      checkedExternalCallNoCode (cfg := config) (C := contract)
        (evm := evmLive) (locals := locals) (receiver := .storage vatRef)
        (name := "move") (sendVal := 0) (args := [thisAddr, sender, .var "rad"])
        (retVar := "_moveRet") hguard
  exact ExecFuncBody.execBlockRevert <| by
    simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts, solm, locals] using
      execBlock_append hpref htail

theorem flapperCageArgs_eval (evm : EVM.State) (rad : UInt256) :
    evalExprs? config
      { contract := contract, locals := flapperCageLocals rad } evm
      [thisAddr, sender, .var "rad"] =
      .ok [.address evm.executionEnv.codeOwner, .address evm.executionEnv.source,
        .int (Int.ofNat rad.toNat)] := by
  simp [evalExprs?, evalExpr?, thisAddr, sender, envValue,
    flapperCageLocals, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem flapperCageBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 2))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨700⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hselLit :
      ((⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ : ByteArray) == I.calldata.extract 0 4) =
        true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 2) (by decide) hsel
  have hd : dispatchMsg contract I.calldata = some cageTransition :=
    flapperDispatch_cage hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_cage_ok (I := I) hsz36
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let rad := flapperCageRadWord I
    have hdecode := flapperX_cage_decode_ok
      (g := Sat256.ofUInt256 g) hsize hsz36 hreach
    by_cases hauthEvm :
        storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) = UInt256.ofNat 1
    · have h3199 := flapperX_cage_auth_ok (g := Sat256.ofUInt256 g)
        hauthEvm hdecode
      have hloadAuthEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        simpa [evmSolm, initState] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperRelyAuthSlot I)
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) = UInt256.ofNat 1 := by
        rw [hloadAuthEq]
        exact hauthEvm
      let evmLive :=
        Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner
          (UInt256.ofNat 7) (UInt256.ofNat 0)
      have hStateLive :
          CallStateRel (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            I (cA, flapperCageLiveWorld σ_evm I) evmLive := by
        have h0 : CallStateRel
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            I (cA, σ_evm) evmSolm :=
          CallStateRel.initState hAccounts
        have h1 := h0.storageStore_codeOwner (UInt256.ofNat 7) (UInt256.ofNat 0)
        simpa [evmLive, evmSolm, flapperCageLiveWorld, initState, storageWrite_eq] using h1
      have hVatLoadEq :
          Solm.EVM.storageLoad evmLive evmLive.executionEnv.codeOwner (UInt256.ofNat 2) =
            storageRead I.codeOwner (flapperCageLiveWorld σ_evm I) (UInt256.ofNat 2) := by
        have hmap := storageLoad_accountMapEquiv
          (evm1 := initState cA gh bl (flapperCageLiveWorld σ_evm I) σ₀
            (Sat256.ofUInt256 g) A I)
          (evm2 := evmLive)
          (by simpa [evmLive, evmSolm, initState] using hStateLive.accounts)
          I.codeOwner (UInt256.ofNat 2)
        have hread :
            Solm.EVM.storageLoad
                (initState cA gh bl (flapperCageLiveWorld σ_evm I) σ₀
                  (Sat256.ofUInt256 g) A I)
                I.codeOwner (UInt256.ofNat 2) =
              storageRead I.codeOwner (flapperCageLiveWorld σ_evm I) (UInt256.ofNat 2) := by
          simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            storageRead_eq]
        have howner : evmLive.executionEnv.codeOwner = I.codeOwner := by
          dsimp [evmLive]
          rw [storageStore_executionEnv]
          simp [evmSolm, initState]
        rw [howner]
        simpa [evmLive, evmSolm, initState] using hmap.symm.trans hread
      have hVatWordSolm :
          UInt256.land
              (Solm.EVM.storageLoad evmLive evmLive.executionEnv.codeOwner (UInt256.ofNat 2))
              solcAddrMask =
            flapperCageVatWord σ_evm I := by
        rw [hVatLoadEq]
        rfl
      by_cases hcodeSize :
          extCodeSizeWord (flapperCageLiveWorld σ_evm I)
              (flapperCageVatWord σ_evm I) = UInt256.ofNat 0
      · have hcodeSizeSolm :
            extCodeSizeWord evmLive.accountMap
                (UInt256.land
                  (Solm.EVM.storageLoad evmLive evmLive.executionEnv.codeOwner
                    (UInt256.ofNat 2))
                  solcAddrMask) = UInt256.ofNat 0 := by
          have hmapCode := extCodeSizeWord_accountMapEquiv hStateLive.accounts
            (flapperCageVatWord σ_evm I)
          exact (by
            simpa [hVatWordSolm] using hmapCode.symm.trans hcodeSize)
        have hbody :
            ExecTransitionBody config contract evmSolm (flapperCageLocals rad)
              cageTransition.body .reverted := by
          simpa [evmSolm, evmLive, rad] using
            flapperCageBodyRevertsNoCode evmSolm rad
              (by simp only [evmSolm, initState]; exact hwv) hauthSolm hcodeSizeSolm
        exact (flapperX_cage_no_code_revert (g := Sat256.ofUInt256 g) hperm
            hcodeSize h3199)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hcodeSizeSolmNe :
            extCodeSizeWord evmLive.accountMap
                (UInt256.land
                  (Solm.EVM.storageLoad evmLive evmLive.executionEnv.codeOwner
                    (UInt256.ofNat 2))
                  solcAddrMask) ≠ UInt256.ofNat 0 := by
          intro hzero
          apply hcodeSize
          have hmapCode := extCodeSizeWord_accountMapEquiv hStateLive.accounts
            (flapperCageVatWord σ_evm I)
          have hzeroVat :
              extCodeSizeWord evmLive.accountMap (flapperCageVatWord σ_evm I) =
                UInt256.ofNat 0 := by
            simpa [hVatWordSolm] using hzero
          exact hmapCode.trans hzeroVat
        let frameLive : Frame := { contract := contract, locals := flapperCageLocals rad }
        have hbaseVat : (flapperCageLocals rad).get? "vat" = none := by
          simp [flapperCageLocals]
        have hguardTrue :
            evalExpr? config frameLive evmLive
              (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
                .ok (.bool true) := by
          simpa [frameLive] using
            flapperCageExtGuard_true evmLive (flapperCageLocals rad) hbaseVat
              hcodeSizeSolmNe
        have hpref :
            ExecBlock config frameLive evmSolm
              (nonpayable ++ auth ++ [ .assign .storage liveRef (.intLit 0) ])
              (.ok frameLive evmLive) := by
          simpa [frameLive, evmLive, evmSolm, rad] using
            flapperCagePrefixOk evmSolm rad
              (by simp only [evmSolm, initState]; exact hwv) hauthSolm
        have htailExternal :
            BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config frameLive evmLive
              [ .externalCall (.storage vatRef) "move" (.intLit 0)
                  [thisAddr, sender, .var "rad"] "_moveRet" ]
              (runtimeExit (.abi cageTransition.returnType)) := by
          obtain ⟨gasArg, awCall, kCall, CCall, rdCall⟩ :=
            flapperX_cage_call_boundary (g := Sat256.ofUInt256 g) hperm
              hcodeSize h3199
          refine BlockProgress.externalCall
            (h := rdCall) (hState := hStateLive)
            (receiver := .storage vatRef) (eth := .intLit 0)
            (args := [thisAddr, sender, .var "rad"])
            (argVals := [.address I.codeOwner, .address I.source,
              .int (Int.ofNat rad.toNat)])
            (tgt := AccountAddress.ofNat (flapperCageVatWord σ_evm I).toNat)
            (name := "move") (retVar := "_moveRet") (value := 0) (stmts := [])
            ?_ ?_ ?_ ?_ ?_ ?_ (by native_decide) hperm
            (by simp only [flapperCageCallRest, List.length_cons, List.length_nil]; omega)
            (by exact True.intro) ?_ ?_
          · have hrecv := flapperCageVat_eval evmLive (flapperCageLocals rad) hbaseVat
            simpa [frameLive, hVatWordSolm] using hrecv
          · simp [evalExpr?, pure]
          · simpa [frameLive, evmLive, evmSolm, initState, storageStore_executionEnv] using
              flapperCageArgs_eval evmLive rad
          · exact wordOfInt_zero.symm
          · rw [accountAddress_ofUInt256_eq_ofNat_toNat]
            apply Fin.ext
            simp [EVM.address, EVM.uintN, AccountAddress.ofNat, EVM.twoPow,
              AccountAddress.size]
          · simpa [rad,
              show (UInt256.ofNat 128).toNat = 128 by decide,
              show (UInt256.ofNat 100).toNat = 100 by decide] using
              flapperCageMoveEncode_eq I rad
          · intro out evm' world' k' C' cur rdSucc hcall hState' hsizeOut
            have hdecodeOut : config.externalABI.decode? "move" out = some [] := by
              simp [config, externalABI, decodeVoid?]
            rw [hdecodeOut]
            have hret : RDret flapperBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                world' ByteArray.empty := by
              exact flapperX_cage_call_success (σ := σ_evm) (sel := flapperSelWord I) (h := by
                simpa [callCursor,
                  show UInt256.ofNat 3292 + ⟨1⟩ = UInt256.ofNat 3293 by native_decide]
                  using rdSucc)
            exact BlockProgress.ofRDret (hsource := ExecBlock.nil) hret
              hState'.created.symm hState'.accounts
              (by simpa [cageTransition] using abiVoidFallthrough)
          · intro out world' k' C' cur rdFail
            exact flapperX_cage_call_failure (σ := σ_evm) (sel := flapperSelWord I) (h := by
              simpa [callCursor,
                show UInt256.ofNat 3292 + ⟨1⟩ = UInt256.ofNat 3293 by native_decide]
                using rdFail)
        have htail :
            BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config frameLive evmLive
              (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
                [thisAddr, sender, .var "rad"] "_moveRet")
              (runtimeExit (.abi cageTransition.returnType)) := by
          simpa [checkedExternalCallStmts] using
            BlockProgress.cons (ExecStmt.requireTrue hguardTrue) htailExternal
        have hprogress :
            BlockProgress flapperBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config frameLive evmSolm cageTransition.body
              (runtimeExit (.abi cageTransition.returnType)) := by
          have hp := BlockProgress.prepend hpref htail
          simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts, frameLive] using hp
        exact hprogress.toRuntimeEquivalenceFor hcode
          (fun result hfunc => by
            exact solmExec.intro (flapperSelectorDispatch_cage hselLit) rfl hdec
              (by simp [evmSolm, initState, Sat256.ofUInt256, Sat256.toUInt256])
              hfunc)
          (by intro result endpoint h; exact h)
    · have hloadAuthEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        simpa [evmSolm, initState] using
          flapperInitStorageLoad_eq
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hAccounts (flapperRelyAuthSlot I)
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) ≠ UInt256.ofNat 1 := by
        intro hbad
        exact hauthEvm (by rw [← hloadAuthEq]; exact hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm (flapperCageLocals rad)
            cageTransition.body .reverted := by
        simpa [evmSolm, rad] using
          flapperCageBodyRevertsAuth evmSolm rad
            (by simp only [evmSolm, initState]; exact hwv) hauthSolm
      exact (flapperX_cage_auth_revert (g := Sat256.ofUInt256 g)
          hauthEvm hdecode)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_cage_none_short (I := I) hsz4 hshort
    have hrev := flapperX_cage_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
