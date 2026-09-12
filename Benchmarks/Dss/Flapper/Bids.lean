import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_003

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperBidsIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def flapperBidsBaseSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 1) (flapperBidsIdWord I)

def flapperBidsBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperBidsBaseSlot I)

def flapperBidsLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperBidsBaseSlot I + UInt256.ofNat 1)

def flapperBidsPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (flapperBidsBaseSlot I + UInt256.ofNat 2)

def flapperBidsGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flapperBidsPackedWord σ I) flapperAddressMask

abbrev flapperUint48Shift160 : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)

abbrev flapperUint48Shift208 : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208)

@[simp] theorem flapperUint48Shift160_eq_pow :
    flapperUint48Shift160 = UInt256.ofNat (256 ^ 20) := by
  decide

@[simp] theorem flapperUint48Shift208_eq_pow :
    flapperUint48Shift208 = UInt256.ofNat (256 ^ 26) := by
  decide

def flapperBidsTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperBidsPackedWord σ I) flapperUint48Shift160)

def flapperBidsEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (flapperBidsPackedWord σ I) flapperUint48Shift208)
    flapperUint48Mask

def flapperBidsReturnBytes
    (bid lot guy tic endw : UInt256) : ByteArray :=
  bid.toByteArray ++ lot.toByteArray ++ guy.toByteArray ++ tic.toByteArray ++
    endw.toByteArray

def flapperBidsReturnMem
    (mem : ByteArray) (bid lot guy tic endw : UInt256) : ByteArray :=
  endw.toByteArray.write 0
    (tic.toByteArray.write 0
      (guy.toByteArray.write 0
        (lot.toByteArray.write 0
          (bid.toByteArray.write 0 mem 128 32) 160 32)
        192 32)
      224 32)
    256 32

def flapperBidsReturnBlockMem
    (mem : ByteArray) (bid lot guy tic endw : UInt256) : ByteArray :=
  endw.toByteArray.write 0
    (tic.toByteArray.write 0
      (guy.toByteArray.write 0
        (lot.toByteArray.write 0
          (bid.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)
          ((memLoad (UInt256.ofNat 64) mem) + UInt256.ofNat 32).toNat 32)
        (UInt256.ofNat 64 + memLoad (UInt256.ofNat 64) mem).toNat 32)
      ((memLoad (UInt256.ofNat 64) mem) + UInt256.ofNat 96).toNat 32)
    ((memLoad (UInt256.ofNat 64) mem) + UInt256.ofNat 128).toNat 32

theorem flapperAddressMask_clean_right (w : UInt256) :
    UInt256.land (UInt256.land w flapperAddressMask) flapperAddressMask =
      UInt256.land w flapperAddressMask := by
  rw [u256_land_comm w flapperAddressMask]
  rw [flapperAddressMask_clean]
  rw [flapperAddressMask_eq_solcAddrMask]
  rw [u256_land_comm solcAddrMask w]

theorem flapperUint48Mask_clean_left (w : UInt256) :
    UInt256.land flapperUint48Mask (UInt256.land flapperUint48Mask w) =
      UInt256.land flapperUint48Mask w := by
  rw [u256_land_comm flapperUint48Mask (UInt256.land flapperUint48Mask w)]
  rw [flapperUint48Mask_clean w]
  rw [u256_land_comm w flapperUint48Mask]

theorem flapperUint48Mask_clean_right (w : UInt256) :
    UInt256.land flapperUint48Mask (UInt256.land w flapperUint48Mask) =
      UInt256.land w flapperUint48Mask := by
  rw [u256_land_comm w flapperUint48Mask]
  exact flapperUint48Mask_clean_left w

theorem flapperStorageLocLoad_uint48_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            flapperUint48Shift160)
          flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask, flapperUint48Shift160, uint48Int] using
    storageLocLoad_uint_offset evm slot ⟨20, by decide⟩ ⟨6, by decide⟩
      ⟨48, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem flapperStorageLocLoad_uint48_offset26 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨26, by decide⟩ (by decide)) =
      .int (Int.ofNat
        (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            flapperUint48Shift208)
          flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask, flapperUint48Shift208, uint48Int] using
    storageLocLoad_uint_offset evm slot ⟨26, by decide⟩ ⟨6, by decide⟩
      ⟨48, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem flapperBidsHashMem_eq (key : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_1562_memory
        (mem := solcFreePtrMem) (x0 := key) =
      twoWordHashMemSlotFirst key (UInt256.ofNat 1) solcFreePtrMem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_1562_memory,
    twoWordHashMemSlotFirst, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide]

theorem flapperBidsHashMem_size (key : UInt256) :
    (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
        (mem := solcFreePtrMem) (x0 := key)).size = 96 := by
  rw [flapperBidsHashMem_eq]
  unfold twoWordHashMemSlotFirst
  exact wordAt0Mem_size_96 key
    (wordAt32Mem_size_96 (UInt256.ofNat 1) solcFreePtrMem_size)

theorem flapperBidsHashMem_read64 (key : UInt256) :
    (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
        (mem := solcFreePtrMem) (x0 := key)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [flapperBidsHashMem_eq]
  unfold twoWordHashMemSlotFirst wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [wordAt32Mem_size_96 (UInt256.ofNat 1) solcFreePtrMem_size]; omega)
      (by omega)
      (by rw [wordAt32Mem_size_96 (UInt256.ofNat 1) solcFreePtrMem_size])]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)
      (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem flapperBidsHashSlot (key : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
          (mem := solcFreePtrMem) (x0 := key)) =
      solcMappingSlot (UInt256.ofNat 1) key := by
  rw [flapperBidsHashMem_eq]
  unfold keccakWord solcMappingSlot
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 64).toNat = 64 by decide,
    twoWordHashMemSlotFirst_read0_64_any]
  exact mappingSlot_single key (UInt256.ofNat 1)

theorem flapperBidsReturnMem_eq {mem : ByteArray} (hmem : mem.size = 96)
    (bid lot guy tic endw : UInt256) :
    flapperBidsReturnMem mem bid lot guy tic endw =
      (((((mem ++ ffi.ByteArray.zeroes 32) ++ bid.toByteArray) ++
        lot.toByteArray) ++ guy.toByteArray ++ tic.toByteArray) ++
        endw.toByteArray) := by
  unfold flapperBidsReturnMem
  rw [toByteArray_write_eq_unbounded _ _ 128 (by omega)]
  rw [toByteArray_write_eq_unbounded _ _ 160]
  · rw [toByteArray_write_eq_unbounded _ _ 192]
    · rw [toByteArray_write_eq_unbounded _ _ 224]
      · rw [toByteArray_write_eq_unbounded _ _ 256]
        · simp only [hmem, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
            Nat.reduceAdd, Nat.reduceSub]
          rw [show ffi.ByteArray.zeroes 0 = ByteArray.empty by exact zeroes_zero rfl]
          simp
        · simp only [hmem, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
            Nat.reduceAdd, Nat.reduceSub]
          omega
      · simp only [hmem, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
          Nat.reduceAdd, Nat.reduceSub]
        omega
    · simp only [hmem, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
        Nat.reduceAdd, Nat.reduceSub]
      omega
  · simp only [hmem, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
      Nat.reduceAdd, Nat.reduceSub]
    omega

theorem flapperBidsReturnMem_size {mem : ByteArray} (hmem : mem.size = 96)
    (bid lot guy tic endw : UInt256) :
    (flapperBidsReturnMem mem bid lot guy tic endw).size = 288 := by
  calc
    (flapperBidsReturnMem mem bid lot guy tic endw).size =
        (((((mem ++ ffi.ByteArray.zeroes 32) ++ bid.toByteArray) ++
          lot.toByteArray) ++ guy.toByteArray ++ tic.toByteArray) ++
          endw.toByteArray).size := by
      rw [flapperBidsReturnMem_eq (mem := mem) hmem]
    _ = 288 := by
      simp [ByteArray.size_append, ByteArray_zeroes_size, hmem]

theorem flapperBidsReturnMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (bid lot guy tic endw : UInt256) :
    (flapperBidsReturnMem mem bid lot guy tic endw).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [flapperBidsReturnMem_eq hmem]
  rw [show
      (((((mem ++ ffi.ByteArray.zeroes 32) ++ bid.toByteArray) ++ lot.toByteArray) ++
            guy.toByteArray ++ tic.toByteArray) ++ endw.toByteArray) =
        mem ++
          (ffi.ByteArray.zeroes 32 ++ bid.toByteArray ++ lot.toByteArray ++
            guy.toByteArray ++ tic.toByteArray ++ endw.toByteArray) by
    simp [ByteArray.append_assoc]]
  rw [readWithPadding_eq_extract _ 64 (by
    simp [ByteArray.size_append, ByteArray_zeroes_size, hmem])]
  rw [extract_append_left mem
    (ffi.ByteArray.zeroes 32 ++ bid.toByteArray ++ lot.toByteArray ++
      guy.toByteArray ++ tic.toByteArray ++ endw.toByteArray) 64 96
    (by simp [hmem])]
  rw [← readWithPadding_eq_extract mem 64 (by simp [hmem])]
  exact hread64

theorem flapperBidsReturnMem_mload64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (bid lot guy tic endw : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (flapperBidsReturnMem mem bid lot guy tic endw).size
        then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((flapperBidsReturnMem mem bid lot guy tic endw).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [flapperBidsReturnMem_size hmem]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using
        flapperBidsReturnMem_read64 hmem hread64 bid lot guy tic endw)

theorem flapperBidsReturnBlockMem_eq {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (bid lot guy tic endw : UInt256) :
    flapperBidsReturnBlockMem mem bid lot guy tic endw =
      flapperBidsReturnMem mem bid lot guy tic endw := by
  have hml :
      memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 := by
    simpa [memLoad] using
      mloadFreePtrValue (by rw [hmem]; decide) hread64
  simp [flapperBidsReturnBlockMem, flapperBidsReturnMem, hml,
    show (UInt256.ofNat 128).toNat = 128 by decide,
    show (UInt256.ofNat 128 + UInt256.ofNat 32).toNat = 160 by decide,
    show (UInt256.ofNat 64 + UInt256.ofNat 128).toNat = 192 by decide,
    show (UInt256.ofNat 128 + UInt256.ofNat 96).toNat = 224 by decide,
    show (UInt256.ofNat 128 + UInt256.ofNat 128).toNat = 256 by decide]

theorem flapperBidsReturnMem_read {mem : ByteArray} (hmem : mem.size = 96)
    (bid lot guy tic endw : UInt256) :
    (flapperBidsReturnMem mem bid lot guy tic endw).readWithPadding 128 160 =
      flapperBidsReturnBytes bid lot guy tic endw := by
  rw [flapperBidsReturnMem_eq hmem]
  have hassoc :
      (((((mem ++ ffi.ByteArray.zeroes 32) ++ bid.toByteArray) ++ lot.toByteArray) ++
            guy.toByteArray ++ tic.toByteArray) ++ endw.toByteArray) =
        (mem ++ ffi.ByteArray.zeroes 32) ++
          flapperBidsReturnBytes bid lot guy tic endw := by
    rw [flapperBidsReturnBytes]
    simp [ByteArray.append_assoc]
  rw [hassoc]
  rw [readWithPadding_eq_extract' _ 128 160 (by norm_num) (by norm_num)]
  · rw [extract_append_right_window]
    · rw [show 128 - (mem ++ ffi.ByteArray.zeroes 32).size = 0 by
        simp [ByteArray_zeroes_size, hmem]]
      rw [show 128 + 160 - (mem ++ ffi.ByteArray.zeroes 32).size =
          (flapperBidsReturnBytes bid lot guy tic endw).size by
        simp [flapperBidsReturnBytes, ByteArray.size_append, ByteArray_zeroes_size,
          hmem]]
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by rfl)
    · simp [ByteArray_zeroes_size, hmem]
  · simp [ByteArray.size_append, ByteArray_zeroes_size, hmem, flapperBidsReturnBytes]

theorem flapperBidsReturnBlockBytes {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (bid lot guy tic endw : UInt256) :
    (flapperBidsReturnBlockMem mem bid lot guy tic endw).readWithPadding
        (memLoad (UInt256.ofNat 64)
          (flapperBidsReturnBlockMem mem bid lot guy tic endw)).toNat
        (UInt256.ofNat 160 +
          UInt256.sub (memLoad (UInt256.ofNat 64) mem)
            (memLoad (UInt256.ofNat 64)
              (flapperBidsReturnBlockMem mem bid lot guy tic endw))).toNat =
      flapperBidsReturnBytes bid lot guy tic endw := by
  have hml :
      memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 := by
    simpa [memLoad] using
      mloadFreePtrValue (by rw [hmem]; decide) hread64
  have hblock := flapperBidsReturnBlockMem_eq hmem hread64 bid lot guy tic endw
  have hfinal :
      memLoad (UInt256.ofNat 64)
          (flapperBidsReturnMem mem bid lot guy tic endw) =
        UInt256.ofNat 128 := by
    simpa [memLoad] using
      flapperBidsReturnMem_mload64 hmem hread64 bid lot guy tic endw
  rw [hblock, hml, hfinal]
  change (flapperBidsReturnMem mem bid lot guy tic endw).readWithPadding 128 160 =
    flapperBidsReturnBytes bid lot guy tic endw
  exact flapperBidsReturnMem_read hmem bid lot guy tic endw

theorem flapperEncodeValue_uint256 (v : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := u256_ofNat_toNat v
  have hlt : v.toNat < EVM.twoPow 256 := by exact v.val.isLt
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]

theorem flapperEncodeValue_uint48 (v : UInt256) (hv : v.toNat < EVM.twoPow 48) :
    encodeABIValue? uint48 (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := u256_ofNat_toNat v
  simp [uint48, uint48Int, encodeABIValue?, encodeABIWord?, hword, hv]

theorem flapperEncodeValue_addr (v : UInt256) (hv : v.toNat < EVM.addressModulus) :
    encodeABIValue? addr (.address (AccountAddress.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word ↑(AccountAddress.ofNat v.toNat) = v := by
    rw [show (↑(AccountAddress.ofNat v.toNat) : Nat) = v.toNat by
      unfold AccountAddress.ofNat
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hv)]
    exact u256_ofNat_toNat v
  simp [addr, encodeABIValue?, encodeABIWord?, hword]

theorem evalExprs?_five {cfg : Config} {solm : Frame} {evm : EVM.State}
    {e0 e1 e2 e3 e4 : Expr} {v0 v1 v2 v3 v4 : Value}
    (h0 : evalExpr? cfg solm evm e0 = .ok v0)
    (h1 : evalExpr? cfg solm evm e1 = .ok v1)
    (h2 : evalExpr? cfg solm evm e2 = .ok v2)
    (h3 : evalExpr? cfg solm evm e3 = .ok v3)
    (h4 : evalExpr? cfg solm evm e4 = .ok v4) :
    evalExprs? cfg solm evm [e0, e1, e2, e3, e4] =
      .ok [v0, v1, v2, v3, v4] := by
  simp only [evalExprs?, h0, h1, h2, h3, h4, bind, EvalResult.bind, pure]

theorem ABlock.returnsFive {cfg evm solm₀ stmts₀ solm rest}
    {e0 e1 e2 e3 e4 : Expr} {v0 v1 v2 v3 v4 : Value}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.return [e0, e1, e2, e3, e4] :: rest))
    (h0 : evalExpr? cfg solm evm e0 = .ok v0)
    (h1 : evalExpr? cfg solm evm e1 = .ok v1)
    (h2 : evalExpr? cfg solm evm e2 = .ok v2)
    (h3 : evalExpr? cfg solm evm e3 = .ok v3)
    (h4 : evalExpr? cfg solm evm e4 = .ok v4) :
    ExecBlock cfg solm₀ evm stmts₀
      (.returned solm evm (some [v0, v1, v2, v3, v4])) :=
  prev.run (ExecBlock.consReturn (ExecStmt.return (evalExprs?_five h0 h1 h2 h3 h4)))

theorem flapperBidsReturnEncoding
    (bid lot guy tic endw : UInt256)
    (hguy : guy.toNat < EVM.addressModulus)
    (htic : tic.toNat < EVM.twoPow 48)
    (hend : endw.toNat < EVM.twoPow 48) :
    encodeReturnValues? [uint256, uint256, addr, uint48, uint48]
      [.int (Int.ofNat bid.toNat),
        .int (Int.ofNat lot.toNat),
        .address (AccountAddress.ofNat guy.toNat),
        .int (Int.ofNat tic.toNat),
        .int (Int.ofNat endw.toNat)] =
      some (flapperBidsReturnBytes bid lot guy tic endw) := by
  have hencBid := flapperEncodeValue_uint256 bid
  have hencLot := flapperEncodeValue_uint256 lot
  have hencGuy := flapperEncodeValue_addr guy hguy
  have hencTic := flapperEncodeValue_uint48 tic htic
  have hencEnd := flapperEncodeValue_uint48 endw hend
  have hhead :
      abiTupleHeadSize? [uint256, uint256, addr, uint48, uint48] = some 160 := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynUint48 : isDynamicABIType uint48 = false := by native_decide
  rw [flapperBidsReturnBytes, toByteArray_eq_toBytesBE bid,
    toByteArray_eq_toBytesBE lot, toByteArray_eq_toBytesBE guy,
    toByteArray_eq_toBytesBE tic, toByteArray_eq_toBytesBE endw]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hhead, hencBid, hencLot, hencGuy, hencTic, hencEnd, hdynUint, hdynAddr,
    hdynUint48, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append,
    List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem flapperX_bids_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (flapperBidsReturnBytes (flapperBidsBidWord σ I) (flapperBidsLotWord σ I)
        (flapperBidsGuyWord σ I) (flapperBidsTicWord σ I) (flapperBidsEndWord σ I)) := by
  obtain ⟨_, _, rd433⟩ := hreach
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
  have rd455 := flapperRuntimeBlocks.flapperRuntime_block_433_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond (by jump_dest) rd433
  have rd1562 := flapperRuntimeBlocks.flapperRuntime_block_455
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 462, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd455
  have rd1562Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1562)
        (flapperBidsIdWord I :: UInt256.ofNat 462 :: [sel])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [flapperBidsIdWord, calldataWord] using rd1562⟩
  obtain ⟨_, _, rd1562'⟩ := rd1562Ex
  obtain ⟨_, _, rd462raw⟩ := flapperRuntimeBlocks.flapperRuntime_block_1562
    (x0 := flapperBidsIdWord I) (x1 := UInt256.ofNat 462) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd1562'
  have hslot :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((flapperBidsIdWord I).toByteArray.write 0
            ((UInt256.ofNat 1).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 32).toNat 32)
            (UInt256.ofNat 0).toNat 32) =
        flapperBidsBaseSlot I := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_1562_memory,
      flapperBidsBaseSlot] using
      flapperBidsHashSlot (flapperBidsIdWord I)
  have haw :
      M (M (M (UInt256.ofNat 3) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
        (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64) =
        UInt256.ofNat 3 := by
    native_decide
  have rd462Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 462)
        (flapperBidsEndWord σ I :: flapperBidsTicWord σ I ::
          flapperBidsGuyWord σ I :: flapperBidsLotWord σ I ::
          flapperBidsBidWord σ I :: UInt256.ofNat 462 :: [sel])
        (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
          (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_1562_stack,
        flapperRuntimeBlocks.flapperRuntime_block_1562_memory,
        flapperBidsEndWord, flapperBidsTicWord, flapperBidsGuyWord,
        flapperBidsLotWord, flapperBidsBidWord, flapperBidsPackedWord,
        flapperBidsBaseSlot, flapperAddressMask, flapperUint48Mask,
        flapperUint48Shift160, flapperUint48Shift208, hslot, haw] using
        rd462raw⟩
  obtain ⟨_, _, rd462⟩ := rd462Ex
  have hret := flapperRuntimeBlocks.flapperRuntime_block_462
    (x0 := flapperBidsEndWord σ I) (x1 := flapperBidsTicWord σ I)
    (x2 := flapperBidsGuyWord σ I) (x3 := flapperBidsLotWord σ I)
    (x4 := flapperBidsBidWord σ I) (R := [UInt256.ofNat 462, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd462
  have hguyClean :
      UInt256.land (flapperBidsGuyWord σ I) flapperAddressMask =
        flapperBidsGuyWord σ I := by
    simpa [flapperBidsGuyWord] using
      flapperAddressMask_clean_right (flapperBidsPackedWord σ I)
  have hguySolcClean :
      UInt256.land (flapperBidsGuyWord σ I) solcAddrMask =
        flapperBidsGuyWord σ I := by
    simpa [flapperAddressMask_eq_solcAddrMask] using hguyClean
  have hticClean :
      UInt256.land flapperUint48Mask (flapperBidsTicWord σ I) =
        flapperBidsTicWord σ I := by
    simpa [flapperBidsTicWord] using
      flapperUint48Mask_clean_left
        (UInt256.div (flapperBidsPackedWord σ I) flapperUint48Shift160)
  have hendClean :
      UInt256.land flapperUint48Mask (flapperBidsEndWord σ I) =
        flapperBidsEndWord σ I := by
    simpa [flapperBidsEndWord] using
      flapperUint48Mask_clean_right
        (UInt256.div (flapperBidsPackedWord σ I) flapperUint48Shift208)
  have hretBytes := flapperBidsReturnBlockBytes
    (mem := flapperRuntimeBlocks.flapperRuntime_block_1562_memory
      (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I))
    (flapperBidsHashMem_size (flapperBidsIdWord I))
    (flapperBidsHashMem_read64 (flapperBidsIdWord I))
    (flapperBidsBidWord σ I) (flapperBidsLotWord σ I)
    (UInt256.land (flapperBidsGuyWord σ I) flapperAddressMask)
    (UInt256.land flapperUint48Mask (flapperBidsTicWord σ I))
    (UInt256.land flapperUint48Mask (flapperBidsEndWord σ I))
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    ((flapperBidsReturnBlockMem
        (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
          (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I))
        (flapperBidsBidWord σ I) (flapperBidsLotWord σ I)
        (UInt256.land (flapperBidsGuyWord σ I) flapperAddressMask)
        (UInt256.land flapperUint48Mask (flapperBidsTicWord σ I))
        (UInt256.land flapperUint48Mask (flapperBidsEndWord σ I))).readWithPadding
      (memLoad (UInt256.ofNat 64)
        (flapperBidsReturnBlockMem
          (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
            (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I))
          (flapperBidsBidWord σ I) (flapperBidsLotWord σ I)
          (UInt256.land (flapperBidsGuyWord σ I) flapperAddressMask)
          (UInt256.land flapperUint48Mask (flapperBidsTicWord σ I))
          (UInt256.land flapperUint48Mask (flapperBidsEndWord σ I)))).toNat
      (UInt256.ofNat 160 +
        UInt256.sub
          (memLoad (UInt256.ofNat 64)
            (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
              (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I)))
          (memLoad (UInt256.ofNat 64)
            (flapperBidsReturnBlockMem
              (flapperRuntimeBlocks.flapperRuntime_block_1562_memory
                (mem := solcFreePtrMem) (x0 := flapperBidsIdWord I))
              (flapperBidsBidWord σ I) (flapperBidsLotWord σ I)
              (UInt256.land (flapperBidsGuyWord σ I) flapperAddressMask)
              (UInt256.land flapperUint48Mask (flapperBidsTicWord σ I))
              (UInt256.land flapperUint48Mask (flapperBidsEndWord σ I))))).toNat) at hret
  rw [hretBytes] at hret
  simpa [hguyClean, hguySolcClean, hticClean, hendClean] using hret

theorem flapperX_bids_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨433⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd433⟩ := hreach
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
  have rd451 := flapperRuntimeBlocks.flapperRuntime_block_433_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd433
  exact flapperRuntimeBlocks.flapperRuntime_block_451
    (R := flapperRuntimeBlocks.flapperRuntime_block_433_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_433_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd451

theorem flapperDispatch_bids {cd : ByteArray}
    (hsel : ((⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some bidsTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition])
    (post := [cageTransition, dealTransition, denyTransition, fileTransition,
      fillTransition, gemTransition, kickTransition, kicksTransition, lidTransition,
      liveTransition, relyTransition, tauTransition, tendTransition, tickTransition,
      ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl
    rw [flapperBegSelectorBytes, hcd]
    decide
  · rw [flapperBidsSelectorBytes]
    exact hsel

theorem flapperDecode_bids_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "arg0"
        (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiUInt256] I.calldata =
    some ((∅ : Store).insert "arg0"
      (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["arg0"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (start := 0) htake4]
  change decodeCalldata.insertValues ["arg0"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)]
      ∅ =
    some ((∅ : Store).insert "arg0"
      (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem flapperDecode_bids_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiUInt256] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["arg0"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short
    (mode := DecodeMode.legacySolc05) (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flapperBidsBodyReturns (evm : EVM.State) (idWord : UInt256)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "arg0" (.int (Int.ofNat idWord.toNat)))
      bidsTransition.body
      (.returned
        { contract := contract,
          locals := ((∅ : Store).insert "arg0" (.int (Int.ofNat idWord.toNat))) }
        evm
        (some [
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (solcMappingSlot (UInt256.ofNat 1) idWord)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 1)).toNat),
          .address (AccountAddress.ofNat
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
              solcAddrMask).toNat),
          .int (Int.ofNat
            (UInt256.land
              (UInt256.div
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
                flapperUint48Shift160)
              flapperUint48Mask).toNat),
          .int (Int.ofNat
            (UInt256.land
              (UInt256.div
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
                flapperUint48Shift208)
              flapperUint48Mask).toNat)
        ])) := by
  let locals := ((∅ : Store).insert "arg0" (.int (Int.ofNat idWord.toNat)))
  let erBid : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "bid"] }
  let erLot : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "lot"] }
  let erGuy : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "guy"] }
  let erTic : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "tic"] }
  let erEnd : EvaledStorageRef :=
    { base := "bids",
      steps := [.mindex (.int (Int.ofNat idWord.toNat)), .field "end"] }
  have hbase : locals.get? "bids" = none := by
    simp [locals]
  have herBid :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "arg0") "bid") = .ok erBid := by
    simp [locals, erBid, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have herLot :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "arg0") "lot") = .ok erLot := by
    simp [locals, erLot, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have herGuy :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "arg0") "guy") = .ok erGuy := by
    simp [locals, erGuy, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have herTic :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "arg0") "tic") = .ok erTic := by
    simp [locals, erTic, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have herEnd :
      evalStorageRef config { contract := contract, locals := locals } evm
          (bidsF (.var "arg0") "end") = .ok erEnd := by
    simp [locals, erEnd, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      bidsF, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have htyBid : storageTypeAt? contract.storage erBid =
      some (.elem (.int uint256Int)) := by
    simp [erBid, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have htyLot : storageTypeAt? contract.storage erLot =
      some (.elem (.int uint256Int)) := by
    simp [erLot, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint256St, BidStructTy]
  have htyGuy : storageTypeAt? contract.storage erGuy =
      some (.elem .address) := by
    simp [erGuy, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      addrSt, BidStructTy]
  have htyTic : storageTypeAt? contract.storage erTic =
      some (.elem (.int uint48Int)) := by
    simp [erTic, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have htyEnd : storageTypeAt? contract.storage erEnd =
      some (.elem (.int uint48Int)) := by
    simp [erEnd, contract, storageDecls, storageTypeAt?, storageTypeStep?,
      uint48St, BidStructTy]
  have hkey : keyValueToWord (KeyValue.int (↑idWord.toNat : Int)) = idWord := by
    simpa using keyValueToWord_uint256 idWord
  have hlocBid : config.storage.layout erBid =
      fun _ => some (wordLoc (solcMappingSlot (UInt256.ofNat 1) idWord)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erBid,
      bidsBase, mapSlot, solcMappingSlot]
    rw [hkey]
    change wordLoc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray))) =
      wordLoc (solcMappingSlot (UInt256.ofNat 1) idWord)
    rfl
  have hlocLot : config.storage.layout erLot =
      fun _ => some (wordLoc
        (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 1)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erLot,
      bidsBase, mapSlot, solcMappingSlot]
    rw [hkey]
    change wordLoc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 1) =
      wordLoc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 1)
    rfl
  have hlocGuy : config.storage.layout erGuy =
      fun _ => some (addrLoc
        (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erGuy,
      bidsBase, mapSlot, solcMappingSlot]
    rw [hkey]
    change addrLoc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2) =
      addrLoc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
    rfl
  have hlocTic : config.storage.layout erTic =
      fun _ => some (uint48Loc
        (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erTic,
      bidsBase, mapSlot, solcMappingSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨20, by decide⟩ (by decide)
    rfl
  have hlocEnd : config.storage.layout erEnd =
      fun _ => some (uint48Loc
        (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, erEnd,
      bidsBase, mapSlot, solcMappingSlot]
    rw [hkey]
    change uint48Loc
        (uInt256OfByteArray (ffi.KEC
          (idWord.toByteArray ++ (UInt256.ofNat 1).toByteArray)) +
          UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide) =
      uint48Loc (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2)
        ⟨26, by decide⟩ (by decide)
    rfl
  have hEvalBid :
      evalExpr? config { contract := contract, locals := locals } evm
          (.storage (bidsF (.var "arg0") "bid")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (solcMappingSlot (UInt256.ofNat 1) idWord)).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := herBid)
      (hty := htyBid) (hloc := hlocBid), flapperStorageLocLoad_uint256]
  have hEvalLot :
      evalExpr? config { contract := contract, locals := locals } evm
          (.storage (bidsF (.var "arg0") "lot")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 1)).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := herLot)
      (hty := htyLot) (hloc := hlocLot), flapperStorageLocLoad_uint256]
  have hEvalGuy :
      evalExpr? config { contract := contract, locals := locals } evm
          (.storage (bidsF (.var "arg0") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
            solcAddrMask).toNat)) := by
    rw [evalExpr_storage_scalar (t := .address) (hbase := hbase) (her := herGuy)
      (hty := htyGuy) (hloc := hlocGuy), flapperStorageLocLoad_address]
  have hEvalTic :
      evalExpr? config { contract := contract, locals := locals } evm
          (.storage (bidsF (.var "arg0") "tic")) =
        .ok (.int (Int.ofNat
          (UInt256.land
            (UInt256.div
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
              flapperUint48Shift160)
            flapperUint48Mask).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herTic)
      (hty := htyTic) (hloc := hlocTic), flapperStorageLocLoad_uint48_offset20]
  have hEvalEnd :
      evalExpr? config { contract := contract, locals := locals } evm
          (.storage (bidsF (.var "arg0") "end")) =
        .ok (.int (Int.ofNat
          (UInt256.land
            (UInt256.div
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (solcMappingSlot (UInt256.ofNat 1) idWord + UInt256.ofNat 2))
              flapperUint48Shift208)
            flapperUint48Mask).toNat)) := by
    rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hbase) (her := herEnd)
      (hty := htyEnd) (hloc := hlocEnd), flapperStorageLocLoad_uint48_offset26]
  exact ExecFuncBody.execBlockRet <|
    Benchmarks.Dss.Flapper.ABlock.returnsFive
      (ABlock.requireStep ABlock.start (evalCallvalueEq_true h))
      hEvalBid hEvalLot hEvalGuy hEvalTic hEvalEnd

theorem flapperBidsBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 1))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨433⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I (⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ : ByteArray)
    rfl hselLit
  have hd := flapperDispatch_bids (cd := I.calldata) hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_bids_ok (I := I) hsz36
    have hslot0 : storageRead I.codeOwner σ_evm (flapperBidsBaseSlot I) =
        storageRead I.codeOwner σ_solm (flapperBidsBaseSlot I) := by
      rw [storageRead_eq, storageRead_eq]
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner
        (flapperBidsBaseSlot I) ⟨0⟩
    have hslot1 : storageRead I.codeOwner σ_evm
          (flapperBidsBaseSlot I + UInt256.ofNat 1) =
        storageRead I.codeOwner σ_solm
          (flapperBidsBaseSlot I + UInt256.ofNat 1) := by
      rw [storageRead_eq, storageRead_eq]
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner
        (flapperBidsBaseSlot I + UInt256.ofNat 1) ⟨0⟩
    have hslot2 : storageRead I.codeOwner σ_evm
          (flapperBidsBaseSlot I + UInt256.ofNat 2) =
        storageRead I.codeOwner σ_solm
          (flapperBidsBaseSlot I + UInt256.ofNat 2) := by
      rw [storageRead_eq, storageRead_eq]
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner
        (flapperBidsBaseSlot I + UInt256.ofNat 2) ⟨0⟩
    have hbidEq : flapperBidsBidWord σ_solm I = flapperBidsBidWord σ_evm I := by
      simpa [flapperBidsBidWord] using hslot0.symm
    have hlotEq : flapperBidsLotWord σ_solm I = flapperBidsLotWord σ_evm I := by
      simpa [flapperBidsLotWord] using hslot1.symm
    have hpackedEq : flapperBidsPackedWord σ_solm I = flapperBidsPackedWord σ_evm I := by
      simpa [flapperBidsPackedWord] using hslot2.symm
    have hguyEq :
        UInt256.land (flapperBidsPackedWord σ_solm I) solcAddrMask =
          flapperBidsGuyWord σ_evm I := by
      rw [hpackedEq]
      simp [flapperBidsGuyWord, flapperAddressMask_eq_solcAddrMask]
    have hticEq :
        UInt256.land
            (UInt256.div (flapperBidsPackedWord σ_solm I) flapperUint48Shift160)
            flapperUint48Mask =
          flapperBidsTicWord σ_evm I := by
      rw [hpackedEq, flapperBidsTicWord]
      rw [u256_land_comm
        (UInt256.div (flapperBidsPackedWord σ_evm I) flapperUint48Shift160)
        flapperUint48Mask]
    have hendEq : flapperBidsEndWord σ_solm I = flapperBidsEndWord σ_evm I := by
      simp [flapperBidsEndWord, hpackedEq]
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((∅ : Store).insert "arg0"
            (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
          bidsTransition.body
          (.returned
            { contract := contract,
              locals := ((∅ : Store).insert "arg0"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [
              .int (Int.ofNat (flapperBidsBidWord σ_solm I).toNat),
              .int (Int.ofNat (flapperBidsLotWord σ_solm I).toNat),
              .address (AccountAddress.ofNat
                (UInt256.land (flapperBidsPackedWord σ_solm I) solcAddrMask).toNat),
              .int (Int.ofNat
                (UInt256.land
                  (UInt256.div (flapperBidsPackedWord σ_solm I) flapperUint48Shift160)
                  flapperUint48Mask).toNat),
              .int (Int.ofNat (flapperBidsEndWord σ_solm I).toNat)
            ])) := by
      simpa [flapperBidsBidWord, flapperBidsLotWord, flapperBidsPackedWord,
        flapperBidsBaseSlot, flapperBidsIdWord, flapperBidsEndWord, storageRead_eq,
        initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
        flapperBidsBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4)
          (by simp only [initState]; exact hwv)
    have hval :
        some ([
          Value.int (Int.ofNat (flapperBidsBidWord σ_solm I).toNat),
          Value.int (Int.ofNat (flapperBidsLotWord σ_solm I).toNat),
          Value.address (AccountAddress.ofNat
            (UInt256.land (flapperBidsPackedWord σ_solm I) solcAddrMask).toNat),
          Value.int (Int.ofNat
            (UInt256.land
              (UInt256.div (flapperBidsPackedWord σ_solm I) flapperUint48Shift160)
              flapperUint48Mask).toNat),
          Value.int (Int.ofNat (flapperBidsEndWord σ_solm I).toNat)
        ] : List Value) =
        some ([
          Value.int (Int.ofNat (flapperBidsBidWord σ_evm I).toNat),
          Value.int (Int.ofNat (flapperBidsLotWord σ_evm I).toNat),
          Value.address (AccountAddress.ofNat (flapperBidsGuyWord σ_evm I).toNat),
          Value.int (Int.ofNat (flapperBidsTicWord σ_evm I).toNat),
          Value.int (Int.ofNat (flapperBidsEndWord σ_evm I).toNat)
        ] : List Value) := by
      simp [hbidEq, hlotEq, hguyEq, hendEq]
      simpa [flapperUint48Shift160] using congrArg UInt256.toNat hticEq
    have hguyCanon : (flapperBidsGuyWord σ_evm I).toNat < EVM.addressModulus := by
      simpa [flapperBidsGuyWord, flapperAddressMask_eq_solcAddrMask] using
        solcAddrMask_result_canonical (flapperBidsPackedWord σ_evm I)
    have hticCanon : (flapperBidsTicWord σ_evm I).toNat < EVM.twoPow 48 := by
      rw [flapperBidsTicWord]
      rw [u256_land_comm flapperUint48Mask
        (UInt256.div (flapperBidsPackedWord σ_evm I) flapperUint48Shift160)]
      exact flapperUint48Word_lt
        (UInt256.div (flapperBidsPackedWord σ_evm I) flapperUint48Shift160)
    have hendCanon : (flapperBidsEndWord σ_evm I).toNat < EVM.twoPow 48 := by
      simpa [flapperBidsEndWord] using
        flapperUint48Word_lt
          (UInt256.div (flapperBidsPackedWord σ_evm I) flapperUint48Shift208)
    have henc : returnEquiv
        (flapperBidsReturnBytes (flapperBidsBidWord σ_evm I)
          (flapperBidsLotWord σ_evm I) (flapperBidsGuyWord σ_evm I)
          (flapperBidsTicWord σ_evm I) (flapperBidsEndWord σ_evm I))
        (some [
          .int (Int.ofNat (flapperBidsBidWord σ_evm I).toNat),
          .int (Int.ofNat (flapperBidsLotWord σ_evm I).toNat),
          .address (AccountAddress.ofNat (flapperBidsGuyWord σ_evm I).toNat),
          .int (Int.ofNat (flapperBidsTicWord σ_evm I).toNat),
          .int (Int.ofNat (flapperBidsEndWord σ_evm I).toNat)
        ])
        bidsTransition.returnType := by
      refine returnEquiv.returned rfl ?_
      simpa [bidsTransition] using
        flapperBidsReturnEncoding
          (flapperBidsBidWord σ_evm I) (flapperBidsLotWord σ_evm I)
          (flapperBidsGuyWord σ_evm I) (flapperBidsTicWord σ_evm I)
          (flapperBidsEndWord σ_evm I)
          hguyCanon hticCanon hendCanon
    exact (flapperX_bids_ok (g := Sat256.ofUInt256 g) hsize hsz36 hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody hval hAccounts henc
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_bids_none_short (I := I) hsz4 hshort
    have hrev := flapperX_bids_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
