import Benchmarks.Dss.Flapper.CreationBlocks_001
import Benchmarks.Dss.Flapper.File
import Reasoning.SolmBody
import Reasoning.Storage
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option linter.unusedSimpArgs false

private abbrev ctorTail (vat gem : AccountAddress) : ByteArray :=
  ByteArray.mk ((EVM.word vat.val).toBytesBE ++ (EVM.word gem.val).toBytesBE).toArray

private theorem ctorTail_eq (vat gem : AccountAddress) :
    ctorTail vat gem =
      (EVM.word vat.val).toBytesBE.toByteArray ++
        (EVM.word gem.val).toBytesBE.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

private theorem flapperCtorEncodeArgs (vat gem : AccountAddress) :
    ABI.encodeABIValues? [addr, addr] [Value.address vat, Value.address gem] =
      some ((EVM.word vat.val).toBytesBE ++ (EVM.word gem.val).toBytesBE) := by
  simp [ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
    ABI.encodeABIValue?.eq_def, addr, ABI.abiTupleHeadSize?, ABI.isDynamicABIType,
    ABI.staticABIEncodedSize?, ABI.encodeABIWord?]

private theorem flapperCtorDeployment_args_length {args : List Value} {deployed : ByteArray}
    (hdeploy : config.selfDeployment flapperCreationBytecode args = some deployed) :
    args.length = 2 := by
  cases args with
  | nil =>
      simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
        ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
        ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType, ABI.staticABIEncodedSize?] at hdeploy
  | cons a rest =>
      cases rest with
      | nil =>
          simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
            ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
            ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType, ABI.staticABIEncodedSize?] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | nil => rfl
          | cons c rest3 =>
              simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
                ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
                ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType,
                ABI.staticABIEncodedSize?] at hdeploy

private theorem flapperCtorDeployment_shape {args : List Value} {deployed : ByteArray}
    (hdeploy : config.selfDeployment flapperCreationBytecode args = some deployed) :
    ∃ vat gem,
      args = [Value.address vat, Value.address gem] ∧
      deployed = flapperCreationBytecode ++ ctorTail vat gem := by
  cases args with
  | nil =>
      simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
        ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
        ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType, ABI.staticABIEncodedSize?] at hdeploy
  | cons a rest =>
      cases rest with
      | nil =>
          simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
            ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
            ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType, ABI.staticABIEncodedSize?] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | cons c rest3 =>
              simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
                ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
                ABI.abiTupleHeadSize?, addr, ABI.isDynamicABIType,
                ABI.staticABIEncodedSize?] at hdeploy
          | nil =>
              cases a <;> cases b <;>
                simp [config, contract, constructorDecl, genSolidityConstructorDeployment,
                  ABI.encodeABIValues?.eq_def, ABI.encodeABIValuesFrom?.eq_def,
                  ABI.encodeABIValue?.eq_def, ABI.abiTupleHeadSize?, addr,
                  ABI.isDynamicABIType, ABI.staticABIEncodedSize?, ABI.encodeABIWord?] at hdeploy
              case address.address vat gem =>
                refine ⟨vat, gem, rfl, ?_⟩
                rw [← hdeploy, ctorTail_eq]

private theorem flapperCreationRuntimeSlice (tail mem : ByteArray) :
    (((flapperCreationBytecode ++ tail).write (UInt256.ofNat 208).toNat mem
        (UInt256.ofNat 0).toNat (UInt256.ofNat 5008).toNat).readWithPadding
      (UInt256.ofNat 0).toNat (UInt256.ofNat 5008).toNat) = flapperBytecode := by
  rw [show (UInt256.ofNat 208).toNat = 208 by native_decide]
  rw [show (UInt256.ofNat 0).toNat = 0 by native_decide]
  rw [show (UInt256.ofNat 5008).toNat = 5008 by native_decide]
  rw [write0_read_back_from_gen (flapperCreationBytecode ++ tail) mem 208 5008
    (by norm_num)
    (by
      rw [ByteArray.size_append]
      have h : flapperCreationBytecode.size = 5216 := by native_decide
      omega)
    (by norm_num)]
  rw [extract_append_left flapperCreationBytecode tail 208 (208 + 5008)
    (by
      have h : flapperCreationBytecode.size = 5216 := by native_decide
      omega)]
  native_decide

private abbrev ctorLocals (vat gem : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat) |>.insert "gem_" (.address gem)

private abbrev ctorFrame (vat gem : AccountAddress) : Frame :=
  { contract := contract, locals := ctorLocals vat gem }

private abbrev ctorBegWord : UInt256 := UInt256.ofNat 1050000000000000000
private abbrev ctorTtlWordConst : UInt256 := UInt256.ofNat 10800
private abbrev ctorTauWordConst : UInt256 := UInt256.ofNat 172800
private abbrev ctorTauShifted : UInt256 := UInt256.ofNat 48638875975601356800
private abbrev ctorTauMask : UInt256 :=
  UInt256.shiftLeft flapperUint48Mask (UInt256.ofNat 48)

private def ctorTtlStoreWord (evm : EVM.State) : UInt256 :=
  UInt256.lor (UInt256.land ctorTtlWordConst flapperUint48Mask)
    (UInt256.land (UInt256.lnot flapperUint48Mask)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5)))

private def ctorTauStoreWord (evm : EVM.State) : UInt256 :=
  UInt256.lor
    (UInt256.mul (UInt256.land ctorTauWordConst flapperUint48Mask)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
    (UInt256.land (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5)))

private def ctorCombinedSlot5Word (evm : EVM.State) : UInt256 :=
  UInt256.lor ctorTauShifted
    (UInt256.land (UInt256.lnot ctorTauMask)
      (UInt256.lor
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))
          (UInt256.lnot flapperUint48Mask))
        ctorTtlWordConst))

private def ctorAddressStoreWord (old addrWord : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
    (UInt256.land addrWord solcAddrMask)

private def ctorSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

private def ctorWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 0) (ctorSenderWord I)

private def ctorAfterBeg (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 4) ctorBegWord

private def ctorAfterTtl (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5) (ctorTtlStoreWord evm)

private def ctorAfterTau (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 5) (ctorTauStoreWord evm)

private def ctorAfterKicks (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 6) (UInt256.ofNat 0)

private def ctorSourceAfterDefaults (evm : EVM.State) : EVM.State :=
  ctorAfterKicks (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm)))

private def ctorAfterWards (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (ctorWardsSlot evm.executionEnv)
    (UInt256.ofNat 1)

private def ctorAfterVat (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 2)
    (ctorAddressStoreWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))
      (UInt256.ofNat vat.val))

private def ctorAfterGem (evm : EVM.State) (gem : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 3)
    (ctorAddressStoreWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 3))
      (UInt256.ofNat gem.val))

private def ctorAfterLive (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (UInt256.ofNat 7) (UInt256.ofNat 1)

private def ctorSourceFinalEVM (evm : EVM.State) (vat gem : AccountAddress) : EVM.State :=
  ctorAfterLive (ctorAfterGem
    (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evm)) vat) gem)

private theorem ctorSourceFinal_createdAccounts (evm : EVM.State)
    (vat gem : AccountAddress) :
    (ctorSourceFinalEVM evm vat gem).createdAccounts = evm.createdAccounts := by
  simp [ctorSourceFinalEVM, ctorSourceAfterDefaults, ctorAfterLive, ctorAfterGem, ctorAfterVat,
    ctorAfterWards, ctorAfterKicks, ctorAfterTau, ctorAfterTtl, ctorAfterBeg,
    storageStore_createdAccounts]

private abbrev ctorCreationFreePtrMem : ByteArray :=
  flapperCreationBlocks.flapperCreation_block_0_taken_memory (mem := ByteArray.empty)

private abbrev ctorCreationArgBase : UInt256 :=
  memLoad (UInt256.ofNat 64) ctorCreationFreePtrMem

private def ctorCreationArgLength (vat gem : AccountAddress) : UInt256 :=
  UInt256.sub (UInt256.ofNat (flapperCreationBytecode ++ ctorTail vat gem).size)
    (UInt256.ofNat 5216)

private def ctorCreationSlot5Word (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  UInt256.lor ctorTauShifted
    (UInt256.land (UInt256.lnot ctorTauMask)
      (UInt256.lor
        (UInt256.land
          (storageRead I.codeOwner
            (storageWrite I.codeOwner σ (UInt256.ofNat 4) ctorBegWord)
            (UInt256.ofNat 5))
          (UInt256.lnot flapperUint48Mask))
        ctorTtlWordConst))

private def ctorCreationAfterDefaults (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  storageWrite I.codeOwner
    (storageWrite I.codeOwner
      (storageWrite I.codeOwner σ (UInt256.ofNat 4) ctorBegWord)
      (UInt256.ofNat 5) (ctorCreationSlot5Word I σ))
    (UInt256.ofNat 6) (UInt256.ofNat 0)

private def ctorCreationArgsMem (vat gem : AccountAddress) : ByteArray :=
  flapperCreationBlocks.flapperCreation_block_77_taken_memory
    (tail := ctorTail vat gem) (mem := ctorCreationFreePtrMem)

private def ctorCreationWardsSlot (I : ExecutionEnv) (vat gem : AccountAddress) : UInt256 :=
  keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
    ((UInt256.ofNat 0).toByteArray.write 0
      ((UInt256.ofNat I.source.val).toByteArray.write 0
        (ctorCreationArgsMem vat gem) (UInt256.ofNat 0).toNat 32)
      (UInt256.ofNat 32).toNat 32)

private def ctorCreationAfterWards (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) : AccountMap :=
  storageWrite I.codeOwner (ctorCreationAfterDefaults I σ)
    (ctorCreationWardsSlot I vat gem) (UInt256.ofNat 1)

private def ctorCreationVatWord (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.lnot solcAddrMask)
      (storageRead I.codeOwner (ctorCreationAfterWards I σ vat gem) (UInt256.ofNat 2)))
    (UInt256.land solcAddrMask
      (memLoad ctorCreationArgBase (ctorCreationArgsMem vat gem)))

private def ctorCreationAfterVat (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) : AccountMap :=
  storageWrite I.codeOwner (ctorCreationAfterWards I σ vat gem) (UInt256.ofNat 2)
    (ctorCreationVatWord I σ vat gem)

private def ctorCreationGemWord (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) : UInt256 :=
  ctorAddressStoreWord
    (storageRead I.codeOwner (ctorCreationAfterVat I σ vat gem) (UInt256.ofNat 3))
    (memLoad ((UInt256.ofNat 32) + ctorCreationArgBase) (ctorCreationArgsMem vat gem))

private def ctorCreationFinalMap (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) : AccountMap :=
  storageWrite I.codeOwner
    (storageWrite I.codeOwner (ctorCreationAfterVat I σ vat gem) (UInt256.ofNat 3)
      (ctorCreationGemWord I σ vat gem))
    (UInt256.ofNat 7) (UInt256.ofNat 1)

private theorem byteArray_write_from_eq_unbounded (src base : ByteArray)
    (srcAddr off len : ℕ) (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hoff : base.size ≤ off) :
    src.write srcAddr base off len =
      base ++ ffi.ByteArray.zeroes (off - base.size) ++ src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hbaseSize : base.data.size = base.size := rfl
  have hzeroSize :
      (ffi.ByteArray.zeroes (off - base.size)).data.size = off - base.size := by
    rw [show (ffi.ByteArray.zeroes (off - base.size)).data.size =
      (ffi.ByteArray.zeroes (off - base.size)).size from rfl, ByteArray_zeroes_size]
  have hprefixSize : (base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data).size = off := by
    rw [Array.size_append, hbaseSize, hzeroSize]
    omega
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  rw [show min len (src.size - srcAddr) = len by omega]
  rw [show min base.size (off + len) - (off + len) = 0 by omega]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rw [hprefixSize])]
  rw [show off + min len ((src.data).size - srcAddr) = off + len by
    have : src.data.size = src.size := rfl
    omega]
  have hsuf :
      (base.data ++ (ffi.ByteArray.zeroes (off - base.size)).data).extract (off + len) =
        #[] := by
    apply Array.extract_eq_empty_of_le
    rw [hprefixSize]
    omega
  rw [hsuf]
  simp [Array.append_assoc]

private theorem ctorCreationFreePtrMem_eq :
    ctorCreationFreePtrMem = solcFreePtrMem := by
  rfl

private theorem ctorCreationArgBase_eq :
    ctorCreationArgBase = UInt256.ofNat 128 := by
  change memLoad (UInt256.ofNat 64) ctorCreationFreePtrMem = UInt256.ofNat 128
  rw [ctorCreationFreePtrMem_eq]
  simpa [memLoad] using solcFreePtrMem_mload64

private theorem ctorTail_size (vat gem : AccountAddress) :
    (ctorTail vat gem).size = 64 := by
  rw [ctorTail_eq, ByteArray.size_append,
    word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

private theorem ctorCreationArgLength_eq (vat gem : AccountAddress) :
    ctorCreationArgLength vat gem = UInt256.ofNat 64 := by
  rw [ctorCreationArgLength, ByteArray.size_append]
  have hcreation : flapperCreationBytecode.size = 5216 := by native_decide
  rw [hcreation, ctorTail_size]
  native_decide

private theorem ctorTail_extractVat (vat gem : AccountAddress) :
    (ctorTail vat gem).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat vat.val) := by
  rw [ctorTail_eq]
  rw [extract_append_left _ _ 0 32 (by rw [word_toBytesBE_toByteArray_size])]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rw [show EVM.word vat.val = UInt256.ofNat vat.val by rfl]
  exact toByteArray_extract_all _

private theorem ctorTail_extractGem (vat gem : AccountAddress) :
    (ctorTail vat gem).extract 32 64 =
      UInt256.toByteArray (UInt256.ofNat gem.val) := by
  rw [ctorTail_eq]
  rw [extract_append_right_window _ _ 32 64 (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 - (EVM.word vat.val).toBytesBE.toByteArray.size = 0 by
    rw [word_toBytesBE_toByteArray_size]]
  rw [show 64 - (EVM.word vat.val).toBytesBE.toByteArray.size = 32 by
    rw [word_toBytesBE_toByteArray_size]]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rw [show EVM.word gem.val = UInt256.ofNat gem.val by rfl]
  exact toByteArray_extract_all _

private theorem ctorCreationCodecopyMem_eq (vat gem : AccountAddress) :
    (flapperCreationBytecode ++ ctorTail vat gem).write 5216 ctorCreationFreePtrMem 128 64 =
      ctorCreationFreePtrMem ++ ffi.ByteArray.zeroes 32 ++ ctorTail vat gem := by
  rw [byteArray_write_from_eq_unbounded
    (flapperCreationBytecode ++ ctorTail vat gem) ctorCreationFreePtrMem 5216 128 64
    (by norm_num)
    (by
      rw [ByteArray.size_append]
      have hcreation : flapperCreationBytecode.size = 5216 := by native_decide
      rw [hcreation, ctorTail_size])
    (by
      rw [ctorCreationFreePtrMem_eq, solcFreePtrMem_size]
      norm_num)]
  rw [ctorCreationFreePtrMem_eq, solcFreePtrMem_size]
  rw [show 128 - 96 = 32 by norm_num]
  have hslice :
      (flapperCreationBytecode ++ ctorTail vat gem).extract 5216 (5216 + 64) =
        ctorTail vat gem := by
    rw [show 5216 = flapperCreationBytecode.size by native_decide]
    rw [show 64 = (ctorTail vat gem).size by rw [ctorTail_size]]
    exact extract_append_right flapperCreationBytecode (ctorTail vat gem)
  rw [hslice]

private theorem ctorCreationCodecopyMem_size (vat gem : AccountAddress) :
    ((flapperCreationBytecode ++ ctorTail vat gem).write 5216 ctorCreationFreePtrMem 128 64).size =
      192 := by
  rw [ctorCreationCodecopyMem_eq, ByteArray.size_append, ByteArray.size_append,
    ctorCreationFreePtrMem_eq, solcFreePtrMem_size, ByteArray_zeroes_size, ctorTail_size]

private theorem ctorCreationArgsMem_size (vat gem : AccountAddress) :
    (ctorCreationArgsMem vat gem).size = 192 := by
  unfold ctorCreationArgsMem flapperCreationBlocks.flapperCreation_block_77_taken_memory
  change (((ctorCreationArgLength vat gem + ctorCreationArgBase).toByteArray.write 0
    ((flapperCreationBytecode ++ ctorTail vat gem).write (UInt256.ofNat 5216).toNat
      ctorCreationFreePtrMem ctorCreationArgBase.toNat (ctorCreationArgLength vat gem).toNat)
    (UInt256.ofNat 64).toNat 32).size = 192)
  rw [ctorCreationArgLength_eq, ctorCreationArgBase_eq]
  rw [show UInt256.ofNat 64 + UInt256.ofNat 128 = UInt256.ofNat 192 by native_decide]
  exact toByteArray_write32_size_of_le
    ((flapperCreationBytecode ++ ctorTail vat gem).write 5216 ctorCreationFreePtrMem 128 64)
    (UInt256.ofNat 192) 64 192 192
    (ctorCreationCodecopyMem_size vat gem)
    (by rw [ctorCreationCodecopyMem_size]; norm_num)
    (by norm_num)

private theorem ctorCreationArgsMem_readVat (vat gem : AccountAddress) :
    (ctorCreationArgsMem vat gem).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat vat.val) := by
  unfold ctorCreationArgsMem flapperCreationBlocks.flapperCreation_block_77_taken_memory
  change (((ctorCreationArgLength vat gem + ctorCreationArgBase).toByteArray.write 0
    ((flapperCreationBytecode ++ ctorTail vat gem).write (UInt256.ofNat 5216).toNat
      ctorCreationFreePtrMem ctorCreationArgBase.toNat (ctorCreationArgLength vat gem).toNat)
    (UInt256.ofNat 64).toNat 32).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat vat.val))
  rw [ctorCreationArgLength_eq, ctorCreationArgBase_eq]
  rw [show UInt256.ofNat 64 + UInt256.ofNat 128 = UInt256.ofNat 192 by native_decide]
  rw [show (UInt256.ofNat 5216).toNat = 5216 by native_decide,
    show (UInt256.ofNat 128).toNat = 128 by native_decide,
    show (UInt256.ofNat 64).toNat = 64 by native_decide]
  rw [write32_read_above
    (UInt256.toByteArray (UInt256.ofNat 192))
    ((flapperCreationBytecode ++ ctorTail vat gem).write 5216 ctorCreationFreePtrMem 128 64)
    64 128
    (by rw [toByteArray_size])
    (by rw [ctorCreationCodecopyMem_size]; norm_num)
    (by norm_num)
    (by rw [ctorCreationCodecopyMem_size]; norm_num)]
  rw [ctorCreationCodecopyMem_eq]
  have hprefixSize : (ctorCreationFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, ctorCreationFreePtrMem_eq, solcFreePtrMem_size,
      ByteArray_zeroes_size]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, hprefixSize, ctorTail_size]
    norm_num)]
  rw [extract_append_right_window
    (ctorCreationFreePtrMem ++ ffi.ByteArray.zeroes 32) (ctorTail vat gem) 128 160
    (by rw [hprefixSize])]
  rw [hprefixSize]
  rw [show 128 - 128 = 0 by norm_num, show 160 - 128 = 32 by norm_num]
  rw [ctorTail_extractVat]

private theorem ctorCreationArgsMem_readGem (vat gem : AccountAddress) :
    (ctorCreationArgsMem vat gem).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.ofNat gem.val) := by
  unfold ctorCreationArgsMem flapperCreationBlocks.flapperCreation_block_77_taken_memory
  change (((ctorCreationArgLength vat gem + ctorCreationArgBase).toByteArray.write 0
    ((flapperCreationBytecode ++ ctorTail vat gem).write (UInt256.ofNat 5216).toNat
      ctorCreationFreePtrMem ctorCreationArgBase.toNat (ctorCreationArgLength vat gem).toNat)
    (UInt256.ofNat 64).toNat 32).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.ofNat gem.val))
  rw [ctorCreationArgLength_eq, ctorCreationArgBase_eq]
  rw [show UInt256.ofNat 64 + UInt256.ofNat 128 = UInt256.ofNat 192 by native_decide]
  rw [show (UInt256.ofNat 5216).toNat = 5216 by native_decide,
    show (UInt256.ofNat 128).toNat = 128 by native_decide,
    show (UInt256.ofNat 64).toNat = 64 by native_decide]
  rw [write32_read_above
    (UInt256.toByteArray (UInt256.ofNat 192))
    ((flapperCreationBytecode ++ ctorTail vat gem).write 5216 ctorCreationFreePtrMem 128 64)
    64 160
    (by rw [toByteArray_size])
    (by rw [ctorCreationCodecopyMem_size]; norm_num)
    (by norm_num)
    (by rw [ctorCreationCodecopyMem_size])]
  rw [ctorCreationCodecopyMem_eq]
  have hprefixSize : (ctorCreationFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, ctorCreationFreePtrMem_eq, solcFreePtrMem_size,
      ByteArray_zeroes_size]
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, hprefixSize, ctorTail_size])]
  rw [extract_append_right_window
    (ctorCreationFreePtrMem ++ ffi.ByteArray.zeroes 32) (ctorTail vat gem) 160 192
    (by rw [hprefixSize]; norm_num)]
  rw [hprefixSize]
  rw [show 160 - 128 = 32 by norm_num, show 192 - 128 = 64 by norm_num]
  rw [ctorTail_extractGem]

private theorem ctorCreationArgsMem_mloadVat (vat gem : AccountAddress) :
    memLoad ctorCreationArgBase (ctorCreationArgsMem vat gem) =
      UInt256.ofNat vat.val := by
  rw [ctorCreationArgBase_eq]
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 by native_decide]
  rw [if_neg (by rw [ctorCreationArgsMem_size]; norm_num)]
  rw [ctorCreationArgsMem_readVat, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

private theorem ctorCreationArgsMem_mloadGem (vat gem : AccountAddress) :
    memLoad ((UInt256.ofNat 32) + ctorCreationArgBase) (ctorCreationArgsMem vat gem) =
      UInt256.ofNat gem.val := by
  rw [ctorCreationArgBase_eq]
  rw [show UInt256.ofNat 32 + UInt256.ofNat 128 = UInt256.ofNat 160 by native_decide]
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 by native_decide]
  rw [if_neg (by rw [ctorCreationArgsMem_size]; norm_num)]
  rw [ctorCreationArgsMem_readGem, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

private theorem ctorCreationWardsSlot_eq (I : ExecutionEnv) (vat gem : AccountAddress) :
    ctorCreationWardsSlot I vat gem = ctorWardsSlot I := by
  unfold ctorCreationWardsSlot ctorWardsSlot ctorSenderWord
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat I.source.val) (UInt256.ofNat 0)
        (ctorCreationArgsMem vat gem)) =
    solcMappingSlot (UInt256.ofNat 0) (UInt256.ofNat I.source.val)
  exact twoWordHashMem_keccak_solcMappingSlot_ofNat
    (UInt256.ofNat I.source.val) (UInt256.ofNat 0) (ctorCreationArgsMem vat gem)

private theorem ctorCreationAfterDefaults_missing (I : ExecutionEnv) (σ : AccountMap)
    (_vat _gem : AccountAddress) (hmissing : σ.find? I.codeOwner = none) :
    ctorCreationAfterDefaults I σ = σ := by
  unfold ctorCreationAfterDefaults
  rw [storageWrite_of_missing hmissing]
  rw [storageWrite_of_missing hmissing]
  rw [storageWrite_of_missing hmissing]

private theorem ctorCreationAfterWards_missing (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) (hmissing : σ.find? I.codeOwner = none) :
    ctorCreationAfterWards I σ vat gem = σ := by
  unfold ctorCreationAfterWards
  rw [ctorCreationAfterDefaults_missing I σ vat gem hmissing]
  rw [storageWrite_of_missing hmissing]

private theorem ctorCreationAfterVat_missing (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) (hmissing : σ.find? I.codeOwner = none) :
    ctorCreationAfterVat I σ vat gem = σ := by
  unfold ctorCreationAfterVat
  rw [ctorCreationAfterWards_missing I σ vat gem hmissing]
  rw [storageWrite_of_missing hmissing]

private theorem ctorCreationFinalMap_missing (I : ExecutionEnv) (σ : AccountMap)
    (vat gem : AccountAddress) (hmissing : σ.find? I.codeOwner = none) :
    ctorCreationFinalMap I σ vat gem = σ := by
  unfold ctorCreationFinalMap
  rw [ctorCreationAfterVat_missing I σ vat gem hmissing]
  rw [storageWrite_of_missing hmissing]
  rw [storageWrite_of_missing hmissing]

private theorem ctorSourceFinal_accountMap_missing (evm : EVM.State)
    (vat gem : AccountAddress)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    (ctorSourceFinalEVM evm vat gem).accountMap = evm.accountMap := by
  simp [ctorSourceFinalEVM, ctorSourceAfterDefaults, ctorAfterLive, ctorAfterGem, ctorAfterVat,
    ctorAfterWards, ctorAfterKicks, ctorAfterTau, ctorAfterTtl, ctorAfterBeg,
    Solm.EVM.storageStore, State.lookupAccount, hmissing, Option.option]

private theorem storageLoad_eq_storageRead (evm : EVM.State) (addr : AccountAddress)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm addr slot = storageRead addr evm.accountMap slot := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, storageRead_eq]

private theorem ctorCombinedSlot5Word_eq_tau_after_ttl_word (old : UInt256) :
    UInt256.lor ctorTauShifted
        (UInt256.land (UInt256.lnot ctorTauMask)
          (UInt256.lor (UInt256.land old (UInt256.lnot flapperUint48Mask))
            ctorTtlWordConst)) =
      UInt256.lor
        (UInt256.mul (UInt256.land ctorTauWordConst flapperUint48Mask)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)))
        (UInt256.land (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680))
          (UInt256.lor (UInt256.land ctorTtlWordConst flapperUint48Mask)
            (UInt256.land (UInt256.lnot flapperUint48Mask) old))) := by
  have htau :
      ctorTauShifted =
        UInt256.mul (UInt256.land ctorTauWordConst flapperUint48Mask)
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48)) := by
    native_decide
  have hmask : ctorTauMask = UInt256.ofNat 79228162514264056118567239680 := by
    native_decide
  have httl : UInt256.land ctorTtlWordConst flapperUint48Mask = ctorTtlWordConst := by
    native_decide
  rw [htau, hmask, httl]
  rw [u256_land_comm old (UInt256.lnot flapperUint48Mask)]
  rw [u256_lor_comm (UInt256.land (UInt256.lnot flapperUint48Mask) old)
    ctorTtlWordConst]

private theorem ctorCreationSlot5Word_eq_ctorTau_present (evm : EVM.State)
    {account : Account}
    (hpresent : evm.accountMap.find? evm.executionEnv.codeOwner = some account) :
    ctorCreationSlot5Word evm.executionEnv evm.accountMap =
      ctorTauStoreWord (ctorAfterTtl (ctorAfterBeg evm)) := by
  have hread :
      storageRead evm.executionEnv.codeOwner
          (storageWrite evm.executionEnv.codeOwner evm.accountMap
            (UInt256.ofNat 4) ctorBegWord)
          (UInt256.ofNat 5) =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5) := by
    rw [storageRead_storageWrite_ne]
    · exact (storageLoad_eq_storageRead evm evm.executionEnv.codeOwner
        (UInt256.ofNat 5)).symm
    · native_decide
  have hloadTtl :
      Solm.EVM.storageLoad (ctorAfterBeg evm)
          (ctorAfterBeg evm).executionEnv.codeOwner (UInt256.ofNat 5) =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5) := by
    unfold ctorAfterBeg
    rw [storageStore_executionEnv]
    exact storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
      (by native_decide : UInt256.ofNat 5 ≠ UInt256.ofNat 4)
  have hbegPresent :
      ∃ accountBeg,
        (ctorAfterBeg evm).accountMap.find? (ctorAfterBeg evm).executionEnv.codeOwner =
          some accountBeg := by
    unfold ctorAfterBeg
    simp [Solm.EVM.storageStore, State.lookupAccount, hpresent, Option.option,
      State.setAccount, Account.updateStorage, accountMap_find_insert_self]
  obtain ⟨accountBeg, hbegPresent⟩ := hbegPresent
  have hloadTau :
      Solm.EVM.storageLoad (ctorAfterTtl (ctorAfterBeg evm))
          (ctorAfterTtl (ctorAfterBeg evm)).executionEnv.codeOwner (UInt256.ofNat 5) =
        ctorTtlStoreWord (ctorAfterBeg evm) := by
    unfold ctorAfterTtl
    rw [storageStore_executionEnv]
    exact storageLoad_storageStore_same_present (ctorAfterBeg evm)
      (ctorAfterBeg evm).executionEnv.codeOwner hbegPresent (UInt256.ofNat 5)
      (ctorTtlStoreWord (ctorAfterBeg evm))
  unfold ctorCreationSlot5Word ctorTauStoreWord
  rw [hread, hloadTau]
  unfold ctorTtlStoreWord
  rw [hloadTtl]
  exact ctorCombinedSlot5Word_eq_tau_after_ttl_word
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 5))

private theorem ctorSourceAfterDefaults_stateEquiv {evm₁ evm₂ : EVM.State}
    (h : EVMStateEquiv evm₁ evm₂) :
    EVMStateEquiv (ctorSourceAfterDefaults evm₁) (ctorSourceAfterDefaults evm₂) := by
  have hbeg : EVMStateEquiv (ctorAfterBeg evm₁) (ctorAfterBeg evm₂) := by
    simpa [ctorAfterBeg] using h.storageStore_codeOwner (UInt256.ofNat 4) rfl
  have httlVal : ctorTtlStoreWord (ctorAfterBeg evm₁) =
      ctorTtlStoreWord (ctorAfterBeg evm₂) := by
    unfold ctorTtlStoreWord
    rw [hbeg.storageLoad_codeOwner]
  have httl : EVMStateEquiv
      (ctorAfterTtl (ctorAfterBeg evm₁)) (ctorAfterTtl (ctorAfterBeg evm₂)) := by
    simpa [ctorAfterTtl] using hbeg.storageStore_codeOwner (UInt256.ofNat 5) httlVal
  have htauVal : ctorTauStoreWord (ctorAfterTtl (ctorAfterBeg evm₁)) =
      ctorTauStoreWord (ctorAfterTtl (ctorAfterBeg evm₂)) := by
    unfold ctorTauStoreWord
    rw [httl.storageLoad_codeOwner]
  have htau : EVMStateEquiv
      (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm₁)))
      (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm₂))) := by
    simpa [ctorAfterTau] using httl.storageStore_codeOwner (UInt256.ofNat 5) htauVal
  simpa [ctorSourceAfterDefaults, ctorAfterKicks] using
    htau.storageStore_codeOwner (UInt256.ofNat 6) rfl

private theorem ctorCreationAfterDefaults_sourceEquiv_same_present (evm : EVM.State)
    {account : Account}
    (hpresent : evm.accountMap.find? evm.executionEnv.codeOwner = some account) :
    accountMapEquiv
      (ctorCreationAfterDefaults evm.executionEnv evm.accountMap)
      (ctorSourceAfterDefaults evm).accountMap := by
  have hslot5 := ctorCreationSlot5Word_eq_ctorTau_present evm hpresent
  have hslot5Equiv :
      accountMapEquiv
        (sstoreAccountMap evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
            (UInt256.ofNat 4) ctorBegWord)
          (UInt256.ofNat 5) (ctorCreationSlot5Word evm.executionEnv evm.accountMap))
        (sstoreAccountMap evm.executionEnv.codeOwner
          (sstoreAccountMap evm.executionEnv.codeOwner
            (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
              (UInt256.ofNat 4) ctorBegWord)
            (UInt256.ofNat 5) (ctorTtlStoreWord (ctorAfterBeg evm)))
          (UInt256.ofNat 5) (ctorCreationSlot5Word evm.executionEnv evm.accountMap)) :=
    accountMapEquiv_sstoreAccountMap_self_update
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
        (UInt256.ofNat 4) ctorBegWord)
      evm.executionEnv.codeOwner (UInt256.ofNat 5) (ctorTtlStoreWord (ctorAfterBeg evm))
      (ctorCreationSlot5Word evm.executionEnv evm.accountMap)
  have hkicksEquiv :=
    accountMapEquiv_sstoreAccountMap evm.executionEnv.codeOwner (UInt256.ofNat 6)
      (UInt256.ofNat 0) hslot5Equiv
  simpa [ctorCreationAfterDefaults, ctorSourceAfterDefaults, ctorAfterKicks, ctorAfterTau,
    ctorAfterTtl, ctorAfterBeg, storageWrite_eq, storageStore_accountMap,
    storageStore_executionEnv, hslot5] using hkicksEquiv

private theorem ctorAddrLocStore (evm : EVM.State) (slot : UInt256) (addr : AccountAddress) :
    storageLocStore evm (addrLoc slot) (.address addr) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (ctorAddressStoreWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat addr.val))) := by
  have hword : (UInt256.ofNat addr.val).toNat = addr.val := by
    have hlt : addr.val < UInt256.size := lt_of_lt_of_le addr.isLt (by decide)
    simpa using ulit_toNat' addr.val hlt
  have hcanon : (UInt256.ofNat addr.val).toNat < EVM.addressModulus := by
    rw [hword]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using addr.isLt
  have haddrEq : AccountAddress.ofNat (UInt256.ofNat addr.val).toNat = addr := by
    apply Fin.ext
    simp [AccountAddress.ofNat, hword]
  have hstore := storageLocStore_address_offset0 evm slot (UInt256.ofNat addr.val) hcanon
  have hloc : addrLoc slot = addressOffset0Loc slot := by
    unfold addrLoc addressOffset0Loc
    congr
  rw [hloc]
  simpa [ctorAddressStoreWord, setAddressOffset0Word, haddrEq] using hstore

private theorem ctorAssignBeg (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage begRef (.int defaultBeg) =
      .ok (ctorFrame vat gem, ctorAfterBeg evm) := by
  let er : EvaledStorageRef := { base := "beg", steps := [] }
  have hbase : (ctorLocals vat gem).get? "beg" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm begRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, begRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨4⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨4⟩ : UInt256)) (.int defaultBeg) =
        some (ctorAfterBeg evm) := by
    simpa [ctorAfterBeg, wordLoc, uint256Loc, defaultBeg,
      show (⟨4⟩ : UInt256) = UInt256.ofNat 4 by decide] using
      storageLocStore_uint256 evm (⟨4⟩ : UInt256) ctorBegWord
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem ctorAssignTtl (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage ttlRef (.int defaultTtl) =
      .ok (ctorFrame vat gem, ctorAfterTtl evm) := by
  let er : EvaledStorageRef := { base := "ttl", steps := [] }
  have hbase : (ctorLocals vat gem).get? "ttl" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm ttlRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, ttlRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint48St]
  have hloc : config.storage.layout er =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨0, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (uint48Loc (⟨5⟩ : UInt256) ⟨0, by decide⟩ (by decide))
          (.int defaultTtl) =
        some (ctorAfterTtl evm) := by
    simpa [ctorAfterTtl, ctorTtlStoreWord, defaultTtl, ctorTtlWordConst,
      show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide,
      show UInt256.land (UInt256.ofNat 10800) flapperUint48Mask = UInt256.ofNat 10800 by
        native_decide] using
      flapperStorageLocStore_uint48_offset0 evm (⟨5⟩ : UInt256) (UInt256.ofNat 10800)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem ctorAssignTau (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage tauRef (.int defaultTau) =
      .ok (ctorFrame vat gem, ctorAfterTau evm) := by
  let er : EvaledStorageRef := { base := "tau", steps := [] }
  have hbase : (ctorLocals vat gem).get? "tau" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm tauRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint48St]
  have hloc : config.storage.layout er =
      fun _ => some (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (uint48Loc (⟨5⟩ : UInt256) ⟨6, by decide⟩ (by decide))
          (.int defaultTau) =
        some (ctorAfterTau evm) := by
    simpa [ctorAfterTau, ctorTauStoreWord, defaultTau, ctorTauWordConst,
      show (⟨5⟩ : UInt256) = UInt256.ofNat 5 by decide,
      show UInt256.land (UInt256.ofNat 172800) flapperUint48Mask = UInt256.ofNat 172800 by
        native_decide] using
      flapperStorageLocStore_uint48_offset6 evm (⟨5⟩ : UInt256) (UInt256.ofNat 172800)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint48Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem ctorAssignKicks (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage kicksRef (.int 0) =
      .ok (ctorFrame vat gem, ctorAfterKicks evm) := by
  let er : EvaledStorageRef := { base := "kicks", steps := [] }
  have hbase : (ctorLocals vat gem).get? "kicks" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm kicksRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, kicksRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨6⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨6⟩ : UInt256)) (.int 0) =
        some (ctorAfterKicks evm) := by
    simpa [ctorAfterKicks, wordLoc, uint256Loc,
      show (⟨6⟩ : UInt256) = UInt256.ofNat 6 by decide] using
      storageLocStore_uint256 evm (⟨6⟩ : UInt256) (UInt256.ofNat 0)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem ctorAssignWards (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage (wardsRef sender) (.int 1) =
      .ok (ctorFrame vat gem, ctorAfterWards evm) := by
  let er : EvaledStorageRef :=
    { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] }
  have hbase : (ctorLocals vat gem).get? "wards" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm (wardsRef sender) = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      wardsRef, sender, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (ctorWardsSlot evm.executionEnv)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er, wardsSlot,
      ctorWardsSlot, ctorSenderWord, mapSlot, solcMappingSlot, keyValueToWord_address]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (ctorWardsSlot evm.executionEnv)) (.int 1) =
        some (ctorAfterWards evm) := by
    simpa [ctorAfterWards, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm (ctorWardsSlot evm.executionEnv) (UInt256.ofNat 1)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem ctorAssignVat (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage vatRef (.address vat) =
      .ok (ctorFrame vat gem, ctorAfterVat evm vat) := by
  let er : EvaledStorageRef := { base := "vat", steps := [] }
  have hbase : (ctorLocals vat gem).get? "vat" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm vatRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    simp [er, contract, storageDecls, storageTypeAt?, addrSt]
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨2⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (addrLoc (⟨2⟩ : UInt256)) (.address vat) =
        some (ctorAfterVat evm vat) := by
    simpa [ctorAfterVat, show (⟨2⟩ : UInt256) = UInt256.ofNat 2 by decide] using
      ctorAddrLocStore evm (⟨2⟩ : UInt256) vat
  exact assignStorageRef_storage_scalar_value (ty := .elem .address)
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hscalar := by trivial)
    (hstore := hstore)

private theorem ctorAssignGem (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage gemRef (.address gem) =
      .ok (ctorFrame vat gem, ctorAfterGem evm gem) := by
  let er : EvaledStorageRef := { base := "gem", steps := [] }
  have hbase : (ctorLocals vat gem).get? "gem" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm gemRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    simp [er, contract, storageDecls, storageTypeAt?, addrSt]
  have hloc : config.storage.layout er = fun _ => some (addrLoc (⟨3⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (addrLoc (⟨3⟩ : UInt256)) (.address gem) =
        some (ctorAfterGem evm gem) := by
    simpa [ctorAfterGem, show (⟨3⟩ : UInt256) = UInt256.ofNat 3 by decide] using
      ctorAddrLocStore evm (⟨3⟩ : UInt256) gem
  exact assignStorageRef_storage_scalar_value (ty := .elem .address)
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hscalar := by trivial)
    (hstore := hstore)

private theorem ctorAssignLive (evm : EVM.State) (vat gem : AccountAddress) :
    assignStorageRef? config (ctorFrame vat gem) evm .storage liveRef (.int 1) =
      .ok (ctorFrame vat gem, ctorAfterLive evm) := by
  let er : EvaledStorageRef := { base := "live", steps := [] }
  have hbase : (ctorLocals vat gem).get? "live" = none := by simp [ctorLocals]
  have her : evalStorageRef config (ctorFrame vat gem) evm liveRef = .ok er := by
    simp [ctorFrame, er, evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc (⟨7⟩ : UInt256)) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er]
  have hstore :
      storageLocStore evm (wordLoc (⟨7⟩ : UInt256)) (.int 1) =
        some (ctorAfterLive evm) := by
    simpa [ctorAfterLive, wordLoc, uint256Loc,
      show (⟨7⟩ : UInt256) = UInt256.ofNat 7 by decide] using
      storageLocStore_uint256 evm (⟨7⟩ : UInt256) (UInt256.ofNat 1)
  exact assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)

private theorem flapperCtorBodyReturns (evm : EVM.State) (vat gem : AccountAddress)
    (hwv : evm.executionEnv.weiValue = (⟨0⟩ : UInt256)) :
    ExecTransitionBody config contract evm (ctorLocals vat gem) constructorDecl.body
      (.returned (ctorFrame vat gem) (ctorSourceFinalEVM evm vat gem) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (ctorFrame vat gem) evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .assign .storage begRef (.intLit defaultBeg),
      .assign .storage ttlRef (.intLit defaultTtl),
      .assign .storage tauRef (.intLit defaultTau),
      .assign .storage kicksRef (.intLit 0),
      .assign .storage (wardsRef sender) (.intLit 1),
      .assign .storage vatRef (.var "vat_"),
      .assign .storage gemRef (.var "gem_"),
      .assign .storage liveRef (.intLit 1) ]
    (.ok (ctorFrame vat gem) (ctorSourceFinalEVM evm vat gem))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure, defaultBeg]) (ctorAssignBeg evm vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure, defaultTtl])
      (ctorAssignTtl (ctorAfterBeg evm) vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure, defaultTau])
      (ctorAssignTau (ctorAfterTtl (ctorAfterBeg evm)) vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (ctorAssignKicks
      (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm))) vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (ctorAssignWards
      (ctorAfterKicks (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm)))) vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (by
        have hget : (ctorLocals vat gem).get? "vat_" = some (.address vat) := by
          rw [Std.HashMap.get?_eq_getElem?]
          rw [Std.HashMap.getElem?_insert]
          simp [ctorLocals]
        simp only [evalExpr?]
        rw [show (ctorFrame vat gem).locals.get? "vat_" = some (.address vat) by
          simpa [ctorFrame] using hget]
        rfl)
      (ctorAssignVat
        (ctorAfterWards
          (ctorAfterKicks (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm))))) vat gem)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (by
        have hget : (ctorLocals vat gem).get? "gem_" = some (.address gem) := by
          rw [Std.HashMap.get?_eq_getElem?]
          rw [Std.HashMap.getElem?_insert]
          simp [ctorLocals]
        simp only [evalExpr?]
        rw [show (ctorFrame vat gem).locals.get? "gem_" = some (.address gem) by
          simpa [ctorFrame] using hget]
        rfl)
      (ctorAssignGem
        (ctorAfterVat
          (ctorAfterWards
            (ctorAfterKicks (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm))))) vat)
        vat gem)) ?_
  simpa [ctorSourceFinalEVM] using
    (ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (ctorAssignLive
          (ctorAfterGem
            (ctorAfterVat
              (ctorAfterWards
                (ctorAfterKicks (ctorAfterTau (ctorAfterTtl (ctorAfterBeg evm))))) vat)
            gem)
          vat gem))
      ExecBlock.nil)

private theorem flapperSolmCtorExecRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment flapperCreationBytecode args = some deployedInitcode)
    (hne : I.weiValue ≠ (⟨0⟩ : UInt256)) :
    solmCtorExec config contract args createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args))
    ?_ ?_ ?_ ?_
  · rfl
  · simpa [contract, constructorDecl] using flapperCtorDeployment_args_length hdeploy
  · rfl
  · exact bodyReverts_nonPayable (cfg := config) (contract := contract)
      (locals := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args))
      (by simpa [initState] using hne)

private theorem flapperSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment flapperCreationBytecode args = some deployedInitcode)
    (hwv : I.weiValue = (⟨0⟩ : UInt256)) :
    ∃ vat gem,
      args = [Value.address vat, Value.address gem] ∧
      deployedInitcode = flapperCreationBytecode ++ ctorTail vat gem ∧
      solmCtorExec config contract args createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned (ctorFrame vat gem)
          (ctorSourceFinalEVM
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
            vat gem)
          none) := by
  obtain ⟨vat, gem, hargs, hdeployed⟩ := flapperCtorDeployment_shape hdeploy
  refine ⟨vat, gem, hargs, hdeployed, ?_⟩
  subst args
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
    (argsStore := ctorLocals vat gem) ?_ ?_ ?_ ?_
  · rfl
  · simp [contract, constructorDecl]
  · rfl
  · exact flapperCtorBodyReturns
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ (.ofUInt256 g) A I)
      vat gem (by simpa [initState] using hwv)

private theorem flapperConstructorRDrevNonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : Sat256} {A : Substate} {I : ExecutionEnv}
    {vat gem : AccountAddress}
    (hcode : I.code = flapperCreationBytecode ++ ctorTail vat gem)
    (hperm : I.perm = true)
    (hne : I.weiValue ≠ (⟨0⟩ : UInt256)) :
    RDrev (flapperCreationBytecode ++ ctorTail vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have hstart :
      RD (flapperCreationBytecode ++ ctorTail vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (UInt256.ofNat 0) [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
        (createdAccounts, σ) 0 0 :=
    RD.initState (code := flapperCreationBytecode ++ ctorTail vat gem) hcode
  obtain ⟨aw1, k1, C1, hpc73⟩ :=
    flapperCreationBlocks.flapperCreation_block_0_fallthrough_packed
      (tail := ctorTail vat gem) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ByteArray.empty) (aw := UInt256.ofNat 0) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := σ) (R := [])
      (by norm_num) hperm (by simpa using isZero_eq_zero_of_ne hne) hstart
  exact flapperCreationBlocks.flapperCreation_block_73
    (tail := ctorTail vat gem) (ee := I) (g := g)
    (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    (mem := flapperCreationBlocks.flapperCreation_block_0_fallthrough_memory
      (mem := ByteArray.empty))
    (aw := aw1) (rdata := ByteArray.empty) (cA := createdAccounts)
    (σ := storageWrite I.codeOwner
      (storageWrite I.codeOwner
        (storageWrite I.codeOwner σ (UInt256.ofNat 4)
          (UInt256.ofNat 1050000000000000000))
        (UInt256.ofNat 5)
        (UInt256.lor (UInt256.ofNat 48638875975601356800)
          (UInt256.land
            (UInt256.lnot
              (UInt256.shiftLeft (UInt256.ofNat 281474976710655) (UInt256.ofNat 48)))
            (UInt256.lor
              (UInt256.land
                (storageRead I.codeOwner
                  (storageWrite I.codeOwner σ (UInt256.ofNat 4)
                    (UInt256.ofNat 1050000000000000000))
                  (UInt256.ofNat 5))
                (UInt256.lnot (UInt256.ofNat 281474976710655)))
              (UInt256.ofNat 10800)))))
      (UInt256.ofNat 6) (UInt256.ofNat 0))
    (k := k1) (C := C1)
    (R := flapperCreationBlocks.flapperCreation_block_0_fallthrough_stack
      (ee := I) (R := []))
    (by simp [flapperCreationBlocks.flapperCreation_block_0_fallthrough_stack])
    hpc73

private theorem flapperConstructorRDretSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : Sat256} {A : Substate} {I : ExecutionEnv}
    {vat gem : AccountAddress}
    (hcode : I.code = flapperCreationBytecode ++ ctorTail vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = (⟨0⟩ : UInt256)) :
    RDret (flapperCreationBytecode ++ ctorTail vat gem) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, ctorCreationFinalMap I σ vat gem) flapperBytecode := by
  have hstart :
      RD (flapperCreationBytecode ++ ctorTail vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (UInt256.ofNat 0) [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
        (createdAccounts, σ) 0 0 :=
    RD.initState (code := flapperCreationBytecode ++ ctorTail vat gem) hcode
  obtain ⟨aw1, k1, C1, hpc77⟩ :=
    flapperCreationBlocks.flapperCreation_block_0_taken_packed
      (tail := ctorTail vat gem) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ByteArray.empty) (aw := UInt256.ofNat 0) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := σ) (R := [])
      (by norm_num) hperm (by rw [hwv]; native_decide) (by native_decide) hstart
  have hpc77' :
      RD (flapperCreationBytecode ++ ctorTail vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (UInt256.ofNat 77) (I.weiValue :: []) ctorCreationFreePtrMem aw1 ByteArray.empty
        (createdAccounts, ctorCreationAfterDefaults I σ) k1 C1 := by
    simpa [ctorCreationFreePtrMem, ctorCreationAfterDefaults, ctorCreationSlot5Word,
      ctorBegWord, ctorTtlWordConst, ctorTauShifted, ctorTauMask, flapperUint48Mask,
      flapperCreationBlocks.flapperCreation_block_0_taken_stack]
      using hpc77
  have hlen64 : ctorCreationArgLength vat gem = UInt256.ofNat 64 := by
    rw [ctorCreationArgLength, ByteArray.size_append]
    have hcreation : flapperCreationBytecode.size = 5216 := by native_decide
    have htail : (ctorTail vat gem).size = 64 := by
      rw [ctorTail_eq, ByteArray.size_append,
        word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]
    rw [hcreation, htail]
    native_decide
  have hcond77 :
      UInt256.isZero
        (UInt256.lt (ctorCreationArgLength vat gem) (UInt256.ofNat 64)) ≠
          (UInt256.ofNat 0) := by
    rw [hlen64]
    native_decide
  obtain ⟨aw2, k2, C2, hpc112⟩ :=
    flapperCreationBlocks.flapperCreation_block_77_taken_packed
      (tail := ctorTail vat gem) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ctorCreationFreePtrMem) (aw := aw1) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := ctorCreationAfterDefaults I σ)
      (x0 := I.weiValue) (R := [])
      (by norm_num)
      (by simpa [ctorCreationArgLength] using hcond77)
      (by native_decide) hpc77'
  have hpc112' :
      RD (flapperCreationBytecode ++ ctorTail vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (UInt256.ofNat 112)
        (ctorCreationArgLength vat gem :: ctorCreationArgBase :: [])
        (ctorCreationArgsMem vat gem) aw2 ByteArray.empty
        (createdAccounts, ctorCreationAfterDefaults I σ) k2 C2 := by
    simpa [ctorCreationArgLength, ctorCreationArgBase, ctorCreationArgsMem,
      flapperCreationBlocks.flapperCreation_block_77_taken_stack]
      using hpc112
  obtain ⟨k3, C3, hpc188⟩ :=
    flapperCreationBlocks.flapperCreation_block_112
      (tail := ctorTail vat gem) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := ctorCreationArgsMem vat gem) (aw := aw2) (rdata := ByteArray.empty)
      (cA := createdAccounts) (σ := ctorCreationAfterDefaults I σ)
      (x0 := ctorCreationArgLength vat gem) (x1 := ctorCreationArgBase) (R := [])
      (by norm_num) hperm hpc112'
  have hpc188' :
      RD (flapperCreationBytecode ++ ctorTail vat gem) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (UInt256.ofNat 188)
        (ctorCreationGemWord I σ vat gem :: UInt256.ofNat 1 :: UInt256.ofNat 3 :: [])
        (flapperCreationBlocks.flapperCreation_block_112_memory
          (ee := I) (mem := ctorCreationArgsMem vat gem))
        (M (M (M (M (M aw2 ctorCreationArgBase (⟨32⟩ : UInt256))
          ((UInt256.ofNat 32) + ctorCreationArgBase) (⟨32⟩ : UInt256))
          (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32)
          (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64))
        ByteArray.empty (createdAccounts, ctorCreationAfterVat I σ vat gem) k3 C3 := by
    simpa [ctorCreationAfterVat, ctorCreationAfterWards, ctorCreationVatWord,
      ctorCreationWardsSlot, ctorCreationGemWord, ctorAddressStoreWord, solcAddrMask,
      flapperCreationBlocks.flapperCreation_block_112_stack]
      using hpc188
  have hret :=
    flapperCreationBlocks.flapperCreation_block_188
      (tail := ctorTail vat gem) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (mem := flapperCreationBlocks.flapperCreation_block_112_memory
        (ee := I) (mem := ctorCreationArgsMem vat gem))
      (aw := M (M (M (M (M aw2 ctorCreationArgBase (⟨32⟩ : UInt256))
        ((UInt256.ofNat 32) + ctorCreationArgBase) (⟨32⟩ : UInt256))
        (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32)
        (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64))
      (rdata := ByteArray.empty) (cA := createdAccounts)
      (σ := ctorCreationAfterVat I σ vat gem) (x0 := ctorCreationGemWord I σ vat gem)
      (x1 := UInt256.ofNat 1) (x2 := UInt256.ofNat 3) (R := [])
      (by norm_num) hperm hpc188'
  simpa [ctorCreationFinalMap, flapperCreationRuntimeSlice] using hret

private theorem flapperConstructorFinalMapEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {vat gem : AccountAddress}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (ctorCreationFinalMap I σ_evm vat gem)
      (ctorSourceFinalEVM
        (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (.ofUInt256 g) A I)
        vat gem).accountMap := by
  let evmE : EVM.State :=
    initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (.ofUInt256 g) A I
  let evmS : EVM.State :=
    initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (.ofUInt256 g) A I
  by_cases hmissing : σ_evm.find? I.codeOwner = none
  · have hmissingS : σ_solm.find? I.codeOwner = none :=
      accountMapEquiv_find?_none hAccounts hmissing
    rw [ctorCreationFinalMap_missing I σ_evm vat gem hmissing]
    rw [ctorSourceFinal_accountMap_missing evmS vat gem (by
      simpa [evmS, initState] using hmissingS)]
    exact hAccounts
  · cases hfind : σ_evm.find? I.codeOwner with
    | none => exact False.elim (hmissing hfind)
    | some account =>
        have hInit : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState
              (cA := createdAccounts) (gh := genesisBlockHeader) (bl := blocks)
              (σ₁ := σ_evm) (σ₀₁ := σ₀) (σ₂ := σ_solm) (σ₀₂ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) hAccounts
        have hSourceDefaults := ctorSourceAfterDefaults_stateEquiv hInit
        have hGeneratedDefaults :=
          ctorCreationAfterDefaults_sourceEquiv_same_present evmE (by
            simpa [evmE, initState] using hfind)
        have hDefaults :
            accountMapEquiv (ctorCreationAfterDefaults I σ_evm)
              (ctorSourceAfterDefaults evmS).accountMap := by
          exact accountMapEquiv.trans
            (by simpa [evmE, initState] using hGeneratedDefaults)
            hSourceDefaults.accountMap
        have hDefaultEnv :
            (ctorSourceAfterDefaults evmS).executionEnv = I := by
          simp [evmS, initState, ctorSourceAfterDefaults, ctorAfterKicks, ctorAfterTau,
            ctorAfterTtl, ctorAfterBeg, storageStore_executionEnv]
        have hDefaultOwner :
            (ctorSourceAfterDefaults evmS).executionEnv.codeOwner = I.codeOwner :=
          congrArg ExecutionEnv.codeOwner hDefaultEnv
        have hWards :
            accountMapEquiv (ctorCreationAfterWards I σ_evm vat gem)
              (ctorAfterWards (ctorSourceAfterDefaults evmS)).accountMap := by
          have hstore :=
            accountMapEquiv_sstoreAccountMap I.codeOwner (ctorWardsSlot I)
              (UInt256.ofNat 1) hDefaults
          simpa [ctorCreationAfterWards, ctorAfterWards, ctorCreationWardsSlot_eq,
            storageWrite_eq, storageStore_accountMap, hDefaultEnv] using hstore
        have hWardsOwner :
            (ctorAfterWards (ctorSourceAfterDefaults evmS)).executionEnv.codeOwner =
              I.codeOwner := by
          simp [evmS, initState, ctorAfterWards, ctorSourceAfterDefaults, ctorAfterKicks,
            ctorAfterTau, ctorAfterTtl, ctorAfterBeg, storageStore_executionEnv]
        have hVatLoad :
            storageRead I.codeOwner (ctorCreationAfterWards I σ_evm vat gem)
                (UInt256.ofNat 2) =
              Solm.EVM.storageLoad (ctorAfterWards (ctorSourceAfterDefaults evmS))
                (ctorAfterWards (ctorSourceAfterDefaults evmS)).executionEnv.codeOwner
                (UInt256.ofNat 2) := by
          have hread :=
            accountMapEquiv_storage_findD hWards I.codeOwner (UInt256.ofNat 2)
              (default : UInt256)
          rw [storageLoad_eq_storageRead]
          rw [hWardsOwner]
          simpa [storageRead_eq] using hread
        have hVatWord :
            ctorCreationVatWord I σ_evm vat gem =
              ctorAddressStoreWord
                (Solm.EVM.storageLoad (ctorAfterWards (ctorSourceAfterDefaults evmS))
                  (ctorAfterWards (ctorSourceAfterDefaults evmS)).executionEnv.codeOwner
                  (UInt256.ofNat 2))
                (UInt256.ofNat vat.val) := by
          unfold ctorCreationVatWord ctorAddressStoreWord
          rw [ctorCreationArgsMem_mloadVat, hVatLoad]
          rw [u256_land_comm (UInt256.lnot solcAddrMask)
            (Solm.EVM.storageLoad (ctorAfterWards (ctorSourceAfterDefaults evmS))
              (ctorAfterWards (ctorSourceAfterDefaults evmS)).executionEnv.codeOwner
              (UInt256.ofNat 2))]
          rw [u256_land_comm solcAddrMask (UInt256.ofNat vat.val)]
        have hVat :
            accountMapEquiv (ctorCreationAfterVat I σ_evm vat gem)
              (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat).accountMap := by
          have hstore :=
            accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 2)
              (ctorAddressStoreWord
                (Solm.EVM.storageLoad (ctorAfterWards (ctorSourceAfterDefaults evmS))
                  (ctorAfterWards (ctorSourceAfterDefaults evmS)).executionEnv.codeOwner
                  (UInt256.ofNat 2))
                (UInt256.ofNat vat.val))
              hWards
          simpa [ctorCreationAfterVat, ctorAfterVat, storageWrite_eq, storageStore_accountMap,
            hVatWord, hWardsOwner] using hstore
        have hVatOwner :
            (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat).executionEnv.codeOwner =
              I.codeOwner := by
          simp [evmS, initState, ctorAfterVat, ctorAfterWards, ctorSourceAfterDefaults,
            ctorAfterKicks, ctorAfterTau, ctorAfterTtl, ctorAfterBeg, storageStore_executionEnv]
        have hGemLoad :
            storageRead I.codeOwner (ctorCreationAfterVat I σ_evm vat gem)
                (UInt256.ofNat 3) =
              Solm.EVM.storageLoad
                (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
                (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat).executionEnv.codeOwner
                (UInt256.ofNat 3) := by
          have hread :=
            accountMapEquiv_storage_findD hVat I.codeOwner (UInt256.ofNat 3)
              (default : UInt256)
          rw [storageLoad_eq_storageRead]
          rw [hVatOwner]
          simpa [storageRead_eq] using hread
        have hGemWord :
            ctorCreationGemWord I σ_evm vat gem =
              ctorAddressStoreWord
                (Solm.EVM.storageLoad
                  (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
                  (ctorAfterVat
                    (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat).executionEnv.codeOwner
                  (UInt256.ofNat 3))
                (UInt256.ofNat gem.val) := by
          unfold ctorCreationGemWord
          rw [ctorCreationArgsMem_mloadGem, hGemLoad]
        have hGem :
            accountMapEquiv
              (storageWrite I.codeOwner (ctorCreationAfterVat I σ_evm vat gem)
                (UInt256.ofNat 3) (ctorCreationGemWord I σ_evm vat gem))
              (ctorAfterGem
                (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
                gem).accountMap := by
          have hstore :=
            accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 3)
              (ctorAddressStoreWord
                (Solm.EVM.storageLoad
                  (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
                  (ctorAfterVat
                    (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat).executionEnv.codeOwner
                  (UInt256.ofNat 3))
                (UInt256.ofNat gem.val))
              hVat
          simpa [ctorAfterGem, storageWrite_eq, storageStore_accountMap, hGemWord,
            hVatOwner] using hstore
        have hGemOwner :
            (ctorAfterGem
                (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
                gem).executionEnv.codeOwner = I.codeOwner := by
          simp [evmS, initState, ctorAfterGem, ctorAfterVat, ctorAfterWards,
            ctorSourceAfterDefaults, ctorAfterKicks, ctorAfterTau, ctorAfterTtl, ctorAfterBeg,
            storageStore_executionEnv]
        have hLive :=
          accountMapEquiv_sstoreAccountMap I.codeOwner (UInt256.ofNat 7)
            (UInt256.ofNat 1) hGem
        change accountMapEquiv
          (storageWrite I.codeOwner
            (storageWrite I.codeOwner (ctorCreationAfterVat I σ_evm vat gem)
              (UInt256.ofNat 3) (ctorCreationGemWord I σ_evm vat gem))
            (UInt256.ofNat 7) (UInt256.ofNat 1))
          (Solm.EVM.storageStore
            (ctorAfterGem
              (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
              gem)
            (ctorAfterGem
              (ctorAfterVat (ctorAfterWards (ctorSourceAfterDefaults evmS)) vat)
              gem).executionEnv.codeOwner
            (UInt256.ofNat 7) (UInt256.ofNat 1)).accountMap
        rw [storageWrite_eq, storageStore_accountMap, hGemOwner]
        exact hLive

theorem flapperConstructorCorrect :
    constructorEquivalence config flapperCreationBytecode contract flapperBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args
    deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  by_cases hwv : I.weiValue = (⟨0⟩ : UInt256)
  · obtain ⟨vat, gem, hargs, hdeployed, hsolm⟩ :=
      flapperSolmCtorExecSuccess
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        (args := args) (deployedInitcode := deployedInitcode) hdeploy hwv
    subst args
    rw [hdeployed] at hcode
    have hrd :=
      flapperConstructorRDretSuccess
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
        (A := A) (I := I) (vat := vat) (gem := gem) hcode hperm hwv
    rcases hrd with hoog | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [hcode]
          simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
    · have hsuccess :=
        Xi_success_of_X (g := g) (by
          rw [hcode]
          simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ : s.accountMap = ctorCreationFinalMap I σ_evm vat gem := congrArg Prod.snd hacc
      rw [hcA, hσ] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess hsolm ?_
      exact @ctorResultEquiv.success
        (.ok (.success (createdAccounts, ctorCreationFinalMap I σ_evm vat gem,
          s.machineState.gasAvailable.toUInt256, s.substate) flapperBytecode))
        (.returned (ctorFrame vat gem)
          (ctorSourceFinalEVM
            (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
              (Sat256.ofUInt256 g) A I)
            vat gem)
          none)
        flapperBytecode
        (ctorFrame vat gem)
        createdAccounts
        (ctorCreationFinalMap I σ_evm vat gem)
        s.machineState.gasAvailable.toUInt256
        s.substate
        flapperBytecode
        (ctorSourceFinalEVM
          (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
            (Sat256.ofUInt256 g) A I)
          vat gem)
        rfl rfl
        (by simp [ctorSourceFinal_createdAccounts, initState])
        (flapperConstructorFinalMapEquiv
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
          (g := g) (A := A) (I := I) (vat := vat) (gem := gem) hAccounts)
        rfl
  · obtain ⟨vat, gem, _hargs, hdeployed⟩ := flapperCtorDeployment_shape hdeploy
    rw [hdeployed] at hcode
    have hrd :=
      flapperConstructorRDrevNonpayable
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
        (A := A) (I := I) (vat := vat) (gem := gem) hcode hperm hwv
    rcases hrd.xiResult hcode with hoog | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas
        (by simpa [Sat256.ofUInt256, Sat256.toUInt256] using hoog)
    · refine constructorEquivalenceFor.execution
        (by simpa [Sat256.ofUInt256, Sat256.toUInt256] using hrev)
        (flapperSolmCtorExecRevert
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          (args := args) (deployedInitcode := deployedInitcode) hdeploy hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Flapper
