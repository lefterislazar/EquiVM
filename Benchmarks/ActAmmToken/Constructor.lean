import Benchmarks.ActAmmToken.Storage
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Constructor
import Reasoning.Stepping
import Solm.Equiv

/-! # Act AMM Token constructor-equivalence target -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000


/-- Solidity deployment accepts exactly one `uint256 _totalSupply` argument. -/
theorem tokenCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    config.selfDeployment tokenCreationBytecode args = some deployedInitcode →
    ∃ supply : Int,
      args = [.int supply]
        ∧ 0 ≤ supply
        ∧ supply < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode =
          tokenCreationBytecode ++ (EVM.Word.toBytesBE (EVM.word supply.toNat)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
              encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
              staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | int supply =>
              by_cases hbounds : 0 ≤ supply ∧ supply < Int.ofNat (EVM.twoPow 256)
              · simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                  encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ supply ∧ supply < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word supply.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (tokenCreationBytecode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · simp at h
                  exact ⟨supply, rfl, hbounds.1, hbounds.2, h.symm⟩
                · rename_i hnot
                  exact False.elim (hnot hbounds)
              · simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                  encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256, uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ supply ∧ supply < Int.ofNat (EVM.twoPow 256) then
                    some (EVM.word supply.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (tokenCreationBytecode ++ args.toByteArray)) =
                  some deployedInitcode at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | bool b =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | address a =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, uint256,
                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem tokenCreationBytecode_size : tokenCreationBytecode.size = 3845 := by
  native_decide

theorem tokenBytecode_size : tokenBytecode.size = 3621 := by
  native_decide

theorem tokenCreationBytecode_runtime_window :
    tokenCreationBytecode.extract 224 (224 + 3621) = tokenBytecode := by
  native_decide

noncomputable def tokenCtorCode (supplyWord : UInt256) : ByteArray :=
  tokenCreationBytecode ++ (EVM.Word.toBytesBE supplyWord).toByteArray

theorem tokenCreationBytecode_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 224) :
    decode (tokenCreationBytecode ++ tail) pc = decode tokenCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window tokenCreationBytecode tail pc
    (by rw [tokenCreationBytecode_size]; omega) (by rw [tokenCreationBytecode_size]; norm_num)

macro "token_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [tokenCreationBytecode_decode_append _ _ (by decide)]
      | (unfold tokenCtorCode; rw [tokenCreationBytecode_decode_append _ _ (by decide)]);
     native_decide))

macro "token_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold tokenCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "token_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by token_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by token_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by token_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by token_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

noncomputable def tokenCtorRuntimeMem : ByteArray :=
  tokenCreationBytecode.write 224 ByteArray.empty 0 3621

theorem tokenCtorRuntimeMem_read :
    tokenCtorRuntimeMem.readWithPadding 0 3621 = tokenBytecode := by
  unfold tokenCtorRuntimeMem
  calc
    (tokenCreationBytecode.write 224 ByteArray.empty 0 3621).readWithPadding 0 3621
        = tokenCreationBytecode.extract 224 (224 + 3621) :=
      write0_read_back_from_gen tokenCreationBytecode ByteArray.empty 224 3621
        (by norm_num) (by rw [tokenCreationBytecode_size]) (by norm_num)
    _ = tokenBytecode := tokenCreationBytecode_runtime_window

theorem tokenCtorCode_size (supplyWord : UInt256) :
    (tokenCtorCode supplyWord).size = 3877 := by
  unfold tokenCtorCode
  rw [ByteArray.size_append, tokenCreationBytecode_size, word_toBytesBE_toByteArray_size]

theorem tokenCtorArgLen_eq (supplyWord : UInt256) :
    (UInt256.ofNat (tokenCtorCode supplyWord).size).sub ⟨3845⟩ = (⟨32⟩ : UInt256) := by
  rw [tokenCtorCode_size]
  native_decide

noncomputable def tokenCtorArgMem (supplyWord : UInt256) : ByteArray :=
  solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++ UInt256.toByteArray supplyWord

theorem tokenCtorArg_codecopy_mem (supplyWord : UInt256) :
    (tokenCtorCode supplyWord).write 3845 solcFreePtrMem 128 32 =
      tokenCtorArgMem supplyWord := by
  unfold tokenCtorArgMem tokenCtorCode
  have hctorD : tokenCreationBytecode.data.size = 3845 := tokenCreationBytecode_size
  have hsfpD : solcFreePtrMem.data.size = 96 := solcFreePtrMem_size
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by norm_num : ¬ (32 : Nat) = 0),
    if_neg (show ¬ 3845 ≥ (tokenCreationBytecode ++
      (EVM.Word.toBytesBE supplyWord).toByteArray).size by
        rw [ByteArray.size_append, tokenCreationBytecode_size, word_toBytesBE_toByteArray_size]
        norm_num)]
  have e1 :
      min 32 ((tokenCreationBytecode ++ (EVM.Word.toBytesBE supplyWord).toByteArray).size -
        3845) = 32 := by
    rw [ByteArray.size_append, tokenCreationBytecode_size, word_toBytesBE_toByteArray_size]
    norm_num
  have e2 : min solcFreePtrMem.size (128 + 32) = 96 := by
    rw [solcFreePtrMem_size]
    norm_num
  simp only [ByteArray.data_copySlice, ByteArray.data_append, e1, solcFreePtrMem_size,
    show (128 : Nat) - 96 = 32 from by norm_num,
    show min 96 (128 + 32) - (128 + 32) = 0 from by norm_num]
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  have hz32 : (ffi.ByteArray.zeroes 32).data.size = 32 := by
    show (ffi.ByteArray.zeroes 32).size = 32
    exact zeroes_ofNat_size 32 (by norm_num)
  simp only [Array.append_empty, Nat.add_zero]
  have ext1 :
      (solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data).extract
          0 128 =
        solcFreePtrMem.data ++ (ffi.ByteArray.zeroes 32).data :=
    Array.extract_eq_self_of_le (by rw [Array.size_append, hsfpD, hz32])
  have ext2 :
      (tokenCreationBytecode.data ++ (EVM.Word.toBytesBE supplyWord).toByteArray.data).extract
          3845 (3845 + 32) =
        (UInt256.toByteArray supplyWord).data := by
    rw [show (3845 : Nat) = tokenCreationBytecode.data.size from hctorD.symm,
      Array.extract_append_right]
    rw [word_toBytesBE_toByteArray_eq_toByteArray]
    apply Array.extract_eq_self_of_le
    change (UInt256.toByteArray supplyWord).size ≤ 32
    rw [toByteArray_size]
  rw [ext1, ext2,
    Array.extract_empty_of_size_le_start (by rw [Array.size_append, hsfpD, hz32]; norm_num),
    Array.append_empty]

theorem tokenCtorArgMem_size (supplyWord : UInt256) :
    (tokenCtorArgMem supplyWord).size = 160 := by
  unfold tokenCtorArgMem
  simp [solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num), toByteArray_size]

theorem tokenCtorArgMem_read128 (supplyWord : UInt256) :
    (tokenCtorArgMem supplyWord).readWithPadding 128 32 =
      UInt256.toByteArray supplyWord := by
  unfold tokenCtorArgMem
  rw [readWithPadding_eq_extract]
  · rw [extract_append_right_window]
    · rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size 32 (by norm_num)]
      rw [show 128 - (96 + 32) = 0 by norm_num]
      rw [show 128 + 32 - (96 + 32) = 32 by norm_num]
      rw [toByteArray_extract_all]
    · rw [ByteArray.size_append, solcFreePtrMem_size,
        zeroes_ofNat_size 32 (by norm_num)]
  · rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size 32 (by norm_num), toByteArray_size]

theorem tokenCtorArgMem_mload128 (supplyWord : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (tokenCtorArgMem supplyWord).size
        ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian ((tokenCtorArgMem supplyWord).readWithPadding 128 32))) =
      supplyWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := tokenCtorArgMem supplyWord) (aw := UInt256.ofNat 5) (off := ⟨128⟩)
    (v := supplyWord)
    (by rw [tokenCtorArgMem_size]; decide)
    (by decide)
    (tokenCtorArgMem_read128 supplyWord)

noncomputable def tokenCtorArgFreeMem (supplyWord : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨160⟩).write 0 (tokenCtorArgMem supplyWord) 64 32

theorem tokenCtorArgFreeMem_size (supplyWord : UInt256) :
    (tokenCtorArgFreeMem supplyWord).size = 160 := by
  unfold tokenCtorArgFreeMem
  simp [tokenCtorArgMem_size, write32_eq, ByteArray.size_append, ByteArray.size_extract,
    toByteArray_size]

theorem tokenCtorArgFreeMem_read64 (supplyWord : UInt256) :
    (tokenCtorArgFreeMem supplyWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold tokenCtorArgFreeMem
  rw [toByteArray_write32_read_back]
  rw [tokenCtorArgMem_size]
  decide

theorem tokenCtorArgFreeMem_read128 (supplyWord : UInt256) :
    (tokenCtorArgFreeMem supplyWord).readWithPadding 128 32 =
      UInt256.toByteArray supplyWord := by
  unfold tokenCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
      (by rw [tokenCtorArgMem_size]; omega) (by omega)
      (by rw [tokenCtorArgMem_size])]
  exact tokenCtorArgMem_read128 supplyWord

theorem tokenCtorArgFreeMem_mload128 (supplyWord : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (tokenCtorArgFreeMem supplyWord).size
        ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian ((tokenCtorArgFreeMem supplyWord).readWithPadding 128 32))) =
      supplyWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := tokenCtorArgFreeMem supplyWord) (aw := UInt256.ofNat 5) (off := ⟨128⟩)
    (v := supplyWord)
    (by rw [tokenCtorArgFreeMem_size]; decide)
    (by decide)
    (tokenCtorArgFreeMem_read128 supplyWord)


theorem tokenInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = tokenCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (tokenCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (tokenCreationBytecode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd11 := token_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by token_ctor_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push1 ⟨14⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact token_ctor_run rd11 with [
    push0, push0,
    raw rev 0 (by token_ctor_decode) mem_cost (by evm_ov)]

theorem tokenCtorPayableGuardTrace
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (supplyWord : UInt256)
    (hcode : I.code = tokenCtorCode supplyWord)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (tokenCtorCode supplyWord) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨16⟩
      [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd0 :
      RD (tokenCtorCode supplyWord) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd16 := token_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by token_ctor_decode)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push1 ⟨14⟩,
    jumpiT (by rw [hwv]; decide) (by token_ctor_jd),
    jumpdest, pop]
  exact ⟨_, _, rd16⟩

set_option maxHeartbeats 3000000 in
theorem tokenCtorArgCodecopyTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (supplyWord : UInt256)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨16⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨30⟩
      [⟨32⟩, ⟨128⟩] (tokenCtorArgMem supplyWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have rd := token_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by token_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨3845⟩, codesize, sub, dup1, push2 ⟨3845⟩, dup4,
    raw codecopy 6 (tokenCtorArgMem supplyWord) (UInt256.ofNat 5)
      (by token_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [tokenCtorArgLen_eq]
        decide)
      (by
        rw [tokenCtorArgLen_eq]
        exact tokenCtorArg_codecopy_mem supplyWord)
      (by rw [tokenCtorArgLen_eq]; decide) (by evm_ov)]
  have rd' : RD (tokenCtorCode supplyWord) I g s0 ⟨30⟩
      [⟨32⟩, ⟨128⟩] (tokenCtorArgMem supplyWord) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + (0 + 3) + 3 + 2 + 3 + 3 + 3 + 3 +
        (6 + (GasConstants.Gverylow + GasConstants.Gcopy * ((32 + 31) / 32)))) := by
    simpa [tokenCtorArgLen_eq] using rd
  exact ⟨_, _, rd'⟩

theorem tokenCtorArgFreePtrTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (supplyWord : UInt256)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨30⟩
      [⟨32⟩, ⟨128⟩] (tokenCtorArgMem supplyWord) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨36⟩
      [⟨32⟩, ⟨128⟩] (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have rd := token_ctor_run h with [
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5)
      (by token_ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  exact ⟨_, _, rd⟩

theorem tokenCtorArgCopyTrace
    {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (supplyWord : UInt256)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨16⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨36⟩
      [⟨32⟩, ⟨128⟩] (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd32⟩ := tokenCtorArgCodecopyTrace (I := I) supplyWord h
  exact tokenCtorArgFreePtrTrace (I := I) supplyWord rd32


theorem tokenCtorArgDecodeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (supplyWord : UInt256)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨36⟩ [⟨32⟩, ⟨128⟩]
      (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨46⟩ [supplyWord]
      (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5) rdata acc k' C' := by
  have rd173 := token_ctor_run h with [
    dup2, add, swap1, push1 ⟨46⟩, swap2, swap1,
    push1 ⟨173⟩, jump (by token_ctor_jd)]
  have rd191 := token_ctor_run rd173 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push1 ⟨191⟩, jumpiT (by native_decide) (by token_ctor_jd)]
  have rd155 := token_ctor_run rd191 with [
    jumpdest, push0, push1 ⟨202⟩, dup5, dup3, dup6, add,
    push1 ⟨155⟩, jump (by token_ctor_jd)]
  have rd136 := token_ctor_run rd155 with [
    jumpdest, push0, dup2,
    raw mload 0 supplyWord (UInt256.ofNat 5)
      (by token_ctor_decode) mem_cost
      (tokenCtorArgFreeMem_mload128 supplyWord) (by decide) (by evm_ov),
    swap1, pop, push1 ⟨167⟩, dup2, push1 ⟨136⟩, jump (by token_ctor_jd)]
  have rd143 := token_ctor_run rd136 with [
    jumpdest, push1 ⟨143⟩, dup2, push1 ⟨127⟩, jump (by token_ctor_jd),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by token_ctor_jd)]
  have heq : UInt256.eq supplyWord supplyWord = ⟨1⟩ := u256_eq_refl _
  have rd152 := token_ctor_run rd143 with [
    jumpdest, dup2, eq, push1 ⟨152⟩,
    jumpiT (by rw [heq]; decide) (by token_ctor_jd)]
  have rd167 := token_ctor_run rd152 with [jumpdest, pop, jump (by token_ctor_jd)]
  have rd202 := token_ctor_run rd167 with [
    jumpdest, swap3, swap2, pop, pop, jump (by token_ctor_jd)]
  exact ⟨_, _, token_ctor_run rd202 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by token_ctor_jd)]⟩

def tokenCtorAfterSupplyMap (σ : AccountMap) (I : ExecutionEnv)
    (supplyWord : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ supplyWord

def tokenCtorBalanceSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨1⟩ (solcSourceWord I)

def tokenCtorFinalMap (σ : AccountMap) (I : ExecutionEnv)
    (supplyWord : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (tokenCtorAfterSupplyMap σ I supplyWord)
    (tokenCtorBalanceSlot I) supplyWord

noncomputable def tokenCtorHashMem (I : ExecutionEnv)
    (supplyWord : UInt256) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩ (tokenCtorArgFreeMem supplyWord)

noncomputable def tokenCtorReturnMem (I : ExecutionEnv)
    (supplyWord : UInt256) : ByteArray :=
  (tokenCtorCode supplyWord).write 224 (tokenCtorHashMem I supplyWord) 0 3621

theorem tokenCtorWordAt0_size (I : ExecutionEnv) (supplyWord : UInt256) :
    (wordAt0Mem (solcSourceWord I) (tokenCtorArgFreeMem supplyWord)).size = 160 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le _ _ 0 160 160
    (tokenCtorArgFreeMem_size supplyWord)
    (by rw [tokenCtorArgFreeMem_size]; omega) (by omega)

theorem tokenCtorHashMem_size (I : ExecutionEnv) (supplyWord : UInt256) :
    (tokenCtorHashMem I supplyWord).size = 160 := by
  unfold tokenCtorHashMem twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le _ _ 32 160 160
    (tokenCtorWordAt0_size I supplyWord)
    (by rw [tokenCtorWordAt0_size]; omega) (by omega)

theorem tokenCtorHashMem_read0 (I : ExecutionEnv) (supplyWord : UInt256) :
    (tokenCtorHashMem I supplyWord).readWithPadding 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold tokenCtorHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by rw [tokenCtorWordAt0_size]; omega) (by omega)]
  exact wordAt0Mem_read0 (solcSourceWord I) (tokenCtorArgFreeMem supplyWord)

theorem tokenCtorHashMem_read32 (I : ExecutionEnv) (supplyWord : UInt256) :
    (tokenCtorHashMem I supplyWord).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold tokenCtorHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [tokenCtorWordAt0_size]; omega)]
  exact toByteArray_extract_all ⟨1⟩

theorem tokenCtorHashMem_read0_64 (I : ExecutionEnv) (supplyWord : UInt256) :
    (tokenCtorHashMem I supplyWord).readWithPadding 0 64 =
      UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray ⟨1⟩ := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [tokenCtorHashMem_size]; omega)]
  have hleft : (tokenCtorHashMem I supplyWord).extract 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
    rw [← readWithPadding_eq_extract _ 0
      (by rw [tokenCtorHashMem_size]; omega), tokenCtorHashMem_read0]
  have hright : (tokenCtorHashMem I supplyWord).extract 32 64 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32
      (by rw [tokenCtorHashMem_size]; omega), tokenCtorHashMem_read32]
  rw [show (tokenCtorHashMem I supplyWord).extract 0 64 =
      (tokenCtorHashMem I supplyWord).extract 0 32 ++
        (tokenCtorHashMem I supplyWord).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem tokenCtorHashSlot (I : ExecutionEnv) (supplyWord : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((tokenCtorHashMem I supplyWord).readWithPadding 0 64))) =
      tokenCtorBalanceSlot I := by
  rw [tokenCtorHashMem_read0_64]
  unfold tokenCtorBalanceSlot solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨1⟩

theorem tokenCtorReturnMem_read (I : ExecutionEnv) (supplyWord : UInt256) :
    (tokenCtorReturnMem I supplyWord).readWithPadding 0 3621 = tokenBytecode := by
  unfold tokenCtorReturnMem
  rw [write0_read_back_from_gen (tokenCtorCode supplyWord)
    (tokenCtorHashMem I supplyWord) 224 3621
    (by decide) (by rw [tokenCtorCode_size]; omega)
    (by decide)]
  have hleft : (tokenCtorCode supplyWord).extract 224 (224 + 3621) =
      tokenCreationBytecode.extract 224 (224 + 3621) := by
    unfold tokenCtorCode
    exact extract_append_left tokenCreationBytecode
      (EVM.Word.toBytesBE supplyWord).toByteArray 224 (224 + 3621)
      (by rw [tokenCreationBytecode_size])
  rw [hleft, tokenCreationBytecode_runtime_window]

theorem tokenCtorSupplyStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {k C : Nat} (supplyWord : UInt256)
    (hperm : I.perm = true)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨46⟩ [supplyWord]
      (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5) rdata (cA, σ) k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨53⟩ [supplyWord]
      (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5) rdata
      (cA, tokenCtorAfterSupplyMap σ I supplyWord) k' C' := by
  have rd51 := token_ctor_run h with [jumpdest, dup1, push0, dup2, swap1]
  obtain ⟨_, _, rd52⟩ := rd51.sstore hperm (by token_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd53 := token_ctor_run rd52 with [pop]
  exact ⟨_, _, by simpa [tokenCtorAfterSupplyMap] using rd53⟩

theorem tokenCtorBalanceStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {k C : Nat} (supplyWord : UInt256)
    (hperm : I.perm = true)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨53⟩ [supplyWord]
      (tokenCtorArgFreeMem supplyWord) (UInt256.ofNat 5) rdata
      (cA, tokenCtorAfterSupplyMap σ I supplyWord) k C) :
    ∃ k' C', RD (tokenCtorCode supplyWord) I g s0 ⟨211⟩ []
      (tokenCtorHashMem I supplyWord) (UInt256.ofNat 5) rdata
      (cA, tokenCtorFinalMap σ I supplyWord) k' C' := by
  have hclean := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd103pre := token_ctor_run h with [
    dup1, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and, dup2]
  rw [hclean, hclean] at rd103pre
  have rd104 := rd103pre.mstore 0
    (wordAt0Mem (solcSourceWord I) (tokenCtorArgFreeMem supplyWord))
    (UInt256.ofNat 5) (by token_ctor_decode) mem_cost (by rfl)
    (by decide) (by evm_ov)
  have rd109pre := token_ctor_run rd104 with [push1 ⟨32⟩, add, swap1, dup2]
  have rd110 := rd109pre.mstore 0 (tokenCtorHashMem I supplyWord)
    (UInt256.ofNat 5) (by token_ctor_decode) mem_cost (by rfl)
    (by decide) (by evm_ov)
  have rd114pre := token_ctor_run rd110 with [push1 ⟨32⟩, add, push0]
  have rd115 := rd114pre.keccak256 0 (tokenCtorBalanceSlot I)
    (UInt256.ofNat 5) (by token_ctor_decode) mem_cost
    (tokenCtorHashSlot I supplyWord) (by decide) (by evm_ov)
  have rd117pre := token_ctor_run rd115 with [dup2, swap1]
  obtain ⟨_, _, rd118⟩ := rd117pre.sstore hperm (by token_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd211 := token_ctor_run rd118 with [
    pop, pop, push1 ⟨211⟩, jump (by token_ctor_jd)]
  exact ⟨_, _, by simpa [tokenCtorFinalMap] using rd211⟩

theorem tokenCtorReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {k C : Nat} (supplyWord : UInt256)
    (h : RD (tokenCtorCode supplyWord) I g s0 ⟨211⟩ []
      (tokenCtorHashMem I supplyWord) (UInt256.ofNat 5) rdata
      (cA, tokenCtorFinalMap σ I supplyWord) k C) :
    RDret (tokenCtorCode supplyWord) g s0
      (cA, tokenCtorFinalMap σ I supplyWord) tokenBytecode := by
  have rd221pre := token_ctor_run h with [
    jumpdest, push2 ⟨3621⟩, dup1, push2 ⟨224⟩, push0,
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 0 3621)) -
        Cₘ (UInt256.ofNat 5))
      (tokenCtorReturnMem I supplyWord) (UInt256.ofNat 114)
      (by token_ctor_decode)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push0]
  exact rd221pre.ret 0 tokenBytecode (by token_ctor_decode) mem_cost
    (tokenCtorReturnMem_read I supplyWord) (by evm_ov)

theorem tokenCtorInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (supplyWord : UInt256) (hcode : I.code = tokenCtorCode supplyWord)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    RDret (tokenCtorCode supplyWord) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, tokenCtorFinalMap σ I supplyWord) tokenBytecode := by
  obtain ⟨_, _, rd16⟩ := tokenCtorPayableGuardTrace supplyWord hcode hwv
  obtain ⟨_, _, rd36⟩ := tokenCtorArgCopyTrace supplyWord rd16
  obtain ⟨_, _, rd46⟩ := tokenCtorArgDecodeTrace supplyWord rd36
  obtain ⟨_, _, rd53⟩ := tokenCtorSupplyStoreTrace supplyWord hperm rd46
  obtain ⟨_, _, rd211⟩ := tokenCtorBalanceStoreTrace supplyWord hperm rd53
  exact tokenCtorReturnTrace supplyWord rd211

def tokenCtorLocals (supply : Int) : Store :=
  (∅ : Store).insert "_totalSupply" (.int supply)

def tokenCtorAfterSupplyState (evm : EVM.State) (supplyWord : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ supplyWord

def tokenCtorAfterBalanceState (evm : EVM.State) (supplyWord : UInt256) : EVM.State :=
  Solm.EVM.storageStore (tokenCtorAfterSupplyState evm supplyWord)
    evm.executionEnv.codeOwner (balanceOfSlot (.address evm.executionEnv.source)) supplyWord

theorem tokenCtorLocals_get (supply : Int) :
    (tokenCtorLocals supply).get? "_totalSupply" = some (.int supply) := by
  simp [tokenCtorLocals]

theorem tokenCtorLocals_get_supply (supply : Int) :
    (tokenCtorLocals supply).get? "totalSupply" = none := by
  unfold tokenCtorLocals
  rw [store_get_ne _ _ (by decide)]
  simp

theorem tokenCtorLocals_get_balance (supply : Int) :
    (tokenCtorLocals supply).get? "balanceOf" = none := by
  unfold tokenCtorLocals
  rw [store_get_ne _ _ (by decide)]
  simp

theorem tokenCtorBalanceSlot_eq (I : ExecutionEnv) :
    balanceOfSlot (.address I.source) = tokenCtorBalanceSlot I := by
  unfold tokenCtorBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [tokenSource_keyValueToWord I.source]

theorem tokenCtorAssignSupply (evm : EVM.State) (supply : Int)
    (h0 : 0 ≤ supply) (hlt : supply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? config { contract := contract, locals := tokenCtorLocals supply }
      evm .storage totalSupplyRef (.int supply) =
    .ok ({ contract := contract, locals := tokenCtorLocals supply },
      tokenCtorAfterSupplyState evm (EVM.word supply.toNat)) := by
  have her : evalStorageRef config
      { contract := contract, locals := tokenCtorLocals supply } evm
      totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
    simp [totalSupplyRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := tokenCtorLocals_get_supply supply) (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)
  have hword := constructorUInt256Word_toNat supply h0 hlt
  simpa [tokenCtorAfterSupplyState, hword, Int.toNat_of_nonneg h0] using
    tokenStorageLocStore_uint256 evm ⟨0⟩ (EVM.word supply.toNat)

theorem tokenCtorAssignBalance (evm : EVM.State) (supply : Int)
    (h0 : 0 ≤ supply) (hlt : supply < Int.ofNat (EVM.twoPow 256)) :
    assignStorageRef? config { contract := contract, locals := tokenCtorLocals supply }
      (tokenCtorAfterSupplyState evm (EVM.word supply.toNat))
      .storage (balanceOfRef sender) (.int supply) =
    .ok ({ contract := contract, locals := tokenCtorLocals supply },
      tokenCtorAfterBalanceState evm (EVM.word supply.toNat)) := by
  let evm1 := tokenCtorAfterSupplyState evm (EVM.word supply.toNat)
  have her : evalStorageRef config
      { contract := contract, locals := tokenCtorLocals supply } evm1
      (balanceOfRef sender) =
      .ok { base := "balanceOf", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, envValue, valueToKey?,
      EvalResult.ofOption, EvalResult.bind, pure, bind,
      evm1, tokenCtorAfterSupplyState, storageStore_executionEnv]
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := tokenCtorLocals_get_balance supply) (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := tokenConfig_storage_balanceOf (.address evm.executionEnv.source))
  have hword := constructorUInt256Word_toNat supply h0 hlt
  simpa [tokenCtorAfterBalanceState, evm1, tokenCtorAfterSupplyState,
    storageStore_executionEnv, hword, Int.toNat_of_nonneg h0] using
    tokenStorageLocStore_uint256 evm1
      (balanceOfSlot (.address evm.executionEnv.source)) (EVM.word supply.toNat)

theorem tokenCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (supply : Int) (h0 : 0 ≤ supply)
    (hlt : supply < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm2 := tokenCtorAfterBalanceState evm0 (EVM.word supply.toNat)
    ExecBlock config { contract := contract, locals := tokenCtorLocals supply }
      evm0 constructorDecl.body
      (.ok { contract := contract, locals := tokenCtorLocals supply } evm2) := by
  intro evm0 evm2
  have hassign0 := tokenCtorAssignSupply evm0 supply h0 hlt
  have hassign1 := tokenCtorAssignBalance evm0 supply h0 hlt
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassign0) ?_
  · rw [evalExpr?, tokenCtorLocals_get]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassign1) ExecBlock.nil
  rw [evalExpr?, tokenCtorLocals_get]
  rfl

theorem tokenSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (supply : Int) (h0 : 0 ≤ supply)
    (hlt : supply < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.int supply] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := tokenCtorLocals supply }
        (tokenCtorAfterBalanceState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          (EVM.word supply.toNat)) none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := tokenCtorLocals supply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [tokenCtorLocals, contract, constructorDecl]
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (tokenCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          supply h0 hlt hwv)

theorem tokenSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (supply : Int) (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.int supply] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := tokenCtorLocals supply)
    ?_ rfl ?_ ?_
  · rfl
  · simp [tokenCtorLocals, contract, constructorDecl]
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := tokenCtorLocals supply) hwv

theorem tokenConstructorCorrect :
    constructorEquivalence config tokenCreationBytecode contract tokenBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata hperm hAccounts
  obtain ⟨supply, hargs, h0, hlt, hdeployed⟩ := tokenCtorDeployment_shape hdeploy
  subst args
  have hcode' : I.code = tokenCtorCode (EVM.word supply.toNat) := by
    simpa [tokenCtorCode, hdeployed] using hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := tokenCtorInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (EVM.word supply.toNat) hcode' hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcode'] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcode'] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          tokenCtorFinalMap σ_evm I (EVM.word supply.toNat) :=
        congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s] using
            tokenSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) supply h0 hlt hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [tokenCtorAfterBalanceState, tokenCtorAfterSupplyState,
          storageStore_createdAccounts, initState]
      · simpa [tokenCtorFinalMap, tokenCtorAfterBalanceState,
          tokenCtorAfterSupplyState, tokenCtorBalanceSlot_eq,
          storageStore_accountMap, storageStore_executionEnv, initState] using
          accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
            ⟨0⟩ (EVM.word supply.toNat) (tokenCtorBalanceSlot I)
            (EVM.word supply.toNat) hAccounts
  · have hrd := tokenInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g)
      (EVM.Word.toBytesBE (EVM.word supply.toNat)).toByteArray
      (by simpa [tokenCtorCode] using hcode') hwv
    rcases hrd.xiResult (by simpa [tokenCtorCode] using hcode') with
      hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (tokenSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) supply hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.ActAmmToken
