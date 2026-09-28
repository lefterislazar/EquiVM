import Benchmarks.ActAmm.Bytecode
import Reasoning.Constructor
import Reasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem ammCtorEncodedArgs_length
    {tys : List ABIType} {vals : List Value}
    {headSize : Nat} {head tail bytes : List UInt8}
    (h : encodeABIValuesFrom? tys vals headSize head tail = some bytes) :
    tys.length = vals.length := by
  induction tys generalizing vals head tail with
  | nil =>
      cases vals with
      | nil => rfl
      | cons _ _ => simp [encodeABIValuesFrom?] at h
  | cons ty tys ih =>
      cases vals with
      | nil => simp [encodeABIValuesFrom?] at h
      | cons val vals =>
          have hval : ∃ encoded, encodeABIValue? ty val = some encoded := by
            by_cases hv : encodeABIValue? ty val = none
            · simp [encodeABIValuesFrom?, hv] at h
            · cases he : encodeABIValue? ty val with
              | none => exact False.elim (hv he)
              | some encoded => exact ⟨encoded, rfl⟩
          obtain ⟨encoded, hencoded⟩ := hval
          by_cases hd : isDynamicABIType ty
          · have hrest : encodeABIValuesFrom? tys vals headSize
                (head ++ natBytes (headSize + tail.length))
                (tail ++ encoded) = some bytes := by
              simpa [encodeABIValuesFrom?, hencoded, hd] using h
            simpa using congrArg Nat.succ (ih hrest)
          · have hrest : encodeABIValuesFrom? tys vals headSize
                (head ++ encoded) tail = some bytes := by
              simpa [encodeABIValuesFrom?, hencoded, hd] using h
            simpa using congrArg Nat.succ (ih hrest)

theorem ammCtorDeployment_args_length
    {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment ammCreationBytecode args =
      some deployedInitcode) :
    args.length = constructorDecl.params.length := by
  change genSolidityConstructorDeployment constructorDecl.params
    ammCreationBytecode args = some deployedInitcode at hdeploy
  unfold genSolidityConstructorDeployment at hdeploy
  obtain ⟨bytes, hbytes⟩ : ∃ bytes,
      encodeABIValues? (constructorDecl.params.map Param.ty) args =
        some bytes := by
    cases h : encodeABIValues? (constructorDecl.params.map Param.ty) args with
    | none => simp [h] at hdeploy
    | some bytes => exact ⟨bytes, rfl⟩
  unfold encodeABIValues? at hbytes
  cases hhead : abiTupleHeadSize? (constructorDecl.params.map Param.ty) with
  | none => simp [hhead] at hbytes
  | some headSize =>
      have hlen := ammCtorEncodedArgs_length
        (by simpa [hhead] using hbytes)
      simpa using hlen.symm

theorem ammCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment ammCreationBytecode args =
      some deployedInitcode) :
    ∃ (t0 t1 : AccountAddress) (liquidity : Int),
      args = [.address t0, .address t1, .int liquidity] ∧
      0 ≤ liquidity ∧ liquidity < Int.ofNat (EVM.twoPow 256) ∧
      deployedInitcode = ammCreationBytecode ++
        (EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
        (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
        (EVM.Word.toBytesBE (EVM.word liquidity.toNat)).toByteArray := by
  have hlen := ammCtorDeployment_args_length hdeploy
  change args.length = 3 at hlen
  obtain ⟨a, b, c, hargs⟩ : ∃ a b c, args = [a, b, c] := by
    cases args with
    | nil => simp at hlen
    | cons a rest =>
        cases rest with
        | nil => simp at hlen
        | cons b rest =>
            cases rest with
            | nil => simp at hlen
            | cons c rest =>
                cases rest with
                | nil => exact ⟨a, b, c, rfl⟩
                | cons d rest => simp at hlen
  subst args
  change genSolidityConstructorDeployment
    [{ name := "t0", ty := addr }, { name := "t1", ty := addr },
      { name := "liquidity", ty := uint256 }]
    ammCreationBytecode [a, b, c] = some deployedInitcode at hdeploy
  obtain ⟨bytes, henc⟩ : ∃ bytes,
      encodeABIValues? [addr, addr, uint256] [a, b, c] = some bytes := by
    unfold genSolidityConstructorDeployment at hdeploy
    cases he : encodeABIValues? [addr, addr, uint256] [a, b, c] with
    | none => simp [he] at hdeploy
    | some bytes => exact ⟨bytes, rfl⟩
  have ha : ∃ t0, a = .address t0 := by
    cases a <;> first
      | exact ⟨_, rfl⟩
      | simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
          encodeABIWord?, uint256, uint256Int, addr] at henc
  obtain ⟨t0, rfl⟩ := ha
  have hb : ∃ t1, b = .address t1 := by
    cases b <;> first
      | exact ⟨_, rfl⟩
      | simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
          encodeABIWord?, uint256, uint256Int, addr] at henc
  obtain ⟨t1, rfl⟩ := hb
  have hc : ∃ liquidity, c = .int liquidity := by
    cases c <;> first
      | exact ⟨_, rfl⟩
      | simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
          staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
          encodeABIWord?, uint256, uint256Int, addr] at henc
  obtain ⟨liquidity, rfl⟩ := hc
  simp [encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
    encodeABIWord?, uint256, uint256Int, addr] at henc
  split_ifs at henc with hbound
  · have hliq : 0 ≤ liquidity ∧ liquidity < Int.ofNat (EVM.twoPow 256) := by
      simpa using hbound
    refine ⟨t0, t1, liquidity, rfl, hliq.1, hliq.2, ?_⟩
    simp [genSolidityConstructorDeployment,
      encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
      staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
      encodeABIWord?, uint256, uint256Int, addr,
      ByteArray.append_assoc] at hdeploy ⊢
    split_ifs at hdeploy
    · simp at hdeploy
      simpa [ByteArray.append_assoc] using hdeploy.symm
  · simp at henc

theorem ammCreationBytecode_size : ammCreationBytecode.size = 8921 := by
  native_decide

theorem ammCreation_runtime_window :
    ammCreationBytecode.extract 1858 (1858 + 7063) = ammBytecode := by
  native_decide

noncomputable def ammCtorArgTail (t0 t1 : AccountAddress) (liquidity : UInt256) :
    ByteArray :=
  (EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
    (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
    (EVM.Word.toBytesBE liquidity).toByteArray

noncomputable def ammCtorCode (t0 t1 : AccountAddress) (liquidity : UInt256) :
    ByteArray :=
  ammCreationBytecode ++ ammCtorArgTail t0 t1 liquidity

theorem ammCtorArgTail_size (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorArgTail t0 t1 liquidity).size = 96 := by
  unfold ammCtorArgTail
  rw [ByteArray.size_append, ByteArray.size_append, word_toBytesBE_toByteArray_size,
    word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

theorem ammCtorCode_size (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).size = 9017 := by
  rw [ammCtorCode, ByteArray.size_append, ammCreationBytecode_size,
    ammCtorArgTail_size]

theorem ammCtorCode_runtime_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).extract 1858 (1858 + 7063) =
      ammBytecode := by
  rw [ammCtorCode]
  rw [extract_append_left ammCreationBytecode (ammCtorArgTail t0 t1 liquidity)
    1858 (1858 + 7063) (by rw [ammCreationBytecode_size])]
  exact ammCreation_runtime_window

theorem ammCtorArg0_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).extract 8921 (8921 + 32) =
      (EVM.Word.toBytesBE (EVM.word t0)).toByteArray := by
  unfold ammCtorCode ammCtorArgTail
  rw [extract_append_right_window ammCreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8921 (8921 + 32)
    (by rw [ammCreationBytecode_size])]
  simp only [ammCreationBytecode_size, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [ByteArray.append_assoc]
  rw [extract_append_left (EVM.Word.toBytesBE (EVM.word t0)).toByteArray
    ((EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 0 32
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 = (EVM.Word.toBytesBE (EVM.word t0)).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem ammCtorArg1_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).extract 8953 (8953 + 32) =
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray := by
  unfold ammCtorCode ammCtorArgTail
  rw [extract_append_right_window ammCreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8953 (8953 + 32)
    (by rw [ammCreationBytecode_size]; omega)]
  simp only [ammCreationBytecode_size]
  norm_num
  rw [extract_append_left
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray)
    (EVM.Word.toBytesBE liquidity).toByteArray 32 64
    (by rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])]
  rw [extract_append_right_window (EVM.Word.toBytesBE (EVM.word t0)).toByteArray
    (EVM.Word.toBytesBE (EVM.word t1)).toByteArray 32 64
    (by rw [word_toBytesBE_toByteArray_size])]
  simp only [word_toBytesBE_toByteArray_size, Nat.sub_self]
  norm_num
  rw [show 32 = (EVM.Word.toBytesBE (EVM.word t1)).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem ammCtorArg2_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).extract 8985 (8985 + 32) =
      (EVM.Word.toBytesBE liquidity).toByteArray := by
  unfold ammCtorCode ammCtorArgTail
  rw [extract_append_right_window ammCreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8985 (8985 + 32)
    (by rw [ammCreationBytecode_size]; omega)]
  simp only [ammCreationBytecode_size]
  norm_num
  rw [extract_append_right_window
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray)
    (EVM.Word.toBytesBE liquidity).toByteArray 64 96
    (by rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])]
  simp only [ByteArray.size_append, word_toBytesBE_toByteArray_size]
  norm_num
  rw [show 32 = (EVM.Word.toBytesBE liquidity).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem ammCtorCode_tail_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (ammCtorCode t0 t1 liquidity).extract 8921 (8921 + 96) =
      ammCtorArgTail t0 t1 liquidity := by
  rw [ammCtorCode]
  rw [extract_append_right_window ammCreationBytecode
    (ammCtorArgTail t0 t1 liquidity) 8921 (8921 + 96)
    (by rw [ammCreationBytecode_size])]
  simp only [ammCreationBytecode_size, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [← ammCtorArgTail_size t0 t1 liquidity]
  exact byteArray_extract_self _

theorem ammCreation_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 8889) :
    decode (ammCreationBytecode ++ tail) pc = decode ammCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window ammCreationBytecode tail pc
    (by rw [ammCreationBytecode_size]; omega)
    (by rw [ammCreationBytecode_size]; norm_num)

end Benchmarks.ActAmm
