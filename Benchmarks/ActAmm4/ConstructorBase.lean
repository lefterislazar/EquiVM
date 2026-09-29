import Benchmarks.ActAmm4.Bytecode
import Reasoning.Constructor
import Reasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem amm4CtorEncodedArgs_length
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

theorem amm4CtorDeployment_args_length
    {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment amm4CreationBytecode args =
      some deployedInitcode) :
    args.length = constructorDecl.params.length := by
  change genSolidityConstructorDeployment constructorDecl.params
    amm4CreationBytecode args = some deployedInitcode at hdeploy
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
      have hlen := amm4CtorEncodedArgs_length
        (by simpa [hhead] using hbytes)
      simpa using hlen.symm

theorem amm4CtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment amm4CreationBytecode args =
      some deployedInitcode) :
    ∃ (t0 t1 : AccountAddress) (liquidity : Int),
      args = [.address t0, .address t1, .int liquidity] ∧
      0 ≤ liquidity ∧ liquidity < Int.ofNat (EVM.twoPow 256) ∧
      deployedInitcode = amm4CreationBytecode ++
        (EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
        (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
        (EVM.Word.toBytesBE (EVM.word liquidity.toNat)).toByteArray := by
  have hlen := amm4CtorDeployment_args_length hdeploy
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
    amm4CreationBytecode [a, b, c] = some deployedInitcode at hdeploy
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

theorem amm4CreationBytecode_size : amm4CreationBytecode.size = 8188 := by
  native_decide

theorem amm4Creation_runtime_window :
    amm4CreationBytecode.extract 1858 (1858 + 6330) = amm4Bytecode := by
  native_decide

noncomputable def amm4CtorArgTail (t0 t1 : AccountAddress) (liquidity : UInt256) :
    ByteArray :=
  (EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
    (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
    (EVM.Word.toBytesBE liquidity).toByteArray

noncomputable def amm4CtorCode (t0 t1 : AccountAddress) (liquidity : UInt256) :
    ByteArray :=
  amm4CreationBytecode ++ amm4CtorArgTail t0 t1 liquidity

theorem amm4CtorArgTail_size (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorArgTail t0 t1 liquidity).size = 96 := by
  unfold amm4CtorArgTail
  rw [ByteArray.size_append, ByteArray.size_append, word_toBytesBE_toByteArray_size,
    word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

theorem amm4CtorCode_size (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).size = 8284 := by
  rw [amm4CtorCode, ByteArray.size_append, amm4CreationBytecode_size,
    amm4CtorArgTail_size]

theorem amm4CtorCode_runtime_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).extract 1858 (1858 + 6330) =
      amm4Bytecode := by
  rw [amm4CtorCode]
  rw [extract_append_left amm4CreationBytecode (amm4CtorArgTail t0 t1 liquidity)
    1858 (1858 + 6330) (by rw [amm4CreationBytecode_size])]
  exact amm4Creation_runtime_window

theorem amm4CtorArg0_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).extract 8188 (8188 + 32) =
      (EVM.Word.toBytesBE (EVM.word t0)).toByteArray := by
  unfold amm4CtorCode amm4CtorArgTail
  rw [extract_append_right_window amm4CreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8188 (8188 + 32)
    (by rw [amm4CreationBytecode_size])]
  simp only [amm4CreationBytecode_size, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [ByteArray.append_assoc]
  rw [extract_append_left (EVM.Word.toBytesBE (EVM.word t0)).toByteArray
    ((EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 0 32
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 = (EVM.Word.toBytesBE (EVM.word t0)).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem amm4CtorArg1_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).extract 8220 (8220 + 32) =
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray := by
  unfold amm4CtorCode amm4CtorArgTail
  rw [extract_append_right_window amm4CreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8220 (8220 + 32)
    (by rw [amm4CreationBytecode_size]; omega)]
  simp only [amm4CreationBytecode_size]
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

theorem amm4CtorArg2_extract (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).extract 8252 (8252 + 32) =
      (EVM.Word.toBytesBE liquidity).toByteArray := by
  unfold amm4CtorCode amm4CtorArgTail
  rw [extract_append_right_window amm4CreationBytecode
    ((EVM.Word.toBytesBE (EVM.word t0)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word t1)).toByteArray ++
      (EVM.Word.toBytesBE liquidity).toByteArray) 8252 (8252 + 32)
    (by rw [amm4CreationBytecode_size]; omega)]
  simp only [amm4CreationBytecode_size]
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

theorem amm4CtorCode_tail_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorCode t0 t1 liquidity).extract 8188 (8188 + 96) =
      amm4CtorArgTail t0 t1 liquidity := by
  rw [amm4CtorCode]
  rw [extract_append_right_window amm4CreationBytecode
    (amm4CtorArgTail t0 t1 liquidity) 8188 (8188 + 96)
    (by rw [amm4CreationBytecode_size])]
  simp only [amm4CreationBytecode_size, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [← amm4CtorArgTail_size t0 t1 liquidity]
  exact byteArray_extract_self _

theorem amm4Creation_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 8156) :
    decode (amm4CreationBytecode ++ tail) pc = decode amm4CreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window amm4CreationBytecode tail pc
    (by rw [amm4CreationBytecode_size]; omega)
    (by rw [amm4CreationBytecode_size]; norm_num)

end Benchmarks.ActAmm4
