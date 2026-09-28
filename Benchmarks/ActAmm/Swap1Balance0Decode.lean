import Benchmarks.ActAmm.Swap1Balance0Failure
import Benchmarks.ActAmm.BurnBalance0Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1Balance0PostCallMem_size_ge (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretSize : ret.size < UInt256.size) :
    (ammMintToken0FreePtr out).toNat + 36 ≤
      (ammSwap1Balance0PostCallMem I out ret).size := by
  unfold ammSwap1Balance0PostCallMem
  have hbase := ammSwap1Balance0CalldataMem_size I hlo hbound
  by_cases hshort : ret.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat =
        ret.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := ret.size)
        (by decide) hshort hretSize
    rw [hlen]
    by_cases hzero : ret.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen ret (ammSwap1Balance0CalldataMem I out)
        (ammMintToken0FreePtr out).toNat ret.size hzero le_rfl
        (by omega), ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ ret.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := ret.size)
        (by decide) hlong hretSize
    rw [hlen]
    rw [write_eq_gen ret (ammSwap1Balance0CalldataMem I out)
      (ammMintToken0FreePtr out).toNat 32
      (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem ammSwap1Balance0PostCallMem_read64 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretSize : ret.size < UInt256.size) :
    (ammSwap1Balance0PostCallMem I out ret).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr out) := by
  unfold ammSwap1Balance0PostCallMem
  have hbase := ammSwap1Balance0CalldataMem_size I hlo hbound
  have hptr := (ammMintToken0FreePtr_bounds out hlo hbound).1
  change 160 ≤ (ammMintToken0FreePtr out).toNat at hptr
  by_cases hshort : ret.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat =
        ret.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := ret.size)
        (by decide) hshort hretSize
    rw [hlen]
    by_cases hzero : ret.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammSwap1Balance0CalldataMem_read64 I hlo hbound
    · rw [write_read_below_gen ret
        (ammSwap1Balance0CalldataMem I out)
        (ammMintToken0FreePtr out).toNat ret.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact ammSwap1Balance0CalldataMem_read64 I hlo hbound
  · have hlong : 32 ≤ ret.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := ret.size)
        (by decide) hlong hretSize
    rw [hlen]
    rw [write32_read_below ret
      (ammSwap1Balance0CalldataMem I out)
      (ammMintToken0FreePtr out).toNat 64 hlong
      (by omega) (by omega)]
    exact ammSwap1Balance0CalldataMem_read64 I hlo hbound

theorem ammSwap1Balance0PostCallMem_readPtr (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretSize : ret.size < UInt256.size) :
    (ammSwap1Balance0PostCallMem I out ret).readWithPadding
      (ammMintToken0FreePtr out).toNat 32 = ret.extract 0 32 := by
  unfold ammSwap1Balance0PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat =
      32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret.size)
      (by decide) hretLo hretSize
  rw [hlen]
  exact write32_read_back ret (ammSwap1Balance0CalldataMem I out)
    (ammMintToken0FreePtr out).toNat hretLo (by
      have h := ammSwap1Balance0CalldataMem_size I hlo hbound
      omega)

noncomputable def ammSwap1Balance0DecodeMem
    (I : ExecutionEnv) (out ret : ByteArray) : ByteArray :=
  (UInt256.add (ammMintToken0FreePtr out)
    (ammMintReturndataRounded ret)).toByteArray.write 0
    (ammSwap1Balance0PostCallMem I out ret) 64 32

theorem ammSwap1Balance0DecodeMem_size_ge (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretSize : ret.size < UInt256.size) :
    (ammMintToken0FreePtr out).toNat + 36 ≤
      (ammSwap1Balance0DecodeMem I out ret).size := by
  unfold ammSwap1Balance0DecodeMem
  let base := ammSwap1Balance0PostCallMem I out ret
  have hbase : (ammMintToken0FreePtr out).toNat + 36 ≤ base.size :=
    ammSwap1Balance0PostCallMem_size_ge I hlo hbound hretSize
  have hptr := (ammMintToken0FreePtr_bounds out hlo hbound).1
  change 160 ≤ (ammMintToken0FreePtr out).toNat at hptr
  have hsz : ((UInt256.add (ammMintToken0FreePtr out)
      (ammMintReturndataRounded ret)).toByteArray.write 0 base 64 32).size =
      base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem ammSwap1Balance0DecodeMem_readPtr (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretSize : ret.size < UInt256.size) :
    (ammSwap1Balance0DecodeMem I out ret).readWithPadding
      (ammMintToken0FreePtr out).toNat 32 = ret.extract 0 32 := by
  unfold ammSwap1Balance0DecodeMem
  have hbase := ammSwap1Balance0PostCallMem_size_ge I
    hlo hbound hretSize
  have hptr := (ammMintToken0FreePtr_bounds out hlo hbound).1
  change 160 ≤ (ammMintToken0FreePtr out).toNat at hptr
  rw [write32_read_above _ _ 64 (ammMintToken0FreePtr out).toNat
    (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  exact ammSwap1Balance0PostCallMem_readPtr I
    hlo hbound hretLo hretSize

theorem ammSwap1X_balance0ToDecoder
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretSize : ret.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3210⟩
      [⟨0⟩, ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0PostCallMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammMintToken0FreePtr out,
        UInt256.add (ammMintToken0FreePtr out)
          (UInt256.ofNat ret.size),
        ⟨3241⟩, ⟨0⟩, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k' C' := by
  let aw := ammSwap1Balance0CalldataWords out
  let fp := ammMintToken0FreePtr out
  have haw : aw.toNat = max 7 (6 + (out.size + 31) / 32) := by
    simpa only [aw] using
      ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle : (out.size + 31) / 32 ≤ out.size + 31 :=
      Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hmem : 64 <
      (ammSwap1Balance0PostCallMem I out ret).size := by
    have hsz := ammSwap1Balance0PostCallMem_size_ge I
      hlo hbound hretSize
    have hptr := (ammMintToken0FreePtr_bounds out hlo hbound).1
    change 160 ≤ (ammMintToken0FreePtr out).toNat at hptr
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap1Balance0PostCallMem I out ret).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1Balance0PostCallMem I out ret).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammSwap1Balance0PostCallMem_read64 I
          (out := out) (ret := ret) hlo hbound hretSize))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd1399 := evm_run rd with [push1 ⟨64⟩]
  have rd1400 := RD.mload 0 fp aw rd1399 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap1Balance0CalldataWords out).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammSwap1Balance0CalldataWords out from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1414 := evm_run rd1400 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1415 := RD.mstore 0
    (ammSwap1Balance0DecodeMem I out ret) aw rd1414
    (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap1Balance0CalldataWords out).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammSwap1Balance0CalldataWords out from by
        simpa only [aw] using hsame]
      simp only [aw]
      omega)
    (by unfold ammSwap1Balance0DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6453 := evm_run rd1415 with [
    pop, dup2, add, swap1, push2 ⟨3241⟩, swap2, swap1,
    push2 ⟨6453⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, ammMintReturndataRounded]
    using rd6453⟩

theorem ammSwap1Balance0LenCheckShort
    (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hshort : ret.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammMintToken0FreePtr out)
          (UInt256.ofNat ret.size))
        (ammMintToken0FreePtr out)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (ammMintToken0FreePtr_bounds out hlo hbound).2
  change (ammMintToken0FreePtr out).toNat ≤ out.size + 159 at hptr
  have hcheck := solcReturnStaticLenCheckShort
    (base := (ammMintToken0FreePtr out).toNat)
    (len := ret.size) (words := 1)
    (by simpa using hshort)
    (ammMintToken0FreePtr out).val.isLt
    (by
      have hcap : 2 ^ 138 + 159 + 32 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammSwap1X_balance0DecodeShortReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hshort : ret.size < 32)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammMintToken0FreePtr out,
        UInt256.add (ammMintToken0FreePtr out)
          (UInt256.ofNat ret.size),
        ⟨3241⟩, ⟨0⟩, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := ammSwap1Balance0LenCheckShort out ret
    hlo hbound hshort
  have rd6462 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6462 with [
    push2 ⟨6474⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6473⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammSwap1Balance0DecodeRevertBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA1 cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σS1 σE2 : AccountMap} {A1 A2 : Substate}
    {ret : ByteArray} {b : Bool}
    (hcode : I.code = ammBytecode)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ammSwap1SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap1AfterTransferStore I b }
        { initState cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σS1, substate := A1,
          createdAccounts := cA1 }))
    (hσ1 : accountMapEquiv σE1 σS1)
    (hcallE : typedCallViaEVM config
      { initState cA1 gh bl σE1 σ₀ (Sat256.ofUInt256 g) A1 I with
        accountMap := σE1 }
      (AccountAddress.ofUInt256 (ammMintToken0Word σE1 I))
      "balanceOf" 0 [.address I.codeOwner]
      (true, { initState cA1 gh bl σE1 σ₀
          (Sat256.ofUInt256 g) A1 I with
          accountMap := σE2, substate := A2, createdAccounts := cA2 }, ret)
      false)
    (hdec : config.externalABI.decode? "balanceOf" ret = none)
    (hrev : RDrev ammBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  obtain ⟨σS2, hcallS, hσ2⟩ :=
    ammSwap1TransportBalance0Call (cA := cA) (σ_solm := σ_solm)
      (A := A) hσ1 hcallE
  have hbody := ammSwap1SourceBalance0DecodeRevert I b ret
    hprefix hcallS hdec
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

theorem ammSwap1Balance0LenCheckOk
    (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammMintToken0FreePtr out)
          (UInt256.ofNat ret.size))
        (ammMintToken0FreePtr out)) ⟨32⟩ = ⟨0⟩ := by
  have hptr0 := ammMintToken0FreePtr_toNat out hbound
  have hptr : (ammMintToken0FreePtr out).toNat < 2 ^ 140 := by
    have hle : (out.size + 31) / 32 ≤ out.size + 31 :=
      Nat.div_le_self _ _
    change (ammMintToken0FreePtr out).toNat =
      128 + 32 * ((out.size + 31) / 32) at hptr0
    rw [hptr0]
    omega
  have hcheck := solcReturnStaticLenCheckOk
    (base := (ammMintToken0FreePtr out).toNat)
    (len := ret.size) (words := 1)
    (by simpa using hretLo)
    (by omega : ret.size < 2 ^ 255)
    (ammMintToken0FreePtr out).val.isLt
    (by
      have hcap : 2 ^ 140 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammSwap1Balance0CalldataWords_ptr_haw (out : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    ¬ ammMintToken0FreePtr out ≥
      ammSwap1Balance0CalldataWords out * ⟨32⟩ := by
  let n := (out.size + 31) / 32
  have hptr : (ammMintToken0FreePtr out).toNat =
      128 + 32 * n := by
    simpa only [n, ammMintToken0FreePtr] using
      ammMintToken0FreePtr_toNat out hbound
  have haw : (ammSwap1Balance0CalldataWords out).toNat =
      max 7 (6 + n) := by
    simpa only [n] using
      ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hmul : (ammSwap1Balance0CalldataWords out).toNat * 32 <
      UInt256.size := by
    have hle : n ≤ out.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    rw [haw]
    omega
  intro h
  have hle : (ammSwap1Balance0CalldataWords out * ⟨32⟩).toNat ≤
      (ammMintToken0FreePtr out).toNat := h
  rw [u256_mul_op_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem ammSwap1Balance0CalldataWords_mloadPtr_same (out : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (ammSwap1Balance0CalldataWords out).toNat
      (ammMintToken0FreePtr out).toNat 32) =
      ammSwap1Balance0CalldataWords out := by
  let n := (out.size + 31) / 32
  have hptr : (ammMintToken0FreePtr out).toNat =
      128 + 32 * n := by
    simpa only [n, ammMintToken0FreePtr] using
      ammMintToken0FreePtr_toNat out hbound
  have haw : (ammSwap1Balance0CalldataWords out).toNat =
      max 7 (6 + n) := by
    simpa only [n] using
      ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hM : MachineState.M (ammSwap1Balance0CalldataWords out).toNat
      (ammMintToken0FreePtr out).toNat 32 =
      (ammSwap1Balance0CalldataWords out).toNat := by
    change max (ammSwap1Balance0CalldataWords out).toNat
      (((ammMintToken0FreePtr out).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammSwap1X_balance0DecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammMintToken0FreePtr out,
        UInt256.add (ammMintToken0FreePtr out)
          (UInt256.ofNat ret.size),
        ⟨3241⟩, ⟨0⟩, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3244⟩
      [UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k' C' := by
  let aw := ammSwap1Balance0CalldataWords out
  let fp := ammMintToken0FreePtr out
  let v : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (ret.extract 0 32))
  have hcheck := ammSwap1Balance0LenCheckOk out ret
    hlo hbound hretLo hretBound
  have rd6474 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6474⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6433 := evm_run rd6474 with [
    jumpdest, push0, push2 ⟨6487⟩, dup5, dup3, dup6, add,
    push2 ⟨6433⟩, jump (by jump_dest)]
  have hmem : fp.toNat <
      (ammSwap1Balance0DecodeMem I out ret).size := by
    have hsz := ammSwap1Balance0DecodeMem_size_ge I
      hlo hbound
      (lt_trans hretBound (by norm_num [UInt256.size]))
    dsimp [fp]
    omega
  have hval :
      (if fp.toNat ≥ (ammSwap1Balance0DecodeMem I out ret).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1Balance0DecodeMem I out ret).readWithPadding
           fp.toNat 32))) = v := by
    have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
      simpa only [fp, aw] using
        ammSwap1Balance0CalldataWords_ptr_haw out hlo hbound
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
      ammSwap1Balance0DecodeMem_readPtr I
        hlo hbound hretLo
        (lt_trans hretBound (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      ammSwap1Balance0CalldataWords_mloadPtr_same out hlo hbound
  have rd6436 := evm_run rd6433 with [jumpdest, push0, dup2]
  have hzero : ammMintToken0FreePtr out + ⟨0⟩ =
      ammMintToken0FreePtr out := by
    rw [u256_add_comm, u256_zero_add]
  have rd6436' := rd6436
  rw [hzero] at rd6436'
  have rd6437 := RD.mload 0 v aw rd6436' (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap1Balance0CalldataWords out).toNat
          (ammMintToken0FreePtr out).toNat 32) =
            ammSwap1Balance0CalldataWords out from by
          simpa only [aw, fp] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5499 := evm_run rd6437 with [
    swap1, pop, push2 ⟨6447⟩, dup2, push2 ⟨5499⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd6447⟩ := RD.ammCheckUint256Identity rd5499
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6487 := evm_run rd6447 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1428 := evm_run rd6487 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  have rd1431 := evm_run rd1428 with [jumpdest, swap1, pop]
  exact ⟨_, _, by simpa only [v, aw, fp] using rd1431⟩

end Benchmarks.ActAmm
