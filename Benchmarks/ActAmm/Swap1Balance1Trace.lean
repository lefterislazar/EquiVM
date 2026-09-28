import Benchmarks.ActAmm.Swap1Balance0Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_balance1Address
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3244⟩
      [UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3301⟩
      [ammMintToken1Word acc.2 I, ⟨0⟩,
        UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k' C' := by
  have rd1436 := evm_run rd with [
    push0, push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd1437⟩ := rd1436.sload
    (by native_decide) (by evm_ov)
  have rd1488 := evm_run rd1437 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken1Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd1488⟩

abbrev ammSwap1Balance1FreePtr (out ret : ByteArray) : UInt256 :=
  UInt256.add (ammMintToken0FreePtr out)
    (ammMintReturndataRounded ret)

theorem ammSwap1Balance1FreePtr_toNat (out ret : ByteArray)
    (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1FreePtr out ret).toNat =
      128 + 32 * ((out.size + 31) / 32 +
        (ret.size + 31) / 32) := by
  have hfp := ammMintToken0FreePtr_toNat out hbound
  have hround := ammMintReturndataRounded_toNat ret hretBound
  have hle0 : (out.size + 31) / 32 ≤ out.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 :=
    Nat.div_le_self _ _
  have hfit : (ammMintToken0FreePtr out).toNat +
      (ammMintReturndataRounded ret).toNat < UInt256.size := by
    rw [show (ammMintToken0FreePtr out).toNat =
      128 + 32 * ((out.size + 31) / 32) from by
        simpa only [ammMintToken0FreePtr] using hfp,
      hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  change (ammMintToken0FreePtr out +
    ammMintReturndataRounded ret).toNat = _
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit,
    show (ammMintToken0FreePtr out).toNat =
      128 + 32 * ((out.size + 31) / 32) from by
        simpa only [ammMintToken0FreePtr] using hfp,
    hround]
  omega

theorem ammSwap1Balance1FreePtr_bounds (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    160 ≤ (ammSwap1Balance1FreePtr out ret).toNat ∧
    (ammSwap1Balance1FreePtr out ret).toNat + 36 < UInt256.size := by
  have hptr := ammSwap1Balance1FreePtr_toNat out ret
    hbound hretBound
  have hle0 : (out.size + 31) / 32 ≤ out.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 :=
    Nat.div_le_self _ _
  have hn0 : 1 ≤ (out.size + 31) / 32 := by omega
  have hcap : 128 + 32 *
      (2 ^ 138 + 31 + 2 ^ 138 + 31) + 36 <
      UInt256.size := by norm_num [UInt256.size]
  constructor <;> omega

theorem ammSwap1Balance0DecodeMem_read64 (I : ExecutionEnv)
    (out ret : ByteArray) :
    (ammSwap1Balance0DecodeMem I out ret).readWithPadding
      64 32 = UInt256.toByteArray (ammSwap1Balance1FreePtr out ret) := by
  unfold ammSwap1Balance0DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

noncomputable def ammSwap1Balance1SelectorMem
    (I : ExecutionEnv) (out ret : ByteArray) : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0
    (ammSwap1Balance0DecodeMem I out ret)
    (ammSwap1Balance1FreePtr out ret).toNat 32

def ammSwap1Balance1SelectorWords (out ret : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammSwap1Balance0CalldataWords out).toNat
    (ammSwap1Balance1FreePtr out ret).toNat 32)

theorem ammSwap1X_balance1SelectorMem
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3301⟩
      [ammMintToken1Word acc.2 I, ⟨0⟩,
        UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0DecodeMem I out ret)
      (ammSwap1Balance0CalldataWords out) ret acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3322⟩
      [ammSwap1Balance1FreePtr out ret, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken1Word acc.2 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1SelectorMem I out ret)
      (ammSwap1Balance1SelectorWords out ret)
      ret acc k' C' := by
  let aw := ammSwap1Balance0CalldataWords out
  let fp := ammSwap1Balance1FreePtr out ret
  let awSel := ammSwap1Balance1SelectorWords out ret
  have hmem : 64 <
      (ammSwap1Balance0DecodeMem I out ret).size := by
    have hsz := ammSwap1Balance0DecodeMem_size_ge I
      hlo hbound
      (lt_trans hretBound (by norm_num [UInt256.size]))
    have hfp := (ammMintToken0FreePtr_bounds out hlo hbound).1
    change 160 ≤ (ammMintToken0FreePtr out).toNat at hfp
    omega
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
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap1Balance0DecodeMem I out ret).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1Balance0DecodeMem I out ret).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using ammSwap1Balance0DecodeMem_read64 I out ret)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd1496 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1497 := RD.mload 0 fp aw rd1496 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS,
        hstk, List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap1Balance0CalldataWords out).toNat
          (⟨64⟩ : UInt256).toNat 32) =
          ammSwap1Balance0CalldataWords out from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1508 := evm_run rd1497 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd1509 := RD.mstore
    (Cₘ awSel - Cₘ aw)
    (ammSwap1Balance1SelectorMem I out ret) awSel rd1508
    (by native_decide)
    (by
      intro s hawS hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS,
        hstk, awSel, aw, fp, ammSwap1Balance1SelectorWords])
    (by unfold ammSwap1Balance1SelectorMem; rfl)
    (by simp [awSel, aw, fp, ammSwap1Balance1SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [ammMintBalanceSelectorWord, fp, awSel] using rd1509⟩

noncomputable def ammSwap1Balance1CalldataMem
    (I : ExecutionEnv) (out ret : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (ammSwap1Balance1SelectorMem I out ret)
    (ammSwap1Balance1FreePtr out ret + ⟨4⟩).toNat 32

def ammSwap1Balance1CalldataWords (out ret : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammSwap1Balance1SelectorWords out ret).toNat
    (ammSwap1Balance1FreePtr out ret + ⟨4⟩).toNat 32)

theorem ammSwap1Balance1CalldataWords_toNat (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1CalldataWords out ret).toNat =
      6 + (out.size + 31) / 32 + (ret.size + 31) / 32 := by
  let n0 := (out.size + 31) / 32
  let n1 := (ret.size + 31) / 32
  let fp := ammSwap1Balance1FreePtr out ret
  let aw0 := ammSwap1Balance0CalldataWords out
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    simpa only [fp, n0, n1] using
      ammSwap1Balance1FreePtr_toNat out ret hbound hretBound
  have haw0 : aw0.toNat = max 7 (6 + n0) := by
    simpa only [aw0, n0] using
      ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hn0 : 1 ≤ n0 := by dsimp [n0]; omega
  have hn1 : 1 ≤ n1 := by dsimp [n1]; omega
  have haw0' : aw0.toNat = 6 + n0 := by rw [haw0]; omega
  have hfit := (ammSwap1Balance1FreePtr_bounds out ret
    hlo hbound hretBound).2
  change fp.toNat + 36 < UInt256.size at hfit
  have hfp4 : (fp + ⟨4⟩).toNat = fp.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hSel : (ammSwap1Balance1SelectorWords out ret).toNat =
      5 + n0 + n1 := by
    unfold ammSwap1Balance1SelectorWords
    rw [hfp, haw0']
    change (UInt256.ofNat
      (max (6 + n0)
        ((128 + 32 * (n0 + n1) + 32 + 31) / 32))).toNat = _
    have hle0 : n0 ≤ out.size + 31 := Nat.div_le_self _ _
    have hle1 : n1 ≤ ret.size + 31 := Nat.div_le_self _ _
    have hcap : 6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 <
      UInt256.size := by norm_num [UInt256.size]
    rw [show max (6 + n0)
        ((128 + 32 * (n0 + n1) + 32 + 31) / 32) =
        5 + n0 + n1 by omega,
      UInt256.toNat_ofNat_of_lt (by omega)]
  unfold ammSwap1Balance1CalldataWords
  rw [hfp4, hfp, hSel]
  change (UInt256.ofNat
    (max (5 + n0 + n1)
      ((128 + 32 * (n0 + n1) + 4 + 32 + 31) / 32))).toNat = _
  have hle0 : n0 ≤ out.size + 31 := Nat.div_le_self _ _
  have hle1 : n1 ≤ ret.size + 31 := Nat.div_le_self _ _
  have hcap : 6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 <
    UInt256.size := by norm_num [UInt256.size]
  rw [show max (5 + n0 + n1)
      ((128 + 32 * (n0 + n1) + 4 + 32 + 31) / 32) =
      6 + n0 + n1 by omega,
    UInt256.toNat_ofNat_of_lt (by omega)]

theorem ammSwap1Balance1FreePtr_add4_toNat (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1FreePtr out ret + ⟨4⟩).toNat =
      (ammSwap1Balance1FreePtr out ret).toNat + 4 := by
  have hfit := (ammSwap1Balance1FreePtr_bounds out ret
    hlo hbound hretBound).2
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt (by omega)]

theorem ammSwap1Balance1SelectorMem_size (I : ExecutionEnv)
    (out ret : ByteArray) :
    (ammSwap1Balance1FreePtr out ret).toNat + 32 ≤
      (ammSwap1Balance1SelectorMem I out ret).size := by
  unfold ammSwap1Balance1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammSwap1Balance1SelectorMem_read64 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1SelectorMem I out ret).readWithPadding
      64 32 = UInt256.toByteArray (ammSwap1Balance1FreePtr out ret) := by
  unfold ammSwap1Balance1SelectorMem
  have hptr := (ammSwap1Balance1FreePtr_bounds out ret
    hlo hbound hretBound).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by
      have hsz := ammSwap1Balance0DecodeMem_size_ge I
        hlo hbound
        (lt_trans hretBound (by norm_num [UInt256.size]))
      have hfp0 := (ammMintToken0FreePtr_bounds out hlo hbound).1
      change 160 ≤ (ammMintToken0FreePtr out).toNat at hfp0
      omega)
    (by omega)]
  exact ammSwap1Balance0DecodeMem_read64 I out ret

theorem ammSwap1Balance1CalldataMem_size (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1FreePtr out ret).toNat + 36 ≤
      (ammSwap1Balance1CalldataMem I out ret).size := by
  unfold ammSwap1Balance1CalldataMem
  rw [ammSwap1Balance1FreePtr_add4_toNat out ret
    hlo hbound hretBound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammSwap1Balance1CalldataMem_read64 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1CalldataMem I out ret).readWithPadding
      64 32 = UInt256.toByteArray (ammSwap1Balance1FreePtr out ret) := by
  unfold ammSwap1Balance1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      rw [ammSwap1Balance1FreePtr_add4_toNat out ret
        hlo hbound hretBound]
      have hsz := ammSwap1Balance1SelectorMem_size I out ret
      omega)
    (by
      rw [ammSwap1Balance1FreePtr_add4_toNat out ret
        hlo hbound hretBound]
      have hptr := (ammSwap1Balance1FreePtr_bounds out ret
        hlo hbound hretBound).1
      omega)]
  exact ammSwap1Balance1SelectorMem_read64 I
    hlo hbound hretBound

theorem ammSwap1Balance1SelectorMem_read4 (I : ExecutionEnv)
    (out ret : ByteArray) :
    (ammSwap1Balance1SelectorMem I out ret).readWithPadding
      (ammSwap1Balance1FreePtr out ret).toNat 4 =
      balanceOfSelector := by
  unfold ammSwap1Balance1SelectorMem
  have h := toByteArray_write_read_window_no_gap
    ammMintBalanceSelectorWord
    (ammSwap1Balance0DecodeMem I out ret)
    (ammSwap1Balance1FreePtr out ret).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammMintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammSwap1Balance1CalldataMem_read4 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1CalldataMem I out ret).readWithPadding
      (ammSwap1Balance1FreePtr out ret).toNat 4 =
      balanceOfSelector := by
  unfold ammSwap1Balance1CalldataMem
  rw [write32_read_below_len _ _ _
    (ammSwap1Balance1FreePtr out ret).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [ammSwap1Balance1FreePtr_add4_toNat out ret
        hlo hbound hretBound]
      have hsz := ammSwap1Balance1SelectorMem_size I out ret
      omega)
    (by rw [ammSwap1Balance1FreePtr_add4_toNat out ret
      hlo hbound hretBound])
    (by
      have hsz := ammSwap1Balance1SelectorMem_size I out ret
      omega)
    (by norm_num) (by norm_num)]
  exact ammSwap1Balance1SelectorMem_read4 I out ret

theorem ammSwap1Balance1CalldataMem_read32 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1CalldataMem I out ret).readWithPadding
      (ammSwap1Balance1FreePtr out ret + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold ammSwap1Balance1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammSwap1Balance1FreePtr_add4_toNat out ret
      hlo hbound hretBound]
    have hsz := ammSwap1Balance1SelectorMem_size I out ret
    omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammSwap1Balance1CalldataMem_read36 (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    (ammSwap1Balance1CalldataMem I out ret).readWithPadding
      (ammSwap1Balance1FreePtr out ret).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (ammSwap1Balance1FreePtr out ret).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have hsz := ammSwap1Balance1CalldataMem_size I
        hlo hbound hretBound
      omega)]
  rw [ammSwap1Balance1CalldataMem_read4 I
    hlo hbound hretBound,
    ← ammSwap1Balance1FreePtr_add4_toNat out ret
      hlo hbound hretBound,
    ammSwap1Balance1CalldataMem_read32 I
      hlo hbound hretBound]

theorem ammSwap1Balance1CalldataMem_encode (I : ExecutionEnv)
    {out ret : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammSwap1Balance1CalldataMem I out ret).readWithPadding
        (ammSwap1Balance1FreePtr out ret).toNat 36) := by
  rw [ammSwap1Balance1CalldataMem_read36 I
    hlo hbound hretBound,
    ← ammMintBalanceCalldataMem_read I]
  exact ammMintBalanceEncode_eq I

theorem ammSwap1X_balance1ArgMem
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3322⟩
      [ammSwap1Balance1FreePtr out ret, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken1Word acc.2 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1SelectorMem I out ret)
      (ammSwap1Balance1SelectorWords out ret)
      ret acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3334⟩
      [ammSwap1Balance1FreePtr out ret + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word acc.2 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1CalldataMem I out ret)
      (ammSwap1Balance1CalldataWords out ret)
      ret acc k' C' := by
  let fp := ammSwap1Balance1FreePtr out ret
  have rd6408 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨3334⟩, swap2, swap1,
    push2 ⟨6408⟩, jump (by jump_dest)]
  have rd6269 := evm_run rd6408 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨6427⟩, push0, dup4, add, dup5, push2 ⟨6269⟩,
    jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩, jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩,
    jump (by jump_dest)]
  have rd5441 := evm_run rd5400 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd6278 := evm_run rd5441 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hcanon : (UInt256.ofNat I.codeOwner).toNat < EVM.addressModulus := by
    have h2 : (UInt256.ofNat I.codeOwner).toNat = I.codeOwner.val := by
      apply UInt256.toNat_ofNat_of_lt
      exact lt_of_lt_of_le I.codeOwner.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide)
    rw [h2]
    change I.codeOwner.val < AccountAddress.size
    exact I.codeOwner.isLt
  have hclean : UInt256.land (UInt256.ofNat I.codeOwner) solcAddrMask =
      UInt256.ofNat I.codeOwner := solcAddrMask_clean hcanon
  have rd6278' := rd6278
  rw [hclean] at rd6278'
  have rd6427pre := evm_run rd6278' with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + fp + ⟨0⟩ = fp + ⟨4⟩ := by
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) fp]
  have rd6427pre' := rd6427pre
  rw [hoff] at rd6427pre'
  let awArg := ammSwap1Balance1CalldataWords out ret
  have rd6427 := RD.mstore
    (Cₘ awArg - Cₘ (ammSwap1Balance1SelectorWords out ret))
    (ammSwap1Balance1CalldataMem I out ret) awArg
    rd6427pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awArg, fp, ammSwap1Balance1CalldataWords])
    (by unfold ammSwap1Balance1CalldataMem; rfl)
    (by simp [awArg, fp, ammSwap1Balance1CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1521 := evm_run rd6427 with [
    pop, pop, jump (by jump_dest), jumpdest,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp, u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, awArg, hend] using rd1521⟩

theorem ammSwap1X_balance1CallFrame
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3334⟩
      [ammSwap1Balance1FreePtr out ret + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word acc.2 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1CalldataMem I out ret)
      (ammSwap1Balance1CalldataWords out ret)
      ret acc k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3346⟩
      [gasWord, ammMintToken1Word acc.2 I,
        ammSwap1Balance1FreePtr out ret, ⟨36⟩,
        ammSwap1Balance1FreePtr out ret, ⟨32⟩,
        ammSwap1Balance1FreePtr out ret + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word acc.2 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance1CalldataMem I out ret)
      (ammSwap1Balance1CalldataWords out ret)
      ret acc k' C' := by
  let aw := ammSwap1Balance1CalldataWords out ret
  let fp := ammSwap1Balance1FreePtr out ret
  have haw : aw.toNat = 6 + (out.size + 31) / 32 +
      (ret.size + 31) / 32 := by
    simpa only [aw] using ammSwap1Balance1CalldataWords_toNat
      out ret hlo hbound hretLo hretBound
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle0 : (out.size + 31) / 32 ≤ out.size + 31 :=
      Nat.div_le_self _ _
    have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 :=
      Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
      UInt256.size := by norm_num [UInt256.size]
    omega
  have hmem : 64 <
      (ammSwap1Balance1CalldataMem I out ret).size := by
    have hsz := ammSwap1Balance1CalldataMem_size I
      hlo hbound hretBound
    have hptr := (ammSwap1Balance1FreePtr_bounds out ret
      hlo hbound hretBound).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap1Balance1CalldataMem I out ret).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1Balance1CalldataMem I out ret).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammSwap1Balance1CalldataMem_read64 I
          (out := out) (ret := ret) hlo hbound hretBound))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd1526 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1527 := RD.mload 0 fp aw rd1526 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap1Balance1CalldataWords out ret).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammSwap1Balance1CalldataWords out ret from by
          simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1533 := evm_run rd1527 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd1533'⟩ := rd1533
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd1533'⟩

noncomputable def ammSwap1Balance1PostCallMem (I : ExecutionEnv)
    (out ret ret1 : ByteArray) : ByteArray :=
  ret1.write 0 (ammSwap1Balance1CalldataMem I out ret)
    (ammSwap1Balance1FreePtr out ret).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat

theorem ammSwap1Balance1CallWords_same (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammSwap1Balance1CalldataWords out ret).toNat
          (ammSwap1Balance1FreePtr out ret).toNat 36)
        (ammSwap1Balance1FreePtr out ret).toNat 32) =
      ammSwap1Balance1CalldataWords out ret := by
  let n0 := (out.size + 31) / 32
  let n1 := (ret.size + 31) / 32
  let fp := ammSwap1Balance1FreePtr out ret
  let aw := ammSwap1Balance1CalldataWords out ret
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    simpa only [fp, n0, n1] using
      ammSwap1Balance1FreePtr_toNat out ret hbound hretBound
  have haw : aw.toNat = 6 + n0 + n1 := by
    simpa only [aw, n0, n1] using
      ammSwap1Balance1CalldataWords_toNat out ret
        hlo hbound hretLo hretBound
  have hM : MachineState.M
      (MachineState.M aw.toNat fp.toNat 36)
      fp.toNat 32 = aw.toNat := by
    change max (max aw.toNat ((fp.toNat + 36 + 31) / 32))
      ((fp.toNat + 32 + 31) / 32) = _
    rw [hfp, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

end Benchmarks.ActAmm
