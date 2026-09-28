import Benchmarks.ActAmm.BurnTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammBurnToken1CalldataWords_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammBurnToken1CalldataWords o).toNat =
      7 + (o.size + 31) / 32 := by
  let n := (o.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using
      ammMintToken0FreePtr_toNat o hbound
  have harg : (ammMintToken0FreePtr o + ⟨36⟩).toNat =
      164 + 32 * n := by
    rw [ammBurnToken0FreePtr_add36_toNat o hlo hbound, hptr]
    omega
  have hsel : (ammBurnToken1SelectorWords o).toNat =
      max 7 (5 + n) := by
    unfold ammBurnToken1SelectorWords
    rw [show MachineState.M 7 (ammMintToken0FreePtr o).toNat 32 =
      max 7 (5 + n) by
      change max 7 (((ammMintToken0FreePtr o).toNat + 32 + 31) / 32) = _
      rw [hptr]
      omega]
    rw [UInt256.toNat_ofNat_of_lt]
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega
  have harg4 : (ammMintToken0FreePtr o + ⟨4⟩).toNat =
      132 + 32 * n := by
    rw [ammMintToken0FreePtr_add4_toNat o hlo hbound, hptr]
    omega
  have hamount : (ammBurnToken1AmountWords o).toNat =
      max 7 (6 + n) := by
    unfold ammBurnToken1AmountWords
    rw [show MachineState.M (ammBurnToken1SelectorWords o).toNat
      (ammMintToken0FreePtr o + ⟨4⟩).toNat 32 = max 7 (6 + n) by
      change max (ammBurnToken1SelectorWords o).toNat
        (((ammMintToken0FreePtr o + ⟨4⟩).toNat + 32 + 31) / 32) = _
      rw [hsel, harg4]
      omega]
    rw [UInt256.toNat_ofNat_of_lt]
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega
  unfold ammBurnToken1CalldataWords
  rw [show MachineState.M (ammBurnToken1AmountWords o).toNat
    (ammMintToken0FreePtr o + ⟨36⟩).toNat 32 = 7 + n by
    change max (ammBurnToken1AmountWords o).toNat
      (((ammMintToken0FreePtr o + ⟨36⟩).toNat + 32 + 31) / 32) = _
    rw [hamount, harg]
    omega]
  rw [UInt256.toNat_ofNat_of_lt]
  have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
  have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
  omega

theorem ammBurnToken1CalldataWords_mload64_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (ammBurnToken1CalldataWords o).toNat 64 32) =
      ammBurnToken1CalldataWords o := by
  have haw := ammBurnToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (ammBurnToken1CalldataWords o).toNat 64 32 =
      (ammBurnToken1CalldataWords o).toNat := by
    change max (ammBurnToken1CalldataWords o).toNat ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammBurnToken1CalldataWords_mload64_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ ammBurnToken1CalldataWords o * ⟨32⟩ := by
  have haw := ammBurnToken1CalldataWords_toNat o hlo hbound
  have hmul : (ammBurnToken1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : (o.size + 31) / 32 ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammBurnToken1CalldataWords o * ⟨32⟩).toNat ≤ 64 := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul] at hle
  omega

theorem ammBurnX_token1CallFrame {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray} {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5007⟩
      [ammMintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1CalldataMem I q0 q1 o0)
      (ammBurnToken1CalldataWords o0) o0 (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5020⟩
      [gasWord, ammMintToken1Word σ I, ⟨0⟩,
        ammMintToken0FreePtr o0, ⟨68⟩,
        ammMintToken0FreePtr o0, ⟨32⟩,
        ammMintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1CalldataMem I q0 q1 o0)
      (ammBurnToken1CalldataWords o0) o0 (cA, σ) k' C' := by
  let aw := ammBurnToken1CalldataWords o0
  let fp := ammMintToken0FreePtr o0
  have hmem : 64 < (ammBurnToken1CalldataMem I q0 q1 o0).size := by
    have hsz : fp.toNat + 68 ≤ (ammBurnToken1CalldataMem I q0 q1 o0).size :=
      ammBurnToken1CalldataMem_size I q0 q1 o0 hlo hbound
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, ammMintToken0FreePtr] using
        (ammMintToken0FreePtr_bounds o0 hlo hbound).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnToken1CalldataMem I q0 q1 o0).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding 64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using
        ammBurnToken1CalldataWords_mload64_haw o0 hlo hbound)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        ammBurnToken1CalldataMem_read64 I q0 q1 hlo hbound)
  have rd5012 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      ammBurnToken1CalldataWords_mload64_same o0 hlo hbound
  have rd5013 := RD.mload 0 fp aw rd5012 (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnToken1CalldataWords o0).toNat
          (⟨64⟩ : UInt256).toNat 32) = ammBurnToken1CalldataWords o0 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5020 := evm_run rd5013 with [
    dup1, dup4, sub, dup2, push0, dup8, gas]
  obtain ⟨gasWord, rd5020'⟩ := rd5020
  have hsub : UInt256.sub (fp + ⟨68⟩) fp = ⟨68⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 68)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd5020'⟩

noncomputable def ammBurnToken1PostCallMem
    (I : ExecutionEnv) (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  o1.write 0 (ammBurnToken1CalldataMem I q0 q1 o0)
    (ammMintToken0FreePtr o0).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat

theorem ammBurnToken1CallWords_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammBurnToken1CalldataWords o).toNat
          (ammMintToken0FreePtr o).toNat 68)
        (ammMintToken0FreePtr o).toNat 32) =
      ammBurnToken1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have haw : (ammBurnToken1CalldataWords o).toNat = 7 + n := by
    simpa only [n] using ammBurnToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M
      (MachineState.M (ammBurnToken1CalldataWords o).toNat
        (ammMintToken0FreePtr o).toNat 68)
      (ammMintToken0FreePtr o).toNat 32 =
      (ammBurnToken1CalldataWords o).toNat := by
    change max (max (ammBurnToken1CalldataWords o).toNat
      (((ammMintToken0FreePtr o).toNat + 68 + 31) / 32))
      (((ammMintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammBurnX_token1Call {cAstart cA gh bl σstart σ σ₀ A I}
    {Apre : Substate} {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hto : (ammBurnToWord I).toNat < EVM.addressModulus)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5020⟩
      [gasWord, ammMintToken1Word σ I, ⟨0⟩,
        ammMintToken0FreePtr o0, ⟨68⟩,
        ammMintToken0FreePtr o0, ⟨32⟩,
        ammMintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1CalldataMem I q0 q1 o0)
      (ammBurnToken1CalldataWords o0) o0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o1 : ByteArray) (A' : Substate) (k' C' : Nat),
      RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I) ⟨5021⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (ammMintToken0FreePtr o0 + ⟨68⟩) :: ⟨3077966991⟩ ::
          ammMintToken1Word σ I :: q1 :: q0 :: ammBurnToWord I ::
          ammBurnLiquidityWord I :: ⟨560⟩ :: [sel])
        (ammBurnToken1PostCallMem I q0 q1 o0 o1)
        (ammBurnToken1CalldataWords o0) o1 (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g Apre I with accountMap := σ }
        (AccountAddress.ofUInt256 (ammMintToken1Word σ I))
        "transfer" 0
        [.int (Int.ofNat q1.toNat),
          .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
        (z, { initState cA gh bl σ σ₀ g Apre I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o1)
        true ∧ o1.size < UInt256.size ∧ o1.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd5020⟩ := hframe
  obtain ⟨cA', σ', z, o1, A_in, callGas, k', C', hΘpack, rd5021, hosz⟩ :=
    RD.call rd5020 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw := ammBurnToken1CallWords_same o0 hlo hbound
  refine ⟨cA', σ', z, o1, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [show (⟨68⟩ : UInt256).toNat = 68 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, ammBurnToken1PostCallMem] using rd5021
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := ammMintToken1Word σ I)
      (mem := ammBurnToken1CalldataMem I q0 q1 o0)
      (inOff := ammMintToken0FreePtr o0) (inSize := ⟨68⟩)
      (fun h => absurd hdepth (by
        rw [show I.depth = (1024 : Fin 1025) from h]
        decide))
      rfl (ammBurnToken1CalldataMem_encode I q0 q1 hlo hbound hto) ?_
    simpa [initState, hperm] using hΘ
  · have hinputSize :
        ((ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
          (ammMintToken0FreePtr o0).toNat 68).size = 68 := by
      rw [ammBurnToken1CalldataMem_read I q0 q1 hlo hbound,
        ByteArray.size_append, ByteArray.size_append,
        toByteArray_size, toByteArray_size]
      decide
    have hinputBound :
        ((ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
          (ammMintToken0FreePtr o0).toNat 68).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken1Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (ammMintToken1Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
        (ammMintToken0FreePtr o0).toNat 68)
      (I.depth + 1) I.header true
      (by simpa [initState, hperm] using hΘ) hinputBound

theorem ammBurnX_token1CallFailed {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨5021⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd5028 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨5035⟩, jumpiNT (by decide)]
  have rd5031 := evm_run rd5028 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd5032 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd5031 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd5034 := evm_run rd5032 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd5034 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammBurnX_token1CallSucceeded {cAstart gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 mem o1 : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5021⟩
      [⟨1⟩, ammMintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o1 acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5040⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o1 acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨5035⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

end Benchmarks.ActAmm
