import Benchmarks.ActAmm.Swap1SourceCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_transferCall
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hto : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3035⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferCalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD ammBytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨3036⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨3077966991⟩ ::
          ammMintToken0Word σ I :: ammSwap1ToWord I ::
          ammSwap1AmountWord I :: ⟨340⟩ :: [sel])
        (o.write 0 (ammSwap1TransferCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 7) o (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ }
        (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
        "transfer" 0
        [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
          .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o)
        true ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1222⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd1223, hosz⟩ :=
    RD.call rd1222 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68)
        128 32) = UInt256.ofNat 7 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd1223
  · refine callCoincides (A_in := A_in) (g'' := g'')
      (callGas := callGas) (callPerm := true)
      (targetWord := ammMintToken0Word σ I)
      (mem := ammSwap1TransferCalldataMem I)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩)
      (fun h => absurd hdepth
        (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (ammSwap1TransferCalldataMem_encode I hto) ?_
    simpa [initState, hperm] using hΘ
  · have hinputSize :
        ((ammSwap1TransferCalldataMem I).readWithPadding 128 68).size =
          68 := by
      rw [readWithPadding_eq_extract' _ 128 68
        (by norm_num) (by norm_num)
        (by rw [ammSwap1TransferCalldataMem_size])]
      rw [ByteArray.size_extract, ammSwap1TransferCalldataMem_size]
      omega
    have hbound :
        ((ammSwap1TransferCalldataMem I).readWithPadding 128 68).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (ammMintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammSwap1TransferCalldataMem I).readWithPadding 128 68)
      (I.depth + 1) I.header true
      (by simpa [initState, hperm] using hΘ) hbound

theorem ammSwap1X_transferCallFailed
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨3036⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd1230 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3050⟩, jumpiNT (by decide)]
  have rd1233 := evm_run rd1230 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1234 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1233 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd1236 := evm_run rd1234 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) -
      Cₘ awout)
    rd1236 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammSwap1X_transferDepthRevert
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : Nat}
    (hdepth : I.depth = 1024)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3035⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferCalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd1223⟩ := RD.callDepthLimit rd
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68)
        128 32) = UInt256.ofNat 7 := by native_decide
  have rd1223' := rd1223
  simpa [haw, byteArray_write_len_zero] using
    (ammSwap1X_transferCallFailed rd1223'
      (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega))

theorem ammSwap1X_transferCallSucceeded
    {cAstart gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3036⟩
      [⟨1⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3055⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3050⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

theorem ammSwap1TransferDepthBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x3d, 0xb6, 0x0b, 0x43]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      ⟨314⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hne0 : ammSwap1ToWord I ≠ ammMintToken0Word σ_evm I)
    (hne1 : ammSwap1ToWord I ≠ ammMintToken1Word σ_evm I)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  obtain ⟨hliqS, h0S, h1S⟩ :=
    ammSwap1ValidSourceGuards (g := Sat256.ofUInt256 g)
      hAccounts hcanon hliq hne0 hne1
  have hdepthS : evmS.executionEnv.depth = 1024 := by
    simpa [evmS, initState] using hdepth
  have hbody := ammSwap1SourceTransferDepthRevert evmS I
    (by simpa [evmS, initState] using hwv)
    hpos hliqS h0S h1S hdepthS hcanon
  obtain ⟨_, _, rd750⟩ := ammSwap1X_decoded
    hsz68 hsize hbig hcanon hreach
  obtain ⟨_, _, rd816⟩ := ammSwap1X_amountPositive rd750 hpos
  obtain ⟨_, _, rd884⟩ := ammSwap1X_liquidityAvailable rd816 hliq
  obtain ⟨_, _, rd941⟩ := ammSwap1X_token0Address rd884
  obtain ⟨_, _, rd973⟩ := ammSwap1X_token0Distinct rd941 hcanon hne0
  obtain ⟨_, _, rd1029⟩ := ammSwap1X_token1Address rd973
  obtain ⟨_, _, rd1117⟩ := ammSwap1X_token1Distinct rd1029 hcanon hne1
  obtain ⟨_, _, rd1174⟩ := ammSwap1X_transferTokenAddress rd1117
  obtain ⟨_, _, rd1196⟩ := ammSwap1X_transferSelectorMem rd1174
  obtain ⟨_, _, rd1209⟩ := ammSwap1X_transferArgs rd1196 hcanon
  obtain ⟨gasWord, _, _, rd1222⟩ := ammSwap1X_transferCallFrame rd1209
  have hrev := ammSwap1X_transferDepthRevert hdepth rd1222
  exact hrev.reEquivExecutionRevert hcode (ammDispatch_swap1 hsel)
    (ammDecode_swap1_ok hsz68 hbig hcanon) hbody

end Benchmarks.ActAmm
