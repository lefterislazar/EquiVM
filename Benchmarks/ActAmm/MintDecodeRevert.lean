import Benchmarks.ActAmm.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammMintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammMintX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨5856⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammMintX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := ammMintX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨5856⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammMintX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammMintToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammMintX_dec5470 hsz36 hsize hbig hreach
  have hunclean : UInt256.eq (ammMintToWord I)
      (UInt256.land (ammMintToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.ammDecodeAddrRevert rd hunclean (by evm_ov)

/-- The valid nonzero-supply path reaches the first token call frame. -/
theorem ammMintX_token0FrameFromEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k C : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3725⟩ [gasWord, ammMintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
        (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  have h3622 := ammMintX_nonzero_toToken0 hsz36 hsize hbig hcanon hnonzero hreach
  have h3680 := ammMintX_toToken0Selector h3622
  have h3701 := ammMintX_token0SelectorMem h3680
  have h3713 := ammMintX_token0ArgMem h3701
  exact ammMintX_token0CallFrame h3713

theorem ammMintX_token0DepthRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdepth : I.depth = 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3725⟩ [gasWord, ammMintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
        (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty
        (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd3725⟩ := hframe
  obtain ⟨_, _, rd3726⟩ := RD.solcStaticcallDepthLimit rd3725
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ammMintX_token0CallFailed rd3726 (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammMintSourceToken0DepthRevert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (ammMintStore I) mintTransition.body .reverted := by
  let evmS := initState cA gh bl σ σ₀ g A I
  let tgt : EVM.Address :=
    (EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)).val)
  have hcall : typedCallViaEVM config evmS tgt "balanceOf" 0
      [.address evmS.executionEnv.codeOwner]
      (false, { evmS with substate := (evmS.addAccessedAccount tgt).substate },
        ByteArray.empty) false := by
    apply callNotMade_depthLimit (calldata :=
      (ammMintBalanceCalldataMem I).readWithPadding 128 36)
    · simpa [evmS, initState] using ammMintBalanceEncode_eq I
    · simpa [evmS, initState] using hdepth
  apply ammMintSourceToken0CallFailed evmS
    { evmS with substate := (evmS.addAccessedAccount tgt).substate }
    I ByteArray.empty
  · simpa [evmS, initState] using hwv
  · simpa [evmS, solcSlotWord, codeOwnerStorageWord, initState] using hnonzero
  · exact hcall

theorem ammMintX_token1FrameFromFirst
    {cA gh bl σ σ' σ₀ A I} {g : Sat256} {sel : UInt256}
    {o : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (hlo : 32 ≤ o.size) (hsize : o.size < UInt256.size)
    (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3745⟩ [⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0PostCallMem I o) (UInt256.ofNat 6) o (cA', σ') k C) :
    ∃ (gasWord : UInt256) (k' C' : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3881⟩ [gasWord, ammMintToken1Word σ' I, ammMintToken0FreePtr o,
          ⟨36⟩, ammMintToken0FreePtr o, ⟨32⟩,
          ammMintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
          ammMintToken1Word σ' I, ⟨0⟩,
          UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)), ⟨0⟩,
          ammMintToWord I, ⟨368⟩, sel]
        (ammMintToken1CalldataMem I o) (ammMintToken1CalldataWords o)
        o (cA', σ') k' C' := by
  obtain ⟨_, _, rd6453⟩ := ammMintX_token0LongToDecoder hlo hsize rd
  obtain ⟨_, _, rd3776⟩ := ammMintX_token0DecodeOk hlo hbound rd6453
  obtain ⟨_, _, rd3779⟩ := ammMintX_token0Decoded rd3776
  obtain ⟨_, _, rd3836⟩ := ammMintX_toToken1Selector rd3779
  obtain ⟨_, _, rd3857⟩ := ammMintX_token1SelectorMem hlo hbound rd3836
  obtain ⟨_, _, rd3869⟩ := ammMintX_token1ArgMem rd3857
  exact ammMintX_token1CallFrame hlo hbound rd3869

theorem ammMintRatioWord_toNat (o : ByteArray) (r supply : UInt256)
    (hlo : 32 ≤ o.size)
    (hle : r.toNat ≤ fromByteArrayBigEndian (o.extract 0 32))
    (hfit : (fromByteArrayBigEndian (o.extract 0 32) - r.toNat) *
      supply.toNat < UInt256.size) :
    (UInt256.div
      (UInt256.mul
        (UInt256.sub
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) r)
        supply) r).toNat =
      ((fromByteArrayBigEndian (o.extract 0 32) - r.toNat) *
        supply.toNat) / r.toNat := by
  have hv : (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat =
      fromByteArrayBigEndian (o.extract 0 32) :=
    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hsub : (UInt256.sub
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) r).toNat =
      fromByteArrayBigEndian (o.extract 0 32) - r.toNat := by
    rw [usub_toNat (by rw [hv]; exact hle), hv]
  have hfitWord :
      (UInt256.sub
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) r).toNat *
        supply.toNat < UInt256.size := by rw [hsub]; exact hfit
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfitWord, hsub]

theorem ammMintX_liquidityZeroFromTrace
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {o1 o2 : ByteArray}
    {k C : Nat}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4046⟩ [q1, q0, a1, a0, v1, v0, liq,
        ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2)
      (ammMintToken1CalldataWords o1) o2 (cA, σ) k C)
    (hzero : liq = ⟨0⟩) :
    RDrev ammBytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have hmem : 64 < (ammMintToken1DecodeMem I o1 o2).size := by
    have hsz := ammMintToken1DecodeMem_size_ge I hlo1 hbound1 hsize2
    have hptr := (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).1
    have hptr' : 160 ≤ (ammMintToken0FreePtr o1).toNat := by
      simpa only [ammMintToken0FreePtr] using hptr
    omega
  have ⟨hawlo, hawfit, _⟩ :=
    ammMintToken1ActiveWords_bounds o1 hlo1 hbound1
  have rdZero : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4046⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2)
      (ammMintToken1CalldataWords o1) o2 (cA, σ) k C := by
    simpa only [hzero] using rd
  exact ammMintX_liquidityZero rdZero hmem
    (ammMintToken1DecodeMem_read64 I o1 o2) hawlo
    (ammActiveWords64 _ hawlo hawfit)

end Benchmarks.ActAmm
