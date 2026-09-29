import Benchmarks.ActAmm4.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4MintX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨4981⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4MintX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4MintX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨4981⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4MintX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4MintToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4MintX_dec4657 hsz36 hsize hbig hreach
  have hunclean : UInt256.eq (amm4MintToWord I)
      (UInt256.land (amm4MintToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.amm4DecodeAddrRevert rd hunclean (by evm_ov)

/-- The valid nonzero-supply path reaches the first token call frame. -/
theorem amm4MintX_token0FrameFromEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k C : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1594⟩ [gasWord, amm4MintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  have h1491 := amm4MintX_nonzero_toToken0 hsz36 hsize hbig hcanon hnonzero hreach
  have h1549 := amm4MintX_toToken0Selector h1491
  have h1570 := amm4MintX_token0SelectorMem h1549
  have h1582 := amm4MintX_token0ArgMem h1570
  exact amm4MintX_token0CallFrame h1582

theorem amm4MintX_token0DepthRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdepth : I.depth = 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1594⟩ [gasWord, amm4MintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty
        (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd1594⟩ := hframe
  obtain ⟨_, _, rd1595⟩ := RD.solcStaticcallDepthLimit rd1594
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact amm4MintX_token0CallFailed rd1595 (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4MintSourceToken0DepthRevert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (amm4MintStore I) mintTransition.body .reverted := by
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
      (amm4MintBalanceCalldataMem I).readWithPadding 128 36)
    · simpa [evmS, initState] using amm4MintBalanceEncode_eq I
    · simpa [evmS, initState] using hdepth
  apply amm4MintSourceToken0CallFailed evmS
    { evmS with substate := (evmS.addAccessedAccount tgt).substate }
    I ByteArray.empty
  · simpa [evmS, initState] using hwv
  · simpa [evmS, solcSlotWord, codeOwnerStorageWord, initState] using hnonzero
  · exact hcall

theorem amm4MintX_token1FrameFromFirst
    {cA gh bl σ σ' σ₀ A I} {g : Sat256} {sel : UInt256}
    {o : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (hlo : 32 ≤ o.size) (hsize : o.size < UInt256.size)
    (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1614⟩ [⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0PostCallMem I o) (UInt256.ofNat 6) o (cA', σ') k C) :
    ∃ (gasWord : UInt256) (k' C' : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1750⟩ [gasWord, amm4MintToken1Word σ' I, amm4MintToken0FreePtr o,
          ⟨36⟩, amm4MintToken0FreePtr o, ⟨32⟩,
          amm4MintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
          amm4MintToken1Word σ' I, ⟨0⟩,
          UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)), ⟨0⟩,
          amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintToken1CalldataMem I o) (amm4MintToken1CalldataWords o)
        o (cA', σ') k' C' := by
  obtain ⟨_, _, rd5415⟩ := amm4MintX_token0LongToDecoder hlo hsize rd
  obtain ⟨_, _, rd1645⟩ := amm4MintX_token0DecodeOk hlo hbound rd5415
  obtain ⟨_, _, rd1648⟩ := amm4MintX_token0Decoded rd1645
  obtain ⟨_, _, rd1705⟩ := amm4MintX_toToken1Selector rd1648
  obtain ⟨_, _, rd1726⟩ := amm4MintX_token1SelectorMem hlo hbound rd1705
  obtain ⟨_, _, rd1738⟩ := amm4MintX_token1ArgMem rd1726
  exact amm4MintX_token1CallFrame hlo hbound rd1738

theorem amm4MintRatioWord_toNat (o : ByteArray) (r supply : UInt256)
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

theorem amm4MintX_liquidityZeroFromTrace
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel v0 v1 a0 a1 q0 q1 liq : UInt256} {o1 o2 : ByteArray}
    {k C : Nat}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, liq,
        amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2)
      (amm4MintToken1CalldataWords o1) o2 (cA, σ) k C)
    (hzero : liq = ⟨0⟩) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have hmem : 64 < (amm4MintToken1DecodeMem I o1 o2).size := by
    have hsz := amm4MintToken1DecodeMem_size_ge I hlo1 hbound1 hsize2
    have hptr := (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
    have hptr' : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
      simpa only [amm4MintToken0FreePtr] using hptr
    omega
  have ⟨hawlo, hawfit, _⟩ :=
    amm4MintToken1ActiveWords_bounds o1 hlo1 hbound1
  have rdZero : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨1915⟩ [q1, q0, a1, a0, v1, v0, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2)
      (amm4MintToken1CalldataWords o1) o2 (cA, σ) k C := by
    simpa only [hzero] using rd
  exact amm4MintX_liquidityZero rdZero hmem
    (amm4MintToken1DecodeMem_read64 I o1 o2) hawlo
    (amm4ActiveWords64 _ hawlo hawfit)

end Benchmarks.ActAmm4
