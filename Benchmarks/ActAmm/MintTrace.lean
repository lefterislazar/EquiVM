import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.BalanceOf
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Benchmarks.ActAmm.Arithmetic
import Reasoning.SolmBody
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammMintToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammMintToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammMintToWord I).toNat)

abbrev ammMintStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (ammMintToValue I)

theorem ammDecode_mint_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata =
        some (ammMintStore I) := by
  show decodeCalldata ["to"] [addr] I.calldata = _
  simpa [ammMintStore, ammMintToValue, ammMintToWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "to") hsz36 hbig hcanon

theorem ammDecode_mint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "to") hsz4 hshort

theorem ammDecode_mint_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammMintToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr, ammMintToWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "to") hsz36 hbig hnc

theorem ammDecode_mint_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "to") hbig

theorem ammMintSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_mint {cd : ByteArray}
    (hsel : ((⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some mintTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition])
    (post := [swap0Transition, swap1Transition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammMintSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, ammAllowanceSelectorBytes, hcd]
    | rw [selectorOf, ammApproveSelectorBytes, hcd]
    | rw [selectorOf, ammBalanceOfSelectorBytes, hcd]
    | rw [selectorOf, ammBurnSelectorBytes, hcd]
  all_goals decide

theorem ammMintX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5836⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨363⟩, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨368⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨363⟩, swap2, swap1, push2 ⟨5836⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammMintX_dec5470 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5870⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨363⟩, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammMintX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5870⟩, dup5, dup3, dup6, add, push2 ⟨5470⟩,
    jump (by jump_dest) ]⟩

theorem ammMintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3609⟩
      [ammMintToWord I, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammMintX_dec5470 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  obtain ⟨_, _, rd5870⟩ := RD.ammDecodeAddrOk rd hcanon
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5870 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨3609⟩, jump (by jump_dest) ]⟩

theorem ammMintX_zeroSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus)
    (hzero : solcSlotWord σ I ⟨0⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3609⟩ := ammMintX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd3613 := evm_run rd3609 with [jumpdest, push0, push0, push0]
  obtain ⟨_, _, rd3614₀⟩ := rd3613.sload (by native_decide) (by evm_ov)
  have rd3614 := rd3614₀
  simp only [solcSlotWord] at hzero
  rw [hzero] at rd3614
  exact evm_run rd3614 with [
    sub, push2 ⟨3622⟩, jumpiNT (by decide),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammMintX_nonzero_toToken0 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨342⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3622⟩
      [⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3609⟩ := ammMintX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd3613 := evm_run rd3609 with [jumpdest, push0, push0, push0]
  obtain ⟨_, _, rd3614⟩ := rd3613.sload (by native_decide) (by evm_ov)
  have rd3615 := evm_run rd3614 with [sub]
  have hsub : UInt256.sub (solcSlotWord σ I ⟨0⟩) ⟨0⟩ =
      solcSlotWord σ I ⟨0⟩ := by
    apply u256_inj
    rw [usub_toNat (by simp)]
    simp
  have hsub' := hsub
  simp only [solcSlotWord] at hsub'
  rw [hsub'] at rd3615
  have hnonzero' := hnonzero
  simp only [solcSlotWord] at hnonzero'
  exact ⟨_, _, evm_run rd3615 with [
    push2 ⟨3622⟩, jumpiT (by simpa [UInt256.isZero] using hnonzero')
      (by jump_dest) ]⟩

abbrev ammMintToken0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask

abbrev ammMintToken1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨4⟩) solcAddrMask

theorem ammMintDivPow0 (w : UInt256) :
    UInt256.div w (UInt256.exp ⟨256⟩ ⟨0⟩) = w := by
  have hexp : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  rw [hexp]
  cases w with
  | mk v =>
    cases v with
    | mk n hn =>
      change (UInt256.mk (Fin.div ⟨n, hn⟩ 1)) = UInt256.mk ⟨n, hn⟩
      congr 1
      apply Fin.ext
      simp only [Fin.div]
      have hone : 1 % UInt256.size = 1 := by decide
      rw [hone]
      omega

theorem ammMintMaskTwice (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land w solcAddrMask := by
  rw [u256_land_comm solcAddrMask w]
  rw [u256_land_comm solcAddrMask (UInt256.land w solcAddrMask)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

/-- The first external call uses the address packed into storage slot 3. -/
theorem ammMintX_toToken0Selector {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3622⟩ [⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3680⟩ [ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3622⟩ := hreach
  have rd3628 := evm_run rd3622 with [jumpdest, push0, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd3629⟩ := rd3628.sload (by native_decide) (by evm_ov)
  have rd3680 := evm_run rd3629 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd3680⟩

abbrev ammMintBalanceSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (⟨4294967295⟩ : UInt256) ⟨1889567281⟩) ⟨224⟩

noncomputable def ammMintBalanceSelectorMem : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0 solcFreePtrMem 128 32

theorem ammMintBalanceSelectorMem_size : ammMintBalanceSelectorMem.size = 160 := by
  unfold ammMintBalanceSelectorMem
  exact toByteArray_write32_size_of_ge solcFreePtrMem ammMintBalanceSelectorWord
    128 96 160 solcFreePtrMem_size (by omega) (by native_decide) (by omega)

theorem ammMintBalanceSelectorMem_selector :
    ammMintBalanceSelectorMem.extract 128 132 = balanceOfSelector := by
  unfold ammMintBalanceSelectorMem
  have hgap : 128 - solcFreePtrMem.size < USize.size := by
    rw [solcFreePtrMem_size]
    native_decide
  rw [toByteArray_write_eq ammMintBalanceSelectorWord solcFreePtrMem 128
    (by rw [solcFreePtrMem_size]; omega) hgap]
  have hprefix :
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (128 - solcFreePtrMem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, solcFreePtrMem_size]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

noncomputable def ammMintBalanceCalldataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0 ammMintBalanceSelectorMem 132 32

theorem ammMintBalanceCalldataMem_size (I : ExecutionEnv) :
    (ammMintBalanceCalldataMem I).size = 164 := by
  unfold ammMintBalanceCalldataMem
  exact toByteArray_write32_size_of_le ammMintBalanceSelectorMem
    (UInt256.ofNat I.codeOwner) 132 160 164 ammMintBalanceSelectorMem_size
    (by rw [ammMintBalanceSelectorMem_size]; omega) (by omega)

theorem ammMintBalanceSelectorMem_read64 :
    ammMintBalanceSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold ammMintBalanceSelectorMem
  rw [toByteArray_write_read_below_of_gap ammMintBalanceSelectorWord solcFreePtrMem
    128 64 (by rw [solcFreePtrMem_size]) (by omega)
    (by rw [solcFreePtrMem_size]; native_decide), solcFreePtrMem_read64]

theorem ammMintBalanceCalldataMem_read64 (I : ExecutionEnv) :
    (ammMintBalanceCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammMintBalanceCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [ammMintBalanceSelectorMem_size]; omega) (by omega),
    ammMintBalanceSelectorMem_read64]

theorem ammMintBalanceCalldataMem_read (I : ExecutionEnv) :
    (ammMintBalanceCalldataMem I).readWithPadding 128 36 =
      balanceOfSelector ++ (UInt256.ofNat I.codeOwner).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [ammMintBalanceCalldataMem_size]), ammMintBalanceCalldataMem,
    write32_eq _ ammMintBalanceSelectorMem 132 (by rw [toByteArray_size])
      (by rw [ammMintBalanceSelectorMem_size]; omega)]
  have hAsz : (ammMintBalanceSelectorMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, ammMintBalanceSelectorMem_size]
    omega
  have hBsz : ((UInt256.ofNat I.codeOwner).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      (ammMintBalanceSelectorMem.extract 0 132 ++
        (UInt256.ofNat I.codeOwner).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : (UInt256.ofNat I.codeOwner).toByteArray.extract 0 32 =
      (UInt256.ofNat I.codeOwner).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega),
    ammMintBalanceSelectorMem_selector,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem ammMintBalanceEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammMintBalanceCalldataMem I).readWithPadding 128 36) := by
  rw [ammMintBalanceCalldataMem_read]
  have hword : EVM.word ↑I.codeOwner.val = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

noncomputable def ammMintToken0PostCallMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (ammMintBalanceCalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem ammMintToken0PostCallMem_size_short (I : ExecutionEnv) {o : ByteArray}
    (hshort : o.size < 32) :
    (ammMintToken0PostCallMem I o).size = 164 := by
  unfold ammMintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, ammMintBalanceCalldataMem_size]
  · rw [write_eq_gen o (ammMintBalanceCalldataMem I) 128 o.size
      hzero le_rfl (by rw [ammMintBalanceCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract,
      ammMintBalanceCalldataMem_size]
    omega

theorem ammMintToken0PostCallMem_read64_short (I : ExecutionEnv) {o : ByteArray}
    (hshort : o.size < 32) :
    (ammMintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammMintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact ammMintBalanceCalldataMem_read64 I
  · rw [write_read_below_gen_extend o (ammMintBalanceCalldataMem I) 128
      o.size 64 hzero le_rfl
      (by rw [ammMintBalanceCalldataMem_size]; omega) (by omega)]
    exact ammMintBalanceCalldataMem_read64 I

theorem ammMintToken0PostCallMem_size_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0PostCallMem I o).size = 164 := by
  unfold ammMintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (ammMintBalanceCalldataMem I) 128 32
    (by omega) hlo (by rw [ammMintBalanceCalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract,
    ammMintBalanceCalldataMem_size]
  omega

theorem ammMintToken0PostCallMem_read64_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammMintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_read_below_gen_extend o (ammMintBalanceCalldataMem I) 128 32 64
    (by omega) hlo (by rw [ammMintBalanceCalldataMem_size]; omega) (by omega)]
  exact ammMintBalanceCalldataMem_read64 I

theorem ammMintToken0PostCallMem_read128_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0PostCallMem I o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold ammMintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen, write_eq_gen o (ammMintBalanceCalldataMem I) 128 32
    (by omega) hlo (by rw [ammMintBalanceCalldataMem_size]; omega)]
  have hprefix : ((ammMintBalanceCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, ammMintBalanceCalldataMem_size]
    omega
  have hsrc : (o.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((ammMintBalanceCalldataMem I).extract 0 128 ++ o.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn : 128 + 32 ≤
      (((ammMintBalanceCalldataMem I).extract 0 128 ++ o.extract 0 32) ++
        (ammMintBalanceCalldataMem I).extract 160 (ammMintBalanceCalldataMem I).size).size := by
    rw [ByteArray.size_append, hmemSize]
    omega
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_left _ _ 128 160 (by rw [hmemSize])]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix, show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

abbrev ammMintReturndataRounded (o : ByteArray) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩) (UInt256.lnot ⟨31⟩)

theorem ammMintReturndataRounded_toNat (o : ByteArray)
    (hbound : o.size < 2 ^ 138) :
    (ammMintReturndataRounded o).toNat = 32 * ((o.size + 31) / 32) := by
  unfold ammMintReturndataRounded
  change (UInt256.land (UInt256.ofNat o.size + ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat = _
  rw [uland_toNat, lnot31_toNat, uadd_toNat]
  rw [UInt256.toNat_ofNat_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    Nat.mod_eq_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]
  exact nat_land_mask _ (by have h := hbound; norm_num at *; omega)

theorem ammMintToken0FreePtr_toNat (o : ByteArray)
    (hbound : o.size < 2 ^ 138) :
    (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toNat =
      128 + 32 * ((o.size + 31) / 32) := by
  change (⟨128⟩ + ammMintReturndataRounded o : UInt256).toNat = _
  rw [uadd_toNat, ammMintReturndataRounded_toNat o hbound]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    Nat.mod_eq_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]

theorem ammMintToken0FreePtr_bounds (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    160 ≤ (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toNat ∧
      (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toNat ≤ o.size + 159 := by
  rw [ammMintToken0FreePtr_toNat o hbound]
  constructor
  · have hdiv : 1 ≤ (o.size + 31) / 32 := by omega
    omega
  · have hmul : 32 * ((o.size + 31) / 32) ≤ o.size + 31 := Nat.mul_div_le _ _
    omega

noncomputable def ammMintToken0DecodeMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toByteArray.write 0
    (ammMintToken0PostCallMem I o) 64 32

theorem ammMintToken0DecodeMem_size_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0DecodeMem I o).size = 164 := by
  unfold ammMintToken0DecodeMem
  exact toByteArray_write32_size_of_le (ammMintToken0PostCallMem I o)
    (UInt256.add ⟨128⟩ (ammMintReturndataRounded o))
    64 164 164 (ammMintToken0PostCallMem_size_long I hlo hhi)
    (by rw [ammMintToken0PostCallMem_size_long I hlo hhi]; omega) (by omega)

theorem ammMintToken0DecodeMem_read128_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0DecodeMem I o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold ammMintToken0DecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [ammMintToken0PostCallMem_size_long I hlo hhi]; omega)
    (by omega)
    (by rw [ammMintToken0PostCallMem_size_long I hlo hhi]; omega)]
  exact ammMintToken0PostCallMem_read128_long I hlo hhi

theorem ammMintToken0DecodeMem_read64_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammMintToken0DecodeMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)) := by
  unfold ammMintToken0DecodeMem
  exact toByteArray_write32_read_back _ _ _ (by
    rw [ammMintToken0PostCallMem_size_long I hlo hhi]
    omega)


abbrev ammMintToken0FreePtr (o : ByteArray) : UInt256 :=
  UInt256.add ⟨128⟩ (ammMintReturndataRounded o)

noncomputable def ammMintToken1SelectorMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0
    (ammMintToken0DecodeMem I o) (ammMintToken0FreePtr o).toNat 32

noncomputable def ammMintToken1CalldataMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (ammMintToken1SelectorMem I o) (ammMintToken0FreePtr o + ⟨4⟩).toNat 32

theorem ammMintToken0FreePtr_add4_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken0FreePtr o + ⟨4⟩).toNat = (ammMintToken0FreePtr o).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr : (ammMintToken0FreePtr o).toNat ≤ o.size + 159 := by
    simpa only [ammMintToken0FreePtr] using (ammMintToken0FreePtr_bounds o hlo hbound).2
  norm_num [UInt256.size] at *
  omega

theorem ammMintToken1SelectorMem_size (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken0FreePtr o).toNat + 32 ≤ (ammMintToken1SelectorMem I o).size := by
  unfold ammMintToken1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammMintToken1SelectorMem_read64 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1SelectorMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o) := by
  unfold ammMintToken1SelectorMem
  have hptr : 160 ≤ (ammMintToken0FreePtr o).toNat := by
    simpa only [ammMintToken0FreePtr] using (ammMintToken0FreePtr_bounds o hlo hbound).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [ammMintToken0DecodeMem_size_long I hlo (by norm_num [UInt256.size] at *; omega)]; omega)
    (by omega)]
  exact ammMintToken0DecodeMem_read64_long I hlo (by norm_num [UInt256.size] at *; omega)

theorem ammMintToken1SelectorMem_read4 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1SelectorMem I o).readWithPadding
      (ammMintToken0FreePtr o).toNat 4 = balanceOfSelector := by
  unfold ammMintToken1SelectorMem
  have h := toByteArray_write_read_window_no_gap ammMintBalanceSelectorWord
    (ammMintToken0DecodeMem I o) (ammMintToken0FreePtr o).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammMintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammMintToken1CalldataMem_size (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken0FreePtr o).toNat + 36 ≤ (ammMintToken1CalldataMem I o).size := by
  unfold ammMintToken1CalldataMem
  rw [ammMintToken0FreePtr_add4_toNat o hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammMintToken1CalldataMem_read64 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1CalldataMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o) := by
  unfold ammMintToken1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by rw [ammMintToken0FreePtr_add4_toNat o hlo hbound];
        exact le_trans (by omega) (ammMintToken1SelectorMem_size I hlo hbound))
    (by rw [ammMintToken0FreePtr_add4_toNat o hlo hbound];
        have h : 160 ≤ (ammMintToken0FreePtr o).toNat := by
          simpa only [ammMintToken0FreePtr] using (ammMintToken0FreePtr_bounds o hlo hbound).1
        omega)]
  exact ammMintToken1SelectorMem_read64 I hlo hbound

theorem ammMintToken1CalldataMem_read4 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1CalldataMem I o).readWithPadding
      (ammMintToken0FreePtr o).toNat 4 = balanceOfSelector := by
  unfold ammMintToken1CalldataMem
  rw [write32_read_below_len _ _ _ (ammMintToken0FreePtr o).toNat 4
    (by rw [toByteArray_size])
    (by rw [ammMintToken0FreePtr_add4_toNat o hlo hbound];
        exact le_trans (by omega) (ammMintToken1SelectorMem_size I hlo hbound))
    (by rw [ammMintToken0FreePtr_add4_toNat o hlo hbound])
    (by exact le_trans (by omega) (ammMintToken1SelectorMem_size I hlo hbound))
    (by norm_num) (by norm_num)]
  exact ammMintToken1SelectorMem_read4 I hlo hbound

theorem ammMintToken1CalldataMem_read32 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1CalldataMem I o).readWithPadding
      (ammMintToken0FreePtr o + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold ammMintToken1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammMintToken0FreePtr_add4_toNat o hlo hbound]
    exact le_trans (by omega) (ammMintToken1SelectorMem_size I hlo hbound))]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammMintToken1CalldataMem_read36 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1CalldataMem I o).readWithPadding
      (ammMintToken0FreePtr o).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _ (ammMintToken0FreePtr o).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact ammMintToken1CalldataMem_size I hlo hbound)]
  rw [ammMintToken1CalldataMem_read4 I hlo hbound,
    ← ammMintToken0FreePtr_add4_toNat o hlo hbound,
    ammMintToken1CalldataMem_read32 I hlo hbound]

theorem ammMintToken1CalldataMem_encode (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammMintToken1CalldataMem I o).readWithPadding
        (ammMintToken0FreePtr o).toNat 36) := by
  rw [ammMintToken1CalldataMem_read36 I hlo hbound,
    ← ammMintBalanceCalldataMem_read I]
  exact ammMintBalanceEncode_eq I

/-- Mint writes the `balanceOf(address)` selector into scratch memory. -/
theorem ammMintX_token0SelectorMem {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3680⟩ [ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3701⟩ [⟨128⟩, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      ammMintBalanceSelectorMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3680⟩ := hreach
  have rd3688 := evm_run rd3680 with [push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd3689 := evm_run rd3688 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd3700 := evm_run rd3689 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd3701 := evm_run rd3700 with [
    raw mstore 6 ammMintBalanceSelectorMem (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [ammMintBalanceSelectorMem, ammMintBalanceSelectorWord] using rd3701⟩

/-- Solidity's address encoder writes this contract's address after the selector. -/
theorem ammMintX_token0ArgMem {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3701⟩ [⟨128⟩, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      ammMintBalanceSelectorMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3713⟩ [⟨164⟩, ⟨1889567281⟩, ammMintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3701⟩ := hreach
  have rd6408 := evm_run rd3701 with [
    push1 ⟨4⟩, add, push2 ⟨3713⟩, swap2, swap1,
    push2 ⟨6408⟩, jump (by jump_dest)]
  have rd6269 := evm_run rd6408 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨6427⟩, push0, dup4, add, dup5, push2 ⟨6269⟩,
    jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩, jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩, jump (by jump_dest)]
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
  have rd6427 := evm_run rd6278' with [
    jumpdest, dup3,
    raw mstore 3 (ammMintBalanceCalldataMem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd3713 := evm_run rd6427 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide,
    show (⟨132⟩ : UInt256) + ⟨32⟩ = ⟨164⟩ from by decide] using rd3713⟩

/-- The first `STATICCALL` frame requests a 32-byte return for `balanceOf(this)`. -/
theorem ammMintX_token0CallFrame {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3713⟩ [⟨164⟩, ⟨1889567281⟩, ammMintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k C : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3725⟩ [gasWord, ammMintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
        (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3713⟩ := hreach
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammMintBalanceCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((ammMintBalanceCalldataMem I).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [ammMintBalanceCalldataMem_size]; decide)
      (by decide) (ammMintBalanceCalldataMem_read64 I)
  have rd3718 := evm_run rd3713 with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd3719 := evm_run rd3718 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd3725 := evm_run rd3719 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd3725'⟩ := rd3725
  exact ⟨gasWord, _, _, by
    simpa only [show (⟨164⟩ : UInt256) - ⟨128⟩ = ⟨36⟩ from by decide]
      using rd3725'⟩

/-- The EVM token0 `STATICCALL` and the Solm `balanceOf(this)` call share the same Θ witness. -/
theorem ammMintX_token0Staticcall {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3725⟩ [gasWord, ammMintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          ammMintToken0Word σ I, ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
        (ammMintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3726⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1889567281⟩ ::
          ammMintToken0Word σ I :: ⟨0⟩ :: ⟨0⟩ :: ammMintToWord I :: ⟨368⟩ :: [sel])
        (o.write 0 (ammMintBalanceCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k' C' ∧
      typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (AccountAddress.ofUInt256 (ammMintToken0Word σ I)) "balanceOf" 0
        [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) false ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd3725⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd3726, hosz⟩ :=
    RD.solcStaticcall rd3725 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36) 128 32) =
        UInt256.ofNat 6 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd3726
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := ammMintToken0Word σ I)
      (mem := ammMintBalanceCalldataMem I) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (ammMintBalanceEncode_eq I) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammMintBalanceCalldataMem I).readWithPadding 128 36).size = 36 := by
      rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
        (by rw [ammMintBalanceCalldataMem_size])]
      rw [ByteArray.size_extract, ammMintBalanceCalldataMem_size]
      omega
    have hbound :
        ((ammMintBalanceCalldataMem I).readWithPadding 128 36).size ≤
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
      ((ammMintBalanceCalldataMem I).readWithPadding 128 36)
      (I.depth + 1) I.header false (by simpa [initState] using hΘ) hbound

theorem ammMintToken0StaticSlot {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' : Substate} {z : Bool} {o : ByteArray}
    (hcall : typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
      (AccountAddress.ofUInt256 (ammMintToken0Word σ I)) "balanceOf" 0
      [.address I.codeOwner]
      (z, { initState cA gh bl σ σ₀ g A I with
        accountMap := σ', substate := A', createdAccounts := cA' }, o) false)
    (slot : UInt256) : solcSlotWord σ' I slot = solcSlotWord σ I slot := by
  have hstatic := typedCallViaEVM_static_accountStorageStateEq hcall
  have hslot := accountStorageStateEq_storage_findD hstatic I.codeOwner slot ⟨0⟩
  simpa [solcSlotWord, codeOwnerStorageWord, initState] using hslot.symm

/-- A failed first token call bubbles its return data and reverts. -/
theorem ammMintX_token0CallFailed {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3726⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3733 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3740⟩,
    jumpiNT (by decide) ]
  have rd3736 := evm_run rd3733 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd3737 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd3736 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd3739 := evm_run rd3737 with [returndatasize, push0]
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd3739 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

/-- The successful call clears its ABI call frame before decoding the returned word. -/
theorem ammMintX_token0CallSucceeded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3726⟩ [⟨1⟩, ⟨164⟩, ⟨1889567281⟩, ammMintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel] mem aw o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3745⟩ [⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3740⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

theorem ammMintX_token0ToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hmemSize : (ammMintToken0PostCallMem I o).size = 164)
    (hread64 : (ammMintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3745⟩ [⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨3776⟩,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammMintToken0PostCallMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((ammMintToken0PostCallMem I o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide) hread64
  have rd3747 := evm_run rd with [push1 ⟨64⟩]
  have rd3748 := evm_run rd3747 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd3762 := evm_run rd3748 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd3763 := evm_run rd3762 with [
    raw mstore 0 (ammMintToken0DecodeMem I o) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd6453 := evm_run rd3763 with [
    pop, dup2, add, swap1, push2 ⟨3776⟩, swap2, swap1,
    push2 ⟨6453⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [ammMintToken0DecodeMem, ammMintReturndataRounded] using rd6453⟩

theorem ammMintX_token0ShortToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hshort : o.size < 32)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3745⟩ [⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨3776⟩,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' :=
  ammMintX_token0ToDecoder (ammMintToken0PostCallMem_size_short I hshort)
    (ammMintToken0PostCallMem_read64_short I hshort) rd

theorem ammMintX_token0LongToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3745⟩ [⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨3776⟩,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' :=
  ammMintX_token0ToDecoder (ammMintToken0PostCallMem_size_long I hlo hhi)
    (ammMintToken0PostCallMem_read64_long I hlo hhi) rd

theorem ammMintX_token0DecodeShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hshort : o.size < 32)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨3776⟩,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcheck := solcDecodeEndLenCheckShort_128_32 hshort
  have rd6462 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6462 with [
    push2 ⟨6474⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6473⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammMintX_token0DecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨3776⟩,
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3776⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  have hhi : o.size < UInt256.size := by
    exact lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo (by omega : o.size < 2 ^ 255)
  have rd6474 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6474⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6433 := evm_run rd6474 with [
    jumpdest, push0, push2 ⟨6487⟩, dup5, dup3, dup6, add,
    push2 ⟨6433⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (ammMintToken0DecodeMem I o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((ammMintToken0DecodeMem I o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      ammMintToken0DecodeMem_read128_long I hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) ⟨128⟩ 164
        (ammMintToken0DecodeMem_size_long I hlo hhi) (by decide) (by decide))
  have rd6436 := evm_run rd6433 with [jumpdest, push0, dup2]
  have rd6437 := evm_run rd6436 with [
    raw mload 0 v (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd5499 := evm_run rd6437 with [
    swap1, pop, push2 ⟨6447⟩, dup2, push2 ⟨5499⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6447⟩ := RD.ammCheckUint256Identity rd5499 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6487 := evm_run rd6447 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3776 := evm_run rd6487 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd3776⟩

theorem ammMintX_token0Decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3776⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3779⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, swap1, pop]⟩

theorem ammMintX_toToken1Selector {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o mem : ByteArray} {aw : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3779⟩ [v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3836⟩ [ammMintToken1Word σ' I, ⟨0⟩,
        v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      mem aw o (cA', σ') k' C' := by
  have rd3784 := evm_run rd with [push0, push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd3785⟩ := rd3784.sload (by native_decide) (by evm_ov)
  have rd3836 := evm_run rd3785 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken1Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd3836⟩

/-- The source's token0 receiver is the same slot-3 address used by the call trace. -/

def ammMintToken1SelectorWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 6 (ammMintToken0FreePtr o).toNat 32)

theorem ammMintX_token1SelectorMem {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3836⟩ [ammMintToken1Word σ' I, ⟨0⟩,
        v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken0DecodeMem I o) (UInt256.ofNat 6) o (cA', σ') k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3857⟩ [ammMintToken0FreePtr o, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1SelectorMem I o) (ammMintToken1SelectorWords o)
      o (cA', σ') k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammMintToken0DecodeMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((ammMintToken0DecodeMem I o).readWithPadding 64 32))) =
        ammMintToken0FreePtr o :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6)
      (v := ammMintToken0FreePtr o)
      (by rw [ammMintToken0DecodeMem_size_long I hlo (by norm_num [UInt256.size] at *; omega)]; decide)
      (by decide)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          ammMintToken0FreePtr] using
          ammMintToken0DecodeMem_read64_long I hlo (by norm_num [UInt256.size] at *; omega))
  have rd3844 := evm_run rd with [push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd3845 := evm_run rd3844 with [
    raw mload 0 (ammMintToken0FreePtr o) (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd3856 := evm_run rd3845 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := ammMintToken1SelectorWords o
  have rd3857 := RD.mstore
    (Cₘ awSel - Cₘ (UInt256.ofNat 6))
    (ammMintToken1SelectorMem I o) awSel rd3856 (by native_decide)
    (by intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awSel,
          ammMintToken1SelectorWords,
          show (UInt256.ofNat 6).toNat = 6 from by decide])
    (by unfold ammMintToken1SelectorMem; rfl)
    (by simp [awSel, ammMintToken1SelectorWords,
          show (UInt256.ofNat 6).toNat = 6 from by decide])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [ammMintBalanceSelectorWord] using rd3857⟩

def ammMintToken1CalldataWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammMintToken1SelectorWords o).toNat
    (ammMintToken0FreePtr o + ⟨4⟩).toNat 32)

theorem ammMintToken1SelectorWords_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1SelectorWords o).toNat = 5 + (o.size + 31) / 32 := by
  let n := (o.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have hM : MachineState.M 6 (ammMintToken0FreePtr o).toNat 32 = 5 + n := by
    change max 6 (((ammMintToken0FreePtr o).toNat + 32 + 31) / 32) = 5 + n
    rw [hptr]
    omega
  unfold ammMintToken1SelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem ammMintToken1CalldataWords_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken1CalldataWords o).toNat = 6 + (o.size + 31) / 32 := by
  let n := (o.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have harg : (ammMintToken0FreePtr o + ⟨4⟩).toNat = 132 + 32 * n := by
    rw [ammMintToken0FreePtr_add4_toNat o hlo hbound, hptr]
    omega
  have haw : (ammMintToken1SelectorWords o).toNat = 5 + n := by
    simpa only [n] using ammMintToken1SelectorWords_toNat o hlo hbound
  have hM : MachineState.M (ammMintToken1SelectorWords o).toNat
      (ammMintToken0FreePtr o + ⟨4⟩).toNat 32 = 6 + n := by
    change max (ammMintToken1SelectorWords o).toNat
      (((ammMintToken0FreePtr o + ⟨4⟩).toNat + 32 + 31) / 32) = 6 + n
    rw [harg, haw]
    omega
  unfold ammMintToken1CalldataWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem ammMintToken1CalldataWords_mload64_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (ammMintToken1CalldataWords o).toNat 64 32) =
      ammMintToken1CalldataWords o := by
  have haw := ammMintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (ammMintToken1CalldataWords o).toNat 64 32 =
      (ammMintToken1CalldataWords o).toNat := by
    change max (ammMintToken1CalldataWords o).toNat ((64 + 32 + 31) / 32) = _
    have hn : 1 ≤ (o.size + 31) / 32 := by omega
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammMintToken1CalldataWords_mload64_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ ammMintToken1CalldataWords o * ⟨32⟩ := by
  have haw := ammMintToken1CalldataWords_toNat o hlo hbound
  have hmul : (ammMintToken1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : (o.size + 31) / 32 ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammMintToken1CalldataWords o * ⟨32⟩).toNat ≤ 64 := by
    exact h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul] at hle
  have hn : 1 ≤ (o.size + 31) / 32 := by omega
  omega

theorem ammMintX_token1ArgMem {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3857⟩ [ammMintToken0FreePtr o, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1SelectorMem I o) (ammMintToken1SelectorWords o)
      o (cA', σ') k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3869⟩ [ammMintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1CalldataMem I o) (ammMintToken1CalldataWords o)
      o (cA', σ') k' C' := by
  have rd6408 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨3869⟩, swap2, swap1,
    push2 ⟨6408⟩, jump (by jump_dest)]
  have rd6269 := evm_run rd6408 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨6427⟩, push0, dup4, add, dup5, push2 ⟨6269⟩,
    jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩, jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩, jump (by jump_dest)]
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
  have hoff : (⟨4⟩ : UInt256) + ammMintToken0FreePtr o + ⟨0⟩ =
      ammMintToken0FreePtr o + ⟨4⟩ := by
    change ((⟨4⟩ : UInt256) + ammMintToken0FreePtr o) + ⟨0⟩ = _
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) (ammMintToken0FreePtr o)]
  have rd6427pre' := rd6427pre
  rw [hoff] at rd6427pre'
  let awArg := ammMintToken1CalldataWords o
  have rd6427 := RD.mstore
    (Cₘ awArg - Cₘ (ammMintToken1SelectorWords o))
    (ammMintToken1CalldataMem I o) awArg rd6427pre' (by native_decide)
    (by intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awArg,
          ammMintToken1CalldataWords])
    (by unfold ammMintToken1CalldataMem; rfl)
    (by simp [awArg, ammMintToken1CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3869 := evm_run rd6427 with [
    pop, pop, jump (by jump_dest), jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + ammMintToken0FreePtr o + ⟨32⟩ =
      ammMintToken0FreePtr o + ⟨36⟩ := by
    change ((⟨4⟩ : UInt256) + ammMintToken0FreePtr o) + ⟨32⟩ = _
    rw [u256_add_comm (⟨4⟩ : UInt256) (ammMintToken0FreePtr o),
      u256_add_assoc (ammMintToken0FreePtr o) ⟨4⟩ ⟨32⟩,
      show (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ from by decide]
  exact ⟨_, _, by
    simpa only [hend, awArg] using rd3869⟩

theorem ammMintX_token1CallFrame {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3869⟩ [ammMintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1CalldataMem I o) (ammMintToken1CalldataWords o)
      o (cA', σ') k C) :
    ∃ (gasWord : UInt256) (k' C' : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3881⟩ [gasWord, ammMintToken1Word σ' I, ammMintToken0FreePtr o,
          ⟨36⟩, ammMintToken0FreePtr o, ⟨32⟩,
          ammMintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
          ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
          ammMintToWord I, ⟨368⟩, sel]
        (ammMintToken1CalldataMem I o) (ammMintToken1CalldataWords o)
        o (cA', σ') k' C' := by
  let aw := ammMintToken1CalldataWords o
  let fp := ammMintToken0FreePtr o
  have hmem : 64 < (ammMintToken1CalldataMem I o).size := by
    have hsz : fp.toNat + 36 ≤ (ammMintToken1CalldataMem I o).size :=
      ammMintToken1CalldataMem_size I hlo hbound
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, ammMintToken0FreePtr] using (ammMintToken0FreePtr_bounds o hlo hbound).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammMintToken1CalldataMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammMintToken1CalldataMem I o).readWithPadding 64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using ammMintToken1CalldataWords_mload64_haw o hlo hbound)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        ammMintToken1CalldataMem_read64 I hlo hbound)
  have rd3874 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      ammMintToken1CalldataWords_mload64_same o hlo hbound
  have rd3875 := RD.mload 0 fp aw rd3874 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (ammMintToken1CalldataWords o).toNat
            (⟨64⟩ : UInt256).toNat 32) = ammMintToken1CalldataWords o from by
          simpa only [aw] using hsame]
        omega)
    hval
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3881 := evm_run rd3875 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd3881'⟩ := rd3881
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd3881'⟩


noncomputable def ammMintToken1PostCallMem
    (I : ExecutionEnv) (o1 o2 : ByteArray) : ByteArray :=
  o2.write 0 (ammMintToken1CalldataMem I o1) (ammMintToken0FreePtr o1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat

theorem ammMintToken1CallWords_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammMintToken1CalldataWords o).toNat
          (ammMintToken0FreePtr o).toNat 36)
        (ammMintToken0FreePtr o).toNat 32) =
      ammMintToken1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have haw : (ammMintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using ammMintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M
      (MachineState.M (ammMintToken1CalldataWords o).toNat
        (ammMintToken0FreePtr o).toNat 36)
      (ammMintToken0FreePtr o).toNat 32 =
      (ammMintToken1CalldataWords o).toNat := by
    change max (max (ammMintToken1CalldataWords o).toNat
      (((ammMintToken0FreePtr o).toNat + 36 + 31) / 32))
      (((ammMintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammMintX_token1Staticcall {cA gh bl σ σ' σ₀ A A1 I} {g : Sat256}
    {sel v : UInt256} {o1 : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare}
    (hlo : 32 ≤ o1.size) (hbound : o1.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3881⟩ [gasWord, ammMintToken1Word σ' I, ammMintToken0FreePtr o1,
          ⟨36⟩, ammMintToken0FreePtr o1, ⟨32⟩,
          ammMintToken0FreePtr o1 + ⟨36⟩, ⟨1889567281⟩,
          ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
          ammMintToWord I, ⟨368⟩, sel]
        (ammMintToken1CalldataMem I o1) (ammMintToken1CalldataWords o1)
        o1 (cA', σ') k C) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (o2 : ByteArray) (A2 : Substate) (k' C' : ℕ),
      RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3882⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (ammMintToken0FreePtr o1 + ⟨36⟩) :: ⟨1889567281⟩ ::
          ammMintToken1Word σ' I :: ⟨0⟩ :: v :: ⟨0⟩ ::
          ammMintToWord I :: ⟨368⟩ :: [sel])
        (ammMintToken1PostCallMem I o1 o2)
        (ammMintToken1CalldataWords o1) o2 (cA'', σ'') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A1, createdAccounts := cA' }
        (AccountAddress.ofUInt256 (ammMintToken1Word σ' I)) "balanceOf" 0
        [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ'', substate := A2, createdAccounts := cA'' }, o2) false ∧
      o2.size < UInt256.size ∧ o2.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd3881⟩ := hframe
  obtain ⟨cA'', σ'', z, o2, A_in, callGas, k', C', hΘpack, rd3882, hosz⟩ :=
    RD.solcStaticcall rd3881 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A2, hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammMintToken1CalldataWords o1).toNat
          (ammMintToken0FreePtr o1).toNat 36)
        (ammMintToken0FreePtr o1).toNat 32) =
      ammMintToken1CalldataWords o1 :=
    ammMintToken1CallWords_same o1 hlo hbound
  refine ⟨cA'', σ'', z, o2, A2, k', C', ?_, ?_, hosz, ?_⟩
  · simpa [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, ammMintToken1PostCallMem] using rd3882
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := ammMintToken1Word σ' I)
      (mem := ammMintToken1CalldataMem I o1)
      (inOff := ammMintToken0FreePtr o1) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (ammMintToken1CalldataMem_encode I hlo hbound) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((ammMintToken1CalldataMem I o1).readWithPadding
          (ammMintToken0FreePtr o1).toNat 36).size = 36 := by
      rw [ammMintToken1CalldataMem_read36 I hlo hbound, ByteArray.size_append,
        toByteArray_size]
      decide
    have hinputBound :
        ((ammMintToken1CalldataMem I o1).readWithPadding
          (ammMintToken0FreePtr o1).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA' gh bl σ' σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken1Word σ' I))
      (toExecute σ' (AccountAddress.ofUInt256 (ammMintToken1Word σ' I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammMintToken1CalldataMem I o1).readWithPadding
        (ammMintToken0FreePtr o1).toNat 36)
      (I.depth + 1) I.header false (by simpa [initState] using hΘ) hinputBound


theorem ammMintX_token1CallFailed {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3882⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3889 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3896⟩,
    jumpiNT (by decide)]
  have rd3892 := evm_run rd3889 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd3893 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd3892 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd3895 := evm_run rd3893 with [returndatasize, push0]
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd3895 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammMintX_token1CallSucceeded {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {mem o1 o2 : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3882⟩ [⟨1⟩, ammMintToken0FreePtr o1 + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        ammMintToWord I, ⟨368⟩, sel] mem aw o2 acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3901⟩ [⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      mem aw o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨3896⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

theorem ammMintToken1PostCallMem_size_ge (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (ammMintToken0FreePtr o1).toNat + 36 ≤
      (ammMintToken1PostCallMem I o1 o2).size := by
  unfold ammMintToken1PostCallMem
  have hbase := ammMintToken1CalldataMem_size I hlo1 hbound1
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen o2 (ammMintToken1CalldataMem I o1)
        (ammMintToken0FreePtr o1).toNat o2.size hzero le_rfl (by omega),
        ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write_eq_gen o2 (ammMintToken1CalldataMem I o1)
      (ammMintToken0FreePtr o1).toNat 32 (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
    omega

theorem ammMintToken1PostCallMem_read64 (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (ammMintToken1PostCallMem I o1 o2).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o1) := by
  unfold ammMintToken1PostCallMem
  have hbase := ammMintToken1CalldataMem_size I hlo1 hbound1
  have hptr : 160 ≤ (ammMintToken0FreePtr o1).toNat := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).1
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammMintToken1CalldataMem_read64 I hlo1 hbound1
    · rw [write_read_below_gen o2 (ammMintToken1CalldataMem I o1)
        (ammMintToken0FreePtr o1).toNat o2.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact ammMintToken1CalldataMem_read64 I hlo1 hbound1
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write32_read_below o2 (ammMintToken1CalldataMem I o1)
      (ammMintToken0FreePtr o1).toNat 64 hlong (by omega) (by omega)]
    exact ammMintToken1CalldataMem_read64 I hlo1 hbound1

theorem ammMintToken1PostCallMem_readPtr (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (ammMintToken1PostCallMem I o1 o2).readWithPadding
      (ammMintToken0FreePtr o1).toNat 32 = o2.extract 0 32 := by
  unfold ammMintToken1PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
      (by decide) hlo2 hsize2
  rw [hlen]
  exact write32_read_back o2 (ammMintToken1CalldataMem I o1)
    (ammMintToken0FreePtr o1).toNat hlo2 (by
      have h := ammMintToken1CalldataMem_size I hlo1 hbound1
      omega)

noncomputable def ammMintToken1DecodeMem
    (I : ExecutionEnv) (o1 o2 : ByteArray) : ByteArray :=
  (UInt256.add (ammMintToken0FreePtr o1) (ammMintReturndataRounded o2)).toByteArray.write 0
    (ammMintToken1PostCallMem I o1 o2) 64 32

theorem ammMintToken1DecodeMem_size_ge (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (ammMintToken0FreePtr o1).toNat + 36 ≤
      (ammMintToken1DecodeMem I o1 o2).size := by
  unfold ammMintToken1DecodeMem
  let base := ammMintToken1PostCallMem I o1 o2
  have hbase : (ammMintToken0FreePtr o1).toNat + 36 ≤ base.size :=
    ammMintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
  have hptr : 160 ≤ (ammMintToken0FreePtr o1).toNat := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).1
  have hsz : ((UInt256.add (ammMintToken0FreePtr o1)
      (ammMintReturndataRounded o2)).toByteArray.write 0 base 64 32).size = base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem ammMintToken1DecodeMem_readPtr (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (ammMintToken1DecodeMem I o1 o2).readWithPadding
      (ammMintToken0FreePtr o1).toNat 32 = o2.extract 0 32 := by
  unfold ammMintToken1DecodeMem
  have hbase := ammMintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
  have hptr : 160 ≤ (ammMintToken0FreePtr o1).toNat := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).1
  rw [write32_read_above _ _ 64 (ammMintToken0FreePtr o1).toNat
    (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]
  exact ammMintToken1PostCallMem_readPtr I hlo1 hbound1 hlo2 hsize2

theorem ammMintX_token1ToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3901⟩ [⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1PostCallMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [ammMintToken0FreePtr o1,
        UInt256.add (ammMintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨3932⟩, ⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k' C' := by
  let aw := ammMintToken1CalldataWords o1
  let fp := ammMintToken0FreePtr o1
  have hmem : 64 < (ammMintToken1PostCallMem I o1 o2).size := by
    have hsz : fp.toNat + 36 ≤ (ammMintToken1PostCallMem I o1 o2).size :=
      ammMintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, ammMintToken0FreePtr] using
        (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammMintToken1PostCallMem I o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammMintToken1PostCallMem I o1 o2).readWithPadding 64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using ammMintToken1CalldataWords_mload64_haw o1 hlo1 hbound1)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        ammMintToken1PostCallMem_read64 I hlo1 hbound1 hsize2)
  have hsame : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      ammMintToken1CalldataWords_mload64_same o1 hlo1 hbound1
  have rd3903 := evm_run rd with [push1 ⟨64⟩]
  have rd3904 := RD.mload 0 fp aw rd3903 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (ammMintToken1CalldataWords o1).toNat
            (⟨64⟩ : UInt256).toNat 32) = ammMintToken1CalldataWords o1 from by
          simpa only [aw] using hsame]
        omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3918 := evm_run rd3904 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd3919 := RD.mstore 0 (ammMintToken1DecodeMem I o1 o2) aw
    rd3918 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (ammMintToken1CalldataWords o1).toNat
            (⟨64⟩ : UInt256).toNat 32) = ammMintToken1CalldataWords o1 from by
          simpa only [aw] using hsame]
        simp only [aw]
        omega)
    (by unfold ammMintToken1DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6453 := evm_run rd3919 with [
    pop, dup2, add, swap1, push2 ⟨3932⟩, swap2, swap1,
    push2 ⟨6453⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, ammMintReturndataRounded] using rd6453⟩

theorem ammMintToken1LenCheckShort (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hshort : o2.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammMintToken0FreePtr o1) (UInt256.ofNat o2.size))
        (ammMintToken0FreePtr o1)) ⟨32⟩ = ⟨1⟩ := by
  have hptr : (ammMintToken0FreePtr o1).toNat ≤ o1.size + 159 := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (ammMintToken0FreePtr o1).toNat) (len := o2.size) (words := 1)
    (by simpa using hshort) (ammMintToken0FreePtr o1).val.isLt
    (by
      have hcap : 2 ^ 138 + 200 < UInt256.size := by norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat, show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammMintToken1LenCheckOk (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammMintToken0FreePtr o1) (UInt256.ofNat o2.size))
        (ammMintToken0FreePtr o1)) ⟨32⟩ = ⟨0⟩ := by
  have hptr : (ammMintToken0FreePtr o1).toNat ≤ o1.size + 159 := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o1 hlo1 hbound1).2
  have hcheck := solcReturnStaticLenCheckOk
    (base := (ammMintToken0FreePtr o1).toNat) (len := o2.size) (words := 1)
    (by simpa using hlo2) (by omega : o2.size < 2 ^ 255)
    (ammMintToken0FreePtr o1).val.isLt
    (by
      have hcap : 2 ^ 139 + 200 < UInt256.size := by norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat, show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammMintX_token1DecodeShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hshort : o2.size < 32)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [ammMintToken0FreePtr o1,
        UInt256.add (ammMintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨3932⟩, ⟨0⟩, v, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcheck := ammMintToken1LenCheckShort o1 o2 hlo1 hbound1 hshort
  have rd6462 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6462 with [
    push2 ⟨6474⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6473⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammMintToken1CalldataWords_ptr_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ ammMintToken0FreePtr o ≥ ammMintToken1CalldataWords o * ⟨32⟩ := by
  let n := (o.size + 31) / 32
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have haw : (ammMintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using ammMintToken1CalldataWords_toNat o hlo hbound
  have hmul : (ammMintToken1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammMintToken1CalldataWords o * ⟨32⟩).toNat ≤
      (ammMintToken0FreePtr o).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem ammMintToken1CalldataWords_mloadPtr_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (ammMintToken1CalldataWords o).toNat
      (ammMintToken0FreePtr o).toNat 32) = ammMintToken1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (ammMintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using ammMintToken0FreePtr_toNat o hbound
  have haw : (ammMintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using ammMintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (ammMintToken1CalldataWords o).toNat
      (ammMintToken0FreePtr o).toNat 32 =
      (ammMintToken1CalldataWords o).toNat := by
    change max (ammMintToken1CalldataWords o).toNat
      (((ammMintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammMintX_token1DecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v1 : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨6453⟩ [ammMintToken0FreePtr o1,
        UInt256.add (ammMintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨3932⟩, ⟨0⟩, v1, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3932⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        ⟨0⟩, v1, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k' C' := by
  let aw := ammMintToken1CalldataWords o1
  let fp := ammMintToken0FreePtr o1
  let v2 : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32))
  have hcheck := ammMintToken1LenCheckOk o1 o2 hlo1 hbound1 hlo2 hbound2
  have rd6474 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6474⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6433 := evm_run rd6474 with [
    jumpdest, push0, push2 ⟨6487⟩, dup5, dup3, dup6, add,
    push2 ⟨6433⟩, jump (by jump_dest)]
  have hmem : fp.toNat < (ammMintToken1DecodeMem I o1 o2).size := by
    have hsz : fp.toNat + 36 ≤ (ammMintToken1DecodeMem I o1 o2).size :=
      ammMintToken1DecodeMem_size_ge I hlo1 hbound1
        (by exact lt_trans hbound2 (by norm_num [UInt256.size]))
    omega
  have hval :
      (if fp.toNat ≥ (ammMintToken1DecodeMem I o1 o2).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammMintToken1DecodeMem I o1 o2).readWithPadding fp.toNat 32))) = v2 :=
    by
      have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
        simpa only [fp, aw] using ammMintToken1CalldataWords_ptr_haw o1 hlo1 hbound1
      rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
        ammMintToken1DecodeMem_readPtr I hlo1 hbound1 hlo2
          (by exact lt_trans hbound2 (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      ammMintToken1CalldataWords_mloadPtr_same o1 hlo1 hbound1
  have rd6436 := evm_run rd6433 with [jumpdest, push0, dup2]
  have hzero : ammMintToken0FreePtr o1 + ⟨0⟩ = ammMintToken0FreePtr o1 := by
    rw [u256_add_comm, u256_zero_add]
  have rd6436' := rd6436
  rw [hzero] at rd6436'
  have rd6437 := RD.mload 0 v2 aw rd6436' (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (ammMintToken1CalldataWords o1).toNat
            (ammMintToken0FreePtr o1).toNat 32) = ammMintToken1CalldataWords o1 from by
          simpa only [aw, fp] using hsame]
        omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5499 := evm_run rd6437 with [
    swap1, pop, push2 ⟨6447⟩, dup2, push2 ⟨5499⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6447⟩ := RD.ammCheckUint256Identity rd5499 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6487 := evm_run rd6447 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd3932 := evm_run rd6487 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v2, aw, fp] using rd3932⟩

theorem ammMintX_token1Decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v1 : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3932⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        ⟨0⟩, v1, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3935⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        v1, ⟨0⟩, ammMintToWord I, ⟨368⟩, sel]
      (ammMintToken1DecodeMem I o1 o2) (ammMintToken1CalldataWords o1)
      o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, swap1, pop]⟩

end Benchmarks.ActAmm
