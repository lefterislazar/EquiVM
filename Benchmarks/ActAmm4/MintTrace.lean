import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.BalanceOf
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Benchmarks.ActAmm4.Arithmetic
import Reasoning.SolmBody
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4MintToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4MintToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4MintToWord I).toNat)

abbrev amm4MintStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (amm4MintToValue I)

theorem amm4Decode_mint_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata =
        some (amm4MintStore I) := by
  show decodeCalldata ["to"] [addr] I.calldata = _
  simpa [amm4MintStore, amm4MintToValue, amm4MintToWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "to") hsz36 hbig hcanon

theorem amm4Decode_mint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "to") hsz4 hshort

theorem amm4Decode_mint_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4MintToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr, amm4MintToWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "to") hsz36 hbig hnc

theorem amm4Decode_mint_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "to") hbig

theorem amm4MintSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_mint {cd : ByteArray}
    (hsel : ((⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some mintTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x6a, 0x62, 0x78, 0x42]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition])
    (post := [swapTransition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4MintSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
    | rw [selectorOf, amm4ApproveSelectorBytes, hcd]
    | rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]
    | rw [selectorOf, amm4BurnSelectorBytes, hcd]
  all_goals decide

theorem amm4MintX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4961⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨301⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨296⟩, swap2, swap1, push2 ⟨4961⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4MintX_dec4657 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨4995⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4MintX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨4995⟩, dup5, dup3, dup6, add, push2 ⟨4657⟩,
    jump (by jump_dest) ]⟩

theorem amm4MintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1478⟩
      [amm4MintToWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4MintX_dec4657 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  obtain ⟨_, _, rd4995⟩ := RD.amm4DecodeAddrOk rd hcanon
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd4995 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1478⟩, jump (by jump_dest) ]⟩

theorem amm4MintX_zeroSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hzero : solcSlotWord σ I ⟨0⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1478⟩ := amm4MintX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd1482 := evm_run rd1478 with [jumpdest, push0, push0, push0]
  obtain ⟨_, _, rd1483₀⟩ := rd1482.sload (by native_decide) (by evm_ov)
  have rd1483 := rd1483₀
  simp only [solcSlotWord] at hzero
  rw [hzero] at rd1483
  exact evm_run rd1483 with [
    sub, push2 ⟨1491⟩, jumpiNT (by decide),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4MintX_nonzero_toToken0 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1491⟩
      [⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1478⟩ := amm4MintX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd1482 := evm_run rd1478 with [jumpdest, push0, push0, push0]
  obtain ⟨_, _, rd1483⟩ := rd1482.sload (by native_decide) (by evm_ov)
  have rd1484 := evm_run rd1483 with [sub]
  have hsub : UInt256.sub (solcSlotWord σ I ⟨0⟩) ⟨0⟩ =
      solcSlotWord σ I ⟨0⟩ := by
    apply u256_inj
    rw [usub_toNat (by simp)]
    simp
  have hsub' := hsub
  simp only [solcSlotWord] at hsub'
  rw [hsub'] at rd1484
  have hnonzero' := hnonzero
  simp only [solcSlotWord] at hnonzero'
  exact ⟨_, _, evm_run rd1484 with [
    push2 ⟨1491⟩, jumpiT (by simpa [UInt256.isZero] using hnonzero')
      (by jump_dest) ]⟩

abbrev amm4MintToken0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨3⟩) solcAddrMask

abbrev amm4MintToken1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨4⟩) solcAddrMask

theorem amm4MintDivPow0 (w : UInt256) :
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

theorem amm4MintMaskTwice (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land w solcAddrMask := by
  rw [u256_land_comm solcAddrMask w]
  rw [u256_land_comm solcAddrMask (UInt256.land w solcAddrMask)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

/-- The first external call uses the address packed into storage slot 3. -/
theorem amm4MintX_toToken0Selector {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1491⟩ [⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1549⟩ [amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1491⟩ := hreach
  have rd1497 := evm_run rd1491 with [jumpdest, push0, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd1498⟩ := rd1497.sload (by native_decide) (by evm_ov)
  have rd1549 := evm_run rd1498 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken0Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd1549⟩

abbrev amm4MintBalanceSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (⟨4294967295⟩ : UInt256) ⟨1889567281⟩) ⟨224⟩

noncomputable def amm4MintBalanceSelectorMem : ByteArray :=
  amm4MintBalanceSelectorWord.toByteArray.write 0 solcFreePtrMem 128 32

theorem amm4MintBalanceSelectorMem_size : amm4MintBalanceSelectorMem.size = 160 := by
  unfold amm4MintBalanceSelectorMem
  exact toByteArray_write32_size_of_ge solcFreePtrMem amm4MintBalanceSelectorWord
    128 96 160 solcFreePtrMem_size (by omega) (by native_decide) (by omega)

theorem amm4MintBalanceSelectorMem_selector :
    amm4MintBalanceSelectorMem.extract 128 132 = balanceOfSelector := by
  unfold amm4MintBalanceSelectorMem
  have hgap : 128 - solcFreePtrMem.size < USize.size := by
    rw [solcFreePtrMem_size]
    native_decide
  rw [toByteArray_write_eq amm4MintBalanceSelectorWord solcFreePtrMem 128
    (by rw [solcFreePtrMem_size]; omega) hgap]
  have hprefix :
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (128 - solcFreePtrMem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, solcFreePtrMem_size]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

noncomputable def amm4MintBalanceCalldataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0 amm4MintBalanceSelectorMem 132 32

theorem amm4MintBalanceCalldataMem_size (I : ExecutionEnv) :
    (amm4MintBalanceCalldataMem I).size = 164 := by
  unfold amm4MintBalanceCalldataMem
  exact toByteArray_write32_size_of_le amm4MintBalanceSelectorMem
    (UInt256.ofNat I.codeOwner) 132 160 164 amm4MintBalanceSelectorMem_size
    (by rw [amm4MintBalanceSelectorMem_size]; omega) (by omega)

theorem amm4MintBalanceSelectorMem_read64 :
    amm4MintBalanceSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold amm4MintBalanceSelectorMem
  rw [toByteArray_write_read_below_of_gap amm4MintBalanceSelectorWord solcFreePtrMem
    128 64 (by rw [solcFreePtrMem_size]) (by omega)
    (by rw [solcFreePtrMem_size]; native_decide), solcFreePtrMem_read64]

theorem amm4MintBalanceCalldataMem_read64 (I : ExecutionEnv) :
    (amm4MintBalanceCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4MintBalanceCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [amm4MintBalanceSelectorMem_size]; omega) (by omega),
    amm4MintBalanceSelectorMem_read64]

theorem amm4MintBalanceCalldataMem_read (I : ExecutionEnv) :
    (amm4MintBalanceCalldataMem I).readWithPadding 128 36 =
      balanceOfSelector ++ (UInt256.ofNat I.codeOwner).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [amm4MintBalanceCalldataMem_size]), amm4MintBalanceCalldataMem,
    write32_eq _ amm4MintBalanceSelectorMem 132 (by rw [toByteArray_size])
      (by rw [amm4MintBalanceSelectorMem_size]; omega)]
  have hAsz : (amm4MintBalanceSelectorMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, amm4MintBalanceSelectorMem_size]
    omega
  have hBsz : ((UInt256.ofNat I.codeOwner).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      (amm4MintBalanceSelectorMem.extract 0 132 ++
        (UInt256.ofNat I.codeOwner).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : (UInt256.ofNat I.codeOwner).toByteArray.extract 0 32 =
      (UInt256.ofNat I.codeOwner).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega),
    amm4MintBalanceSelectorMem_selector,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem amm4MintBalanceEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4MintBalanceCalldataMem I).readWithPadding 128 36) := by
  rw [amm4MintBalanceCalldataMem_read]
  have hword : EVM.word ↑I.codeOwner.val = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

noncomputable def amm4MintToken0PostCallMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (amm4MintBalanceCalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem amm4MintToken0PostCallMem_size_short (I : ExecutionEnv) {o : ByteArray}
    (hshort : o.size < 32) :
    (amm4MintToken0PostCallMem I o).size = 164 := by
  unfold amm4MintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, amm4MintBalanceCalldataMem_size]
  · rw [write_eq_gen o (amm4MintBalanceCalldataMem I) 128 o.size
      hzero le_rfl (by rw [amm4MintBalanceCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract,
      amm4MintBalanceCalldataMem_size]
    omega

theorem amm4MintToken0PostCallMem_read64_short (I : ExecutionEnv) {o : ByteArray}
    (hshort : o.size < 32) :
    (amm4MintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4MintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact amm4MintBalanceCalldataMem_read64 I
  · rw [write_read_below_gen_extend o (amm4MintBalanceCalldataMem I) 128
      o.size 64 hzero le_rfl
      (by rw [amm4MintBalanceCalldataMem_size]; omega) (by omega)]
    exact amm4MintBalanceCalldataMem_read64 I

theorem amm4MintToken0PostCallMem_size_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0PostCallMem I o).size = 164 := by
  unfold amm4MintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (amm4MintBalanceCalldataMem I) 128 32
    (by omega) hlo (by rw [amm4MintBalanceCalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract,
    amm4MintBalanceCalldataMem_size]
  omega

theorem amm4MintToken0PostCallMem_read64_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4MintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_read_below_gen_extend o (amm4MintBalanceCalldataMem I) 128 32 64
    (by omega) hlo (by rw [amm4MintBalanceCalldataMem_size]; omega) (by omega)]
  exact amm4MintBalanceCalldataMem_read64 I

theorem amm4MintToken0PostCallMem_read128_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0PostCallMem I o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold amm4MintToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen, write_eq_gen o (amm4MintBalanceCalldataMem I) 128 32
    (by omega) hlo (by rw [amm4MintBalanceCalldataMem_size]; omega)]
  have hprefix : ((amm4MintBalanceCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, amm4MintBalanceCalldataMem_size]
    omega
  have hsrc : (o.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((amm4MintBalanceCalldataMem I).extract 0 128 ++ o.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn : 128 + 32 ≤
      (((amm4MintBalanceCalldataMem I).extract 0 128 ++ o.extract 0 32) ++
        (amm4MintBalanceCalldataMem I).extract 160 (amm4MintBalanceCalldataMem I).size).size := by
    rw [ByteArray.size_append, hmemSize]
    omega
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_left _ _ 128 160 (by rw [hmemSize])]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix, show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

abbrev amm4MintReturndataRounded (o : ByteArray) : UInt256 :=
  UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩) (UInt256.lnot ⟨31⟩)

theorem amm4MintReturndataRounded_toNat (o : ByteArray)
    (hbound : o.size < 2 ^ 138) :
    (amm4MintReturndataRounded o).toNat = 32 * ((o.size + 31) / 32) := by
  unfold amm4MintReturndataRounded
  change (UInt256.land (UInt256.ofNat o.size + ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat = _
  rw [uland_toNat, lnot31_toNat, uadd_toNat]
  rw [UInt256.toNat_ofNat_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    Nat.mod_eq_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]
  exact nat_land_mask _ (by have h := hbound; norm_num at *; omega)

theorem amm4MintToken0FreePtr_toNat (o : ByteArray)
    (hbound : o.size < 2 ^ 138) :
    (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toNat =
      128 + 32 * ((o.size + 31) / 32) := by
  change (⟨128⟩ + amm4MintReturndataRounded o : UInt256).toNat = _
  rw [uadd_toNat, amm4MintReturndataRounded_toNat o hbound]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    Nat.mod_eq_of_lt (by have h := hbound; norm_num [UInt256.size] at *; omega)]

theorem amm4MintToken0FreePtr_bounds (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    160 ≤ (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toNat ∧
      (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toNat ≤ o.size + 159 := by
  rw [amm4MintToken0FreePtr_toNat o hbound]
  constructor
  · have hdiv : 1 ≤ (o.size + 31) / 32 := by omega
    omega
  · have hmul : 32 * ((o.size + 31) / 32) ≤ o.size + 31 := Nat.mul_div_le _ _
    omega

noncomputable def amm4MintToken0DecodeMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toByteArray.write 0
    (amm4MintToken0PostCallMem I o) 64 32

theorem amm4MintToken0DecodeMem_size_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0DecodeMem I o).size = 164 := by
  unfold amm4MintToken0DecodeMem
  exact toByteArray_write32_size_of_le (amm4MintToken0PostCallMem I o)
    (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o))
    64 164 164 (amm4MintToken0PostCallMem_size_long I hlo hhi)
    (by rw [amm4MintToken0PostCallMem_size_long I hlo hhi]; omega) (by omega)

theorem amm4MintToken0DecodeMem_read128_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0DecodeMem I o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold amm4MintToken0DecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [amm4MintToken0PostCallMem_size_long I hlo hhi]; omega)
    (by omega)
    (by rw [amm4MintToken0PostCallMem_size_long I hlo hhi]; omega)]
  exact amm4MintToken0PostCallMem_read128_long I hlo hhi

theorem amm4MintToken0DecodeMem_read64_long (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4MintToken0DecodeMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)) := by
  unfold amm4MintToken0DecodeMem
  exact toByteArray_write32_read_back _ _ _ (by
    rw [amm4MintToken0PostCallMem_size_long I hlo hhi]
    omega)


abbrev amm4MintToken0FreePtr (o : ByteArray) : UInt256 :=
  UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)

noncomputable def amm4MintToken1SelectorMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  amm4MintBalanceSelectorWord.toByteArray.write 0
    (amm4MintToken0DecodeMem I o) (amm4MintToken0FreePtr o).toNat 32

noncomputable def amm4MintToken1CalldataMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (amm4MintToken1SelectorMem I o) (amm4MintToken0FreePtr o + ⟨4⟩).toNat 32

theorem amm4MintToken0FreePtr_add4_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o + ⟨4⟩).toNat = (amm4MintToken0FreePtr o).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr : (amm4MintToken0FreePtr o).toNat ≤ o.size + 159 := by
    simpa only [amm4MintToken0FreePtr] using (amm4MintToken0FreePtr_bounds o hlo hbound).2
  norm_num [UInt256.size] at *
  omega

theorem amm4MintToken1SelectorMem_size (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o).toNat + 32 ≤ (amm4MintToken1SelectorMem I o).size := by
  unfold amm4MintToken1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4MintToken1SelectorMem_read64 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1SelectorMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o) := by
  unfold amm4MintToken1SelectorMem
  have hptr : 160 ≤ (amm4MintToken0FreePtr o).toNat := by
    simpa only [amm4MintToken0FreePtr] using (amm4MintToken0FreePtr_bounds o hlo hbound).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [amm4MintToken0DecodeMem_size_long I hlo (by norm_num [UInt256.size] at *; omega)]; omega)
    (by omega)]
  exact amm4MintToken0DecodeMem_read64_long I hlo (by norm_num [UInt256.size] at *; omega)

theorem amm4MintToken1SelectorMem_read4 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1SelectorMem I o).readWithPadding
      (amm4MintToken0FreePtr o).toNat 4 = balanceOfSelector := by
  unfold amm4MintToken1SelectorMem
  have h := toByteArray_write_read_window_no_gap amm4MintBalanceSelectorWord
    (amm4MintToken0DecodeMem I o) (amm4MintToken0FreePtr o).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : amm4MintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4MintToken1CalldataMem_size (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o).toNat + 36 ≤ (amm4MintToken1CalldataMem I o).size := by
  unfold amm4MintToken1CalldataMem
  rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4MintToken1CalldataMem_read64 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1CalldataMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o) := by
  unfold amm4MintToken1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound];
        exact le_trans (by omega) (amm4MintToken1SelectorMem_size I hlo hbound))
    (by rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound];
        have h : 160 ≤ (amm4MintToken0FreePtr o).toNat := by
          simpa only [amm4MintToken0FreePtr] using (amm4MintToken0FreePtr_bounds o hlo hbound).1
        omega)]
  exact amm4MintToken1SelectorMem_read64 I hlo hbound

theorem amm4MintToken1CalldataMem_read4 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1CalldataMem I o).readWithPadding
      (amm4MintToken0FreePtr o).toNat 4 = balanceOfSelector := by
  unfold amm4MintToken1CalldataMem
  rw [write32_read_below_len _ _ _ (amm4MintToken0FreePtr o).toNat 4
    (by rw [toByteArray_size])
    (by rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound];
        exact le_trans (by omega) (amm4MintToken1SelectorMem_size I hlo hbound))
    (by rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound])
    (by exact le_trans (by omega) (amm4MintToken1SelectorMem_size I hlo hbound))
    (by norm_num) (by norm_num)]
  exact amm4MintToken1SelectorMem_read4 I hlo hbound

theorem amm4MintToken1CalldataMem_read32 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1CalldataMem I o).readWithPadding
      (amm4MintToken0FreePtr o + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold amm4MintToken1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound]
    exact le_trans (by omega) (amm4MintToken1SelectorMem_size I hlo hbound))]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4MintToken1CalldataMem_read36 (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1CalldataMem I o).readWithPadding
      (amm4MintToken0FreePtr o).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _ (amm4MintToken0FreePtr o).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact amm4MintToken1CalldataMem_size I hlo hbound)]
  rw [amm4MintToken1CalldataMem_read4 I hlo hbound,
    ← amm4MintToken0FreePtr_add4_toNat o hlo hbound,
    amm4MintToken1CalldataMem_read32 I hlo hbound]

theorem amm4MintToken1CalldataMem_encode (I : ExecutionEnv) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4MintToken1CalldataMem I o).readWithPadding
        (amm4MintToken0FreePtr o).toNat 36) := by
  rw [amm4MintToken1CalldataMem_read36 I hlo hbound,
    ← amm4MintBalanceCalldataMem_read I]
  exact amm4MintBalanceEncode_eq I

/-- Mint writes the `balanceOf(address)` selector into scratch memory. -/
theorem amm4MintX_token0SelectorMem {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1549⟩ [amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1570⟩ [⟨128⟩, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      amm4MintBalanceSelectorMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1549⟩ := hreach
  have rd1557 := evm_run rd1549 with [push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1558 := evm_run rd1557 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd1569 := evm_run rd1558 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd1570 := evm_run rd1569 with [
    raw mstore 6 amm4MintBalanceSelectorMem (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [amm4MintBalanceSelectorMem, amm4MintBalanceSelectorWord] using rd1570⟩

/-- Solidity's address encoder writes this contract's address after the selector. -/
theorem amm4MintX_token0ArgMem {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1570⟩ [⟨128⟩, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      amm4MintBalanceSelectorMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1582⟩ [⟨164⟩, ⟨1889567281⟩, amm4MintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1570⟩ := hreach
  have rd5370 := evm_run rd1570 with [
    push1 ⟨4⟩, add, push2 ⟨1582⟩, swap2, swap1,
    push2 ⟨5370⟩, jump (by jump_dest)]
  have rd5355 := evm_run rd5370 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨5389⟩, push0, dup4, add, dup5, push2 ⟨5355⟩,
    jump (by jump_dest)]
  have rd4618 := evm_run rd5355 with [
    jumpdest, push2 ⟨5364⟩, dup2, push2 ⟨4618⟩, jump (by jump_dest)]
  have rd4587 := evm_run rd4618 with [
    jumpdest, push0, push2 ⟨4628⟩, dup3, push2 ⟨4587⟩, jump (by jump_dest)]
  have rd4628 := evm_run rd4587 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd5364 := evm_run rd4628 with [
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
  have rd5364' := rd5364
  rw [hclean] at rd5364'
  have rd5389 := evm_run rd5364' with [
    jumpdest, dup3,
    raw mstore 3 (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd1582 := evm_run rd5389 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide,
    show (⟨132⟩ : UInt256) + ⟨32⟩ = ⟨164⟩ from by decide] using rd1582⟩

/-- The first `STATICCALL` frame requests a 32-byte return for `balanceOf(this)`. -/
theorem amm4MintX_token0CallFrame {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1582⟩ [⟨164⟩, ⟨1889567281⟩, amm4MintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k C : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1594⟩ [gasWord, amm4MintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1582⟩ := hreach
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4MintBalanceCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((amm4MintBalanceCalldataMem I).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [amm4MintBalanceCalldataMem_size]; decide)
      (by decide) (amm4MintBalanceCalldataMem_read64 I)
  have rd1587 := evm_run rd1582 with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1588 := evm_run rd1587 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1594 := evm_run rd1588 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd1594'⟩ := rd1594
  exact ⟨gasWord, _, _, by
    simpa only [show (⟨164⟩ : UInt256) - ⟨128⟩ = ⟨36⟩ from by decide]
      using rd1594'⟩

/-- The EVM token0 `STATICCALL` and the Solm `balanceOf(this)` call share the same Θ witness. -/
theorem amm4MintX_token0Staticcall {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1594⟩ [gasWord, amm4MintToken0Word σ I, ⟨128⟩, ⟨36⟩,
          ⟨128⟩, ⟨32⟩, ⟨164⟩, ⟨1889567281⟩,
          amm4MintToken0Word σ I, ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintBalanceCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1595⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨1889567281⟩ ::
          amm4MintToken0Word σ I :: ⟨0⟩ :: ⟨0⟩ :: amm4MintToWord I :: ⟨301⟩ :: [sel])
        (o.write 0 (amm4MintBalanceCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k' C' ∧
      typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
        (AccountAddress.ofUInt256 (amm4MintToken0Word σ I)) "balanceOf" 0
        [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o) false ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1594⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd1595, hosz⟩ :=
    RD.solcStaticcall rd1594 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36) 128 32) =
        UInt256.ofNat 6 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd1595
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := amm4MintToken0Word σ I)
      (mem := amm4MintBalanceCalldataMem I) (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (amm4MintBalanceEncode_eq I) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((amm4MintBalanceCalldataMem I).readWithPadding 128 36).size = 36 := by
      rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
        (by rw [amm4MintBalanceCalldataMem_size])]
      rw [ByteArray.size_extract, amm4MintBalanceCalldataMem_size]
      omega
    have hbound :
        ((amm4MintBalanceCalldataMem I).readWithPadding 128 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (amm4MintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4MintBalanceCalldataMem I).readWithPadding 128 36)
      (I.depth + 1) I.header false (by simpa [initState] using hΘ) hbound

theorem amm4MintToken0StaticSlot {cA gh bl σ σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' : Substate} {z : Bool} {o : ByteArray}
    (hcall : typedCallViaEVM config (initState cA gh bl σ σ₀ g A I)
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ I)) "balanceOf" 0
      [.address I.codeOwner]
      (z, { initState cA gh bl σ σ₀ g A I with
        accountMap := σ', substate := A', createdAccounts := cA' }, o) false)
    (slot : UInt256) : solcSlotWord σ' I slot = solcSlotWord σ I slot := by
  have hstatic := typedCallViaEVM_static_accountStorageStateEq hcall
  have hslot := accountStorageStateEq_storage_findD hstatic I.codeOwner slot ⟨0⟩
  simpa [solcSlotWord, codeOwnerStorageWord, initState] using hslot.symm

/-- A failed first token call bubbles its return data and reverts. -/
theorem amm4MintX_token0CallFailed {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1595⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1602 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1609⟩,
    jumpiNT (by decide) ]
  have rd1605 := evm_run rd1602 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1606 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1605 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd1608 := evm_run rd1606 with [returndatasize, push0]
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1608 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

/-- The successful call clears its ABI call frame before decoding the returned word. -/
theorem amm4MintX_token0CallSucceeded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1595⟩ [⟨1⟩, ⟨164⟩, ⟨1889567281⟩, amm4MintToken0Word σ I,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel] mem aw o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1614⟩ [⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1609⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

theorem amm4MintX_token0ToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hmemSize : (amm4MintToken0PostCallMem I o).size = 164)
    (hread64 : (amm4MintToken0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1614⟩ [⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1645⟩,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4MintToken0PostCallMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((amm4MintToken0PostCallMem I o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide) hread64
  have rd1616 := evm_run rd with [push1 ⟨64⟩]
  have rd1617 := evm_run rd1616 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1631 := evm_run rd1617 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1632 := evm_run rd1631 with [
    raw mstore 0 (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5415 := evm_run rd1632 with [
    pop, dup2, add, swap1, push2 ⟨1645⟩, swap2, swap1,
    push2 ⟨5415⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [amm4MintToken0DecodeMem, amm4MintReturndataRounded] using rd5415⟩

theorem amm4MintX_token0ShortToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hshort : o.size < 32)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1614⟩ [⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1645⟩,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' :=
  amm4MintX_token0ToDecoder (amm4MintToken0PostCallMem_size_short I hshort)
    (amm4MintToken0PostCallMem_read64_short I hshort) rd

theorem amm4MintX_token0LongToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1614⟩ [⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0PostCallMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1645⟩,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' :=
  amm4MintX_token0ToDecoder (amm4MintToken0PostCallMem_size_long I hlo hhi)
    (amm4MintToken0PostCallMem_read64_long I hlo hhi) rd

theorem amm4MintX_token0DecodeShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hshort : o.size < 32)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1645⟩,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcheck := solcDecodeEndLenCheckShort_128_32 hshort
  have rd5424 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd4583 := evm_run rd5424 with [
    push2 ⟨5436⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨5435⟩, push2 ⟨4583⟩, jump (by jump_dest)]
  exact evm_run rd4583 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem amm4MintX_token0DecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1645⟩,
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1645⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  have hhi : o.size < UInt256.size := by
    exact lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo (by omega : o.size < 2 ^ 255)
  have rd5436 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨5436⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd5395 := evm_run rd5436 with [
    jumpdest, push0, push2 ⟨5449⟩, dup5, dup3, dup6, add,
    push2 ⟨5395⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (amm4MintToken0DecodeMem I o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((amm4MintToken0DecodeMem I o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      amm4MintToken0DecodeMem_read128_long I hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) ⟨128⟩ 164
        (amm4MintToken0DecodeMem_size_long I hlo hhi) (by decide) (by decide))
  have rd5398 := evm_run rd5395 with [jumpdest, push0, dup2]
  have rd5399 := evm_run rd5398 with [
    raw mload 0 v (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd4686 := evm_run rd5399 with [
    swap1, pop, push2 ⟨5409⟩, dup2, push2 ⟨4686⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5409⟩ := RD.amm4CheckUint256Identity rd4686 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5449 := evm_run rd5409 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1645 := evm_run rd5449 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd1645⟩

theorem amm4MintX_token0Decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1645⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1648⟩ [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, swap1, pop]⟩

theorem amm4MintX_toToken1Selector {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o mem : ByteArray} {aw : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1648⟩ [v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw o (cA', σ') k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1705⟩ [amm4MintToken1Word σ' I, ⟨0⟩,
        v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw o (cA', σ') k' C' := by
  have rd1653 := evm_run rd with [push0, push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd1654⟩ := rd1653.sload (by native_decide) (by evm_ov)
  have rd1705 := evm_run rd1654 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken1Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd1705⟩

/-- The source's token0 receiver is the same slot-3 address used by the call trace. -/

def amm4MintToken1SelectorWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 6 (amm4MintToken0FreePtr o).toNat 32)

theorem amm4MintX_token1SelectorMem {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1705⟩ [amm4MintToken1Word σ' I, ⟨0⟩,
        v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken0DecodeMem I o) (UInt256.ofNat 6) o (cA', σ') k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1726⟩ [amm4MintToken0FreePtr o, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1SelectorMem I o) (amm4MintToken1SelectorWords o)
      o (cA', σ') k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4MintToken0DecodeMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian ((amm4MintToken0DecodeMem I o).readWithPadding 64 32))) =
        amm4MintToken0FreePtr o :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6)
      (v := amm4MintToken0FreePtr o)
      (by rw [amm4MintToken0DecodeMem_size_long I hlo (by norm_num [UInt256.size] at *; omega)]; decide)
      (by decide)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          amm4MintToken0FreePtr] using
          amm4MintToken0DecodeMem_read64_long I hlo (by norm_num [UInt256.size] at *; omega))
  have rd1713 := evm_run rd with [push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1714 := evm_run rd1713 with [
    raw mload 0 (amm4MintToken0FreePtr o) (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1725 := evm_run rd1714 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := amm4MintToken1SelectorWords o
  have rd1726 := RD.mstore
    (Cₘ awSel - Cₘ (UInt256.ofNat 6))
    (amm4MintToken1SelectorMem I o) awSel rd1725 (by native_decide)
    (by intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awSel,
          amm4MintToken1SelectorWords,
          show (UInt256.ofNat 6).toNat = 6 from by decide])
    (by unfold amm4MintToken1SelectorMem; rfl)
    (by simp [awSel, amm4MintToken1SelectorWords,
          show (UInt256.ofNat 6).toNat = 6 from by decide])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4MintBalanceSelectorWord] using rd1726⟩

def amm4MintToken1CalldataWords (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4MintToken1SelectorWords o).toNat
    (amm4MintToken0FreePtr o + ⟨4⟩).toNat 32)

theorem amm4MintToken1SelectorWords_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1SelectorWords o).toNat = 5 + (o.size + 31) / 32 := by
  let n := (o.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using amm4MintToken0FreePtr_toNat o hbound
  have hM : MachineState.M 6 (amm4MintToken0FreePtr o).toNat 32 = 5 + n := by
    change max 6 (((amm4MintToken0FreePtr o).toNat + 32 + 31) / 32) = 5 + n
    rw [hptr]
    omega
  unfold amm4MintToken1SelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem amm4MintToken1CalldataWords_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken1CalldataWords o).toNat = 6 + (o.size + 31) / 32 := by
  let n := (o.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using amm4MintToken0FreePtr_toNat o hbound
  have harg : (amm4MintToken0FreePtr o + ⟨4⟩).toNat = 132 + 32 * n := by
    rw [amm4MintToken0FreePtr_add4_toNat o hlo hbound, hptr]
    omega
  have haw : (amm4MintToken1SelectorWords o).toNat = 5 + n := by
    simpa only [n] using amm4MintToken1SelectorWords_toNat o hlo hbound
  have hM : MachineState.M (amm4MintToken1SelectorWords o).toNat
      (amm4MintToken0FreePtr o + ⟨4⟩).toNat 32 = 6 + n := by
    change max (amm4MintToken1SelectorWords o).toNat
      (((amm4MintToken0FreePtr o + ⟨4⟩).toNat + 32 + 31) / 32) = 6 + n
    rw [harg, haw]
    omega
  unfold amm4MintToken1CalldataWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem amm4MintToken1CalldataWords_mload64_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4MintToken1CalldataWords o).toNat 64 32) =
      amm4MintToken1CalldataWords o := by
  have haw := amm4MintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (amm4MintToken1CalldataWords o).toNat 64 32 =
      (amm4MintToken1CalldataWords o).toNat := by
    change max (amm4MintToken1CalldataWords o).toNat ((64 + 32 + 31) / 32) = _
    have hn : 1 ≤ (o.size + 31) / 32 := by omega
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4MintToken1CalldataWords_mload64_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ amm4MintToken1CalldataWords o * ⟨32⟩ := by
  have haw := amm4MintToken1CalldataWords_toNat o hlo hbound
  have hmul : (amm4MintToken1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : (o.size + 31) / 32 ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4MintToken1CalldataWords o * ⟨32⟩).toNat ≤ 64 := by
    exact h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul] at hle
  have hn : 1 ≤ (o.size + 31) / 32 := by omega
  omega

theorem amm4MintX_token1ArgMem {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1726⟩ [amm4MintToken0FreePtr o, UInt256.ofNat I.codeOwner, ⟨1889567281⟩,
        amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1SelectorMem I o) (amm4MintToken1SelectorWords o)
      o (cA', σ') k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1738⟩ [amm4MintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
        amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1CalldataMem I o) (amm4MintToken1CalldataWords o)
      o (cA', σ') k' C' := by
  have rd5370 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨1738⟩, swap2, swap1,
    push2 ⟨5370⟩, jump (by jump_dest)]
  have rd5355 := evm_run rd5370 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨5389⟩, push0, dup4, add, dup5, push2 ⟨5355⟩,
    jump (by jump_dest)]
  have rd4618 := evm_run rd5355 with [
    jumpdest, push2 ⟨5364⟩, dup2, push2 ⟨4618⟩, jump (by jump_dest)]
  have rd4587 := evm_run rd4618 with [
    jumpdest, push0, push2 ⟨4628⟩, dup3, push2 ⟨4587⟩, jump (by jump_dest)]
  have rd4628 := evm_run rd4587 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd5364 := evm_run rd4628 with [
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
  have rd5364' := rd5364
  rw [hclean] at rd5364'
  have rd5389pre := evm_run rd5364' with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + amm4MintToken0FreePtr o + ⟨0⟩ =
      amm4MintToken0FreePtr o + ⟨4⟩ := by
    change ((⟨4⟩ : UInt256) + amm4MintToken0FreePtr o) + ⟨0⟩ = _
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) (amm4MintToken0FreePtr o)]
  have rd5389pre' := rd5389pre
  rw [hoff] at rd5389pre'
  let awArg := amm4MintToken1CalldataWords o
  have rd5389 := RD.mstore
    (Cₘ awArg - Cₘ (amm4MintToken1SelectorWords o))
    (amm4MintToken1CalldataMem I o) awArg rd5389pre' (by native_decide)
    (by intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awArg,
          amm4MintToken1CalldataWords])
    (by unfold amm4MintToken1CalldataMem; rfl)
    (by simp [awArg, amm4MintToken1CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1738 := evm_run rd5389 with [
    pop, pop, jump (by jump_dest), jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + amm4MintToken0FreePtr o + ⟨32⟩ =
      amm4MintToken0FreePtr o + ⟨36⟩ := by
    change ((⟨4⟩ : UInt256) + amm4MintToken0FreePtr o) + ⟨32⟩ = _
    rw [u256_add_comm (⟨4⟩ : UInt256) (amm4MintToken0FreePtr o),
      u256_add_assoc (amm4MintToken0FreePtr o) ⟨4⟩ ⟨32⟩,
      show (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ from by decide]
  exact ⟨_, _, by
    simpa only [hend, awArg] using rd1738⟩

theorem amm4MintX_token1CallFrame {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {k C : ℕ}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1738⟩ [amm4MintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
        amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1CalldataMem I o) (amm4MintToken1CalldataWords o)
      o (cA', σ') k C) :
    ∃ (gasWord : UInt256) (k' C' : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1750⟩ [gasWord, amm4MintToken1Word σ' I, amm4MintToken0FreePtr o,
          ⟨36⟩, amm4MintToken0FreePtr o, ⟨32⟩,
          amm4MintToken0FreePtr o + ⟨36⟩, ⟨1889567281⟩,
          amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
          amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintToken1CalldataMem I o) (amm4MintToken1CalldataWords o)
        o (cA', σ') k' C' := by
  let aw := amm4MintToken1CalldataWords o
  let fp := amm4MintToken0FreePtr o
  have hmem : 64 < (amm4MintToken1CalldataMem I o).size := by
    have hsz : fp.toNat + 36 ≤ (amm4MintToken1CalldataMem I o).size :=
      amm4MintToken1CalldataMem_size I hlo hbound
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, amm4MintToken0FreePtr] using (amm4MintToken0FreePtr_bounds o hlo hbound).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4MintToken1CalldataMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4MintToken1CalldataMem I o).readWithPadding 64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using amm4MintToken1CalldataWords_mload64_haw o hlo hbound)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        amm4MintToken1CalldataMem_read64 I hlo hbound)
  have rd1743 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      amm4MintToken1CalldataWords_mload64_same o hlo hbound
  have rd1744 := RD.mload 0 fp aw rd1743 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (amm4MintToken1CalldataWords o).toNat
            (⟨64⟩ : UInt256).toNat 32) = amm4MintToken1CalldataWords o from by
          simpa only [aw] using hsame]
        omega)
    hval
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1750 := evm_run rd1744 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd1750'⟩ := rd1750
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd1750'⟩


noncomputable def amm4MintToken1PostCallMem
    (I : ExecutionEnv) (o1 o2 : ByteArray) : ByteArray :=
  o2.write 0 (amm4MintToken1CalldataMem I o1) (amm4MintToken0FreePtr o1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat

theorem amm4MintToken1CallWords_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (amm4MintToken1CalldataWords o).toNat
          (amm4MintToken0FreePtr o).toNat 36)
        (amm4MintToken0FreePtr o).toNat 32) =
      amm4MintToken1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using amm4MintToken0FreePtr_toNat o hbound
  have haw : (amm4MintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using amm4MintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M
      (MachineState.M (amm4MintToken1CalldataWords o).toNat
        (amm4MintToken0FreePtr o).toNat 36)
      (amm4MintToken0FreePtr o).toNat 32 =
      (amm4MintToken1CalldataWords o).toNat := by
    change max (max (amm4MintToken1CalldataWords o).toNat
      (((amm4MintToken0FreePtr o).toNat + 36 + 31) / 32))
      (((amm4MintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4MintX_token1Staticcall {cA gh bl σ σ' σ₀ A A1 I} {g : Sat256}
    {sel v : UInt256} {o1 : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare}
    (hlo : 32 ≤ o1.size) (hbound : o1.size < 2 ^ 138)
    (hdepth : I.depth.val < 1024)
    (hframe : ∃ (gasWord : UInt256) (k C : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1750⟩ [gasWord, amm4MintToken1Word σ' I, amm4MintToken0FreePtr o1,
          ⟨36⟩, amm4MintToken0FreePtr o1, ⟨32⟩,
          amm4MintToken0FreePtr o1 + ⟨36⟩, ⟨1889567281⟩,
          amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
          amm4MintToWord I, ⟨301⟩, sel]
        (amm4MintToken1CalldataMem I o1) (amm4MintToken1CalldataWords o1)
        o1 (cA', σ') k C) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (o2 : ByteArray) (A2 : Substate) (k' C' : ℕ),
      RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1751⟩
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          (amm4MintToken0FreePtr o1 + ⟨36⟩) :: ⟨1889567281⟩ ::
          amm4MintToken1Word σ' I :: ⟨0⟩ :: v :: ⟨0⟩ ::
          amm4MintToWord I :: ⟨301⟩ :: [sel])
        (amm4MintToken1PostCallMem I o1 o2)
        (amm4MintToken1CalldataWords o1) o2 (cA'', σ'') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A1, createdAccounts := cA' }
        (AccountAddress.ofUInt256 (amm4MintToken1Word σ' I)) "balanceOf" 0
        [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ'', substate := A2, createdAccounts := cA'' }, o2) false ∧
      o2.size < UInt256.size ∧ o2.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd1750⟩ := hframe
  obtain ⟨cA'', σ'', z, o2, A_in, callGas, k', C', hΘpack, rd1751, hosz⟩ :=
    RD.solcStaticcall rd1750 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A2, hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M
        (MachineState.M (amm4MintToken1CalldataWords o1).toNat
          (amm4MintToken0FreePtr o1).toNat 36)
        (amm4MintToken0FreePtr o1).toNat 32) =
      amm4MintToken1CalldataWords o1 :=
    amm4MintToken1CallWords_same o1 hlo hbound
  refine ⟨cA'', σ'', z, o2, A2, k', C', ?_, ?_, hosz, ?_⟩
  · simpa [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      haw, amm4MintToken1PostCallMem] using rd1751
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := amm4MintToken1Word σ' I)
      (mem := amm4MintToken1CalldataMem I o1)
      (inOff := amm4MintToken0FreePtr o1) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (amm4MintToken1CalldataMem_encode I hlo hbound) ?_
    simpa [initState] using hΘ
  · have hinputSize :
        ((amm4MintToken1CalldataMem I o1).readWithPadding
          (amm4MintToken0FreePtr o1).toNat 36).size = 36 := by
      rw [amm4MintToken1CalldataMem_read36 I hlo hbound, ByteArray.size_append,
        toByteArray_size]
      decide
    have hinputBound :
        ((amm4MintToken1CalldataMem I o1).readWithPadding
          (amm4MintToken0FreePtr o1).toNat 36).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA' gh bl σ' σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (amm4MintToken1Word σ' I))
      (toExecute σ' (AccountAddress.ofUInt256 (amm4MintToken1Word σ' I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4MintToken1CalldataMem I o1).readWithPadding
        (amm4MintToken0FreePtr o1).toNat 36)
      (I.depth + 1) I.header false (by simpa [initState] using hΘ) hinputBound


theorem amm4MintX_token1CallFailed {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1751⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1758 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1765⟩,
    jumpiNT (by decide)]
  have rd1761 := evm_run rd1758 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd1762 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd1761 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd1764 := evm_run rd1762 with [returndatasize, push0]
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd1764 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem amm4MintX_token1CallSucceeded {cA gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel v : UInt256} {mem o1 o2 : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1751⟩ [⟨1⟩, amm4MintToken0FreePtr o1 + ⟨36⟩, ⟨1889567281⟩,
        amm4MintToken1Word σ' I, ⟨0⟩, v, ⟨0⟩,
        amm4MintToWord I, ⟨301⟩, sel] mem aw o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1770⟩ [⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      mem aw o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨1765⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

theorem amm4MintToken1PostCallMem_size_ge (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4MintToken0FreePtr o1).toNat + 36 ≤
      (amm4MintToken1PostCallMem I o1 o2).size := by
  unfold amm4MintToken1PostCallMem
  have hbase := amm4MintToken1CalldataMem_size I hlo1 hbound1
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen o2 (amm4MintToken1CalldataMem I o1)
        (amm4MintToken0FreePtr o1).toNat o2.size hzero le_rfl (by omega),
        ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write_eq_gen o2 (amm4MintToken1CalldataMem I o1)
      (amm4MintToken0FreePtr o1).toNat 32 (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
    omega

theorem amm4MintToken1PostCallMem_read64 (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4MintToken1PostCallMem I o1 o2).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o1) := by
  unfold amm4MintToken1PostCallMem
  have hbase := amm4MintToken1CalldataMem_size I hlo1 hbound1
  have hptr : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact amm4MintToken1CalldataMem_read64 I hlo1 hbound1
    · rw [write_read_below_gen o2 (amm4MintToken1CalldataMem I o1)
        (amm4MintToken0FreePtr o1).toNat o2.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact amm4MintToken1CalldataMem_read64 I hlo1 hbound1
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write32_read_below o2 (amm4MintToken1CalldataMem I o1)
      (amm4MintToken0FreePtr o1).toNat 64 hlong (by omega) (by omega)]
    exact amm4MintToken1CalldataMem_read64 I hlo1 hbound1

theorem amm4MintToken1PostCallMem_readPtr (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (amm4MintToken1PostCallMem I o1 o2).readWithPadding
      (amm4MintToken0FreePtr o1).toNat 32 = o2.extract 0 32 := by
  unfold amm4MintToken1PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
      (by decide) hlo2 hsize2
  rw [hlen]
  exact write32_read_back o2 (amm4MintToken1CalldataMem I o1)
    (amm4MintToken0FreePtr o1).toNat hlo2 (by
      have h := amm4MintToken1CalldataMem_size I hlo1 hbound1
      omega)

noncomputable def amm4MintToken1DecodeMem
    (I : ExecutionEnv) (o1 o2 : ByteArray) : ByteArray :=
  (UInt256.add (amm4MintToken0FreePtr o1) (amm4MintReturndataRounded o2)).toByteArray.write 0
    (amm4MintToken1PostCallMem I o1 o2) 64 32

theorem amm4MintToken1DecodeMem_size_ge (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4MintToken0FreePtr o1).toNat + 36 ≤
      (amm4MintToken1DecodeMem I o1 o2).size := by
  unfold amm4MintToken1DecodeMem
  let base := amm4MintToken1PostCallMem I o1 o2
  have hbase : (amm4MintToken0FreePtr o1).toNat + 36 ≤ base.size :=
    amm4MintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
  have hptr : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
  have hsz : ((UInt256.add (amm4MintToken0FreePtr o1)
      (amm4MintReturndataRounded o2)).toByteArray.write 0 base 64 32).size = base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem amm4MintToken1DecodeMem_readPtr (I : ExecutionEnv) {o1 o2 : ByteArray}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (amm4MintToken1DecodeMem I o1 o2).readWithPadding
      (amm4MintToken0FreePtr o1).toNat 32 = o2.extract 0 32 := by
  unfold amm4MintToken1DecodeMem
  have hbase := amm4MintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
  have hptr : 160 ≤ (amm4MintToken0FreePtr o1).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
  rw [write32_read_above _ _ 64 (amm4MintToken0FreePtr o1).toNat
    (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)]
  exact amm4MintToken1PostCallMem_readPtr I hlo1 hbound1 hlo2 hsize2

theorem amm4MintX_token1ToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1770⟩ [⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1PostCallMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [amm4MintToken0FreePtr o1,
        UInt256.add (amm4MintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨1801⟩, ⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k' C' := by
  let aw := amm4MintToken1CalldataWords o1
  let fp := amm4MintToken0FreePtr o1
  have hmem : 64 < (amm4MintToken1PostCallMem I o1 o2).size := by
    have hsz : fp.toNat + 36 ≤ (amm4MintToken1PostCallMem I o1 o2).size :=
      amm4MintToken1PostCallMem_size_ge I hlo1 hbound1 hsize2
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, amm4MintToken0FreePtr] using
        (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4MintToken1PostCallMem I o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4MintToken1PostCallMem I o1 o2).readWithPadding 64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using amm4MintToken1CalldataWords_mload64_haw o1 hlo1 hbound1)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        amm4MintToken1PostCallMem_read64 I hlo1 hbound1 hsize2)
  have hsame : UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) =
      aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      amm4MintToken1CalldataWords_mload64_same o1 hlo1 hbound1
  have rd1772 := evm_run rd with [push1 ⟨64⟩]
  have rd1773 := RD.mload 0 fp aw rd1772 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (amm4MintToken1CalldataWords o1).toNat
            (⟨64⟩ : UInt256).toNat 32) = amm4MintToken1CalldataWords o1 from by
          simpa only [aw] using hsame]
        omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1787 := evm_run rd1773 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1788 := RD.mstore 0 (amm4MintToken1DecodeMem I o1 o2) aw
    rd1787 (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (amm4MintToken1CalldataWords o1).toNat
            (⟨64⟩ : UInt256).toNat 32) = amm4MintToken1CalldataWords o1 from by
          simpa only [aw] using hsame]
        simp only [aw]
        omega)
    (by unfold amm4MintToken1DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5415 := evm_run rd1788 with [
    pop, dup2, add, swap1, push2 ⟨1801⟩, swap2, swap1,
    push2 ⟨5415⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, amm4MintReturndataRounded] using rd5415⟩

theorem amm4MintToken1LenCheckShort (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hshort : o2.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (amm4MintToken0FreePtr o1) (UInt256.ofNat o2.size))
        (amm4MintToken0FreePtr o1)) ⟨32⟩ = ⟨1⟩ := by
  have hptr : (amm4MintToken0FreePtr o1).toNat ≤ o1.size + 159 := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (amm4MintToken0FreePtr o1).toNat) (len := o2.size) (words := 1)
    (by simpa using hshort) (amm4MintToken0FreePtr o1).val.isLt
    (by
      have hcap : 2 ^ 138 + 200 < UInt256.size := by norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat, show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4MintToken1LenCheckOk (o1 o2 : ByteArray)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (amm4MintToken0FreePtr o1) (UInt256.ofNat o2.size))
        (amm4MintToken0FreePtr o1)) ⟨32⟩ = ⟨0⟩ := by
  have hptr : (amm4MintToken0FreePtr o1).toNat ≤ o1.size + 159 := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o1 hlo1 hbound1).2
  have hcheck := solcReturnStaticLenCheckOk
    (base := (amm4MintToken0FreePtr o1).toNat) (len := o2.size) (words := 1)
    (by simpa using hlo2) (by omega : o2.size < 2 ^ 255)
    (amm4MintToken0FreePtr o1).val.isLt
    (by
      have hcap : 2 ^ 139 + 200 < UInt256.size := by norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat, show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4MintX_token1DecodeShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hshort : o2.size < 32)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [amm4MintToken0FreePtr o1,
        UInt256.add (amm4MintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨1801⟩, ⟨0⟩, v, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcheck := amm4MintToken1LenCheckShort o1 o2 hlo1 hbound1 hshort
  have rd5424 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd4583 := evm_run rd5424 with [
    push2 ⟨5436⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨5435⟩, push2 ⟨4583⟩, jump (by jump_dest)]
  exact evm_run rd4583 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem amm4MintToken1CalldataWords_ptr_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ amm4MintToken0FreePtr o ≥ amm4MintToken1CalldataWords o * ⟨32⟩ := by
  let n := (o.size + 31) / 32
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using amm4MintToken0FreePtr_toNat o hbound
  have haw : (amm4MintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using amm4MintToken1CalldataWords_toNat o hlo hbound
  have hmul : (amm4MintToken1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4MintToken1CalldataWords o * ⟨32⟩).toNat ≤
      (amm4MintToken0FreePtr o).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem amm4MintToken1CalldataWords_mloadPtr_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4MintToken1CalldataWords o).toNat
      (amm4MintToken0FreePtr o).toNat 32) = amm4MintToken1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using amm4MintToken0FreePtr_toNat o hbound
  have haw : (amm4MintToken1CalldataWords o).toNat = 6 + n := by
    simpa only [n] using amm4MintToken1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (amm4MintToken1CalldataWords o).toNat
      (amm4MintToken0FreePtr o).toNat 32 =
      (amm4MintToken1CalldataWords o).toNat := by
    change max (amm4MintToken1CalldataWords o).toNat
      (((amm4MintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4MintX_token1DecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v1 : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨5415⟩ [amm4MintToken0FreePtr o1,
        UInt256.add (amm4MintToken0FreePtr o1) (UInt256.ofNat o2.size),
        ⟨1801⟩, ⟨0⟩, v1, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1801⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        ⟨0⟩, v1, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k' C' := by
  let aw := amm4MintToken1CalldataWords o1
  let fp := amm4MintToken0FreePtr o1
  let v2 : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32))
  have hcheck := amm4MintToken1LenCheckOk o1 o2 hlo1 hbound1 hlo2 hbound2
  have rd5436 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨5436⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd5395 := evm_run rd5436 with [
    jumpdest, push0, push2 ⟨5449⟩, dup5, dup3, dup6, add,
    push2 ⟨5395⟩, jump (by jump_dest)]
  have hmem : fp.toNat < (amm4MintToken1DecodeMem I o1 o2).size := by
    have hsz : fp.toNat + 36 ≤ (amm4MintToken1DecodeMem I o1 o2).size :=
      amm4MintToken1DecodeMem_size_ge I hlo1 hbound1
        (by exact lt_trans hbound2 (by norm_num [UInt256.size]))
    omega
  have hval :
      (if fp.toNat ≥ (amm4MintToken1DecodeMem I o1 o2).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4MintToken1DecodeMem I o1 o2).readWithPadding fp.toNat 32))) = v2 :=
    by
      have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
        simpa only [fp, aw] using amm4MintToken1CalldataWords_ptr_haw o1 hlo1 hbound1
      rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
        amm4MintToken1DecodeMem_readPtr I hlo1 hbound1 hlo2
          (by exact lt_trans hbound2 (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      amm4MintToken1CalldataWords_mloadPtr_same o1 hlo1 hbound1
  have rd5398 := evm_run rd5395 with [jumpdest, push0, dup2]
  have hzero : amm4MintToken0FreePtr o1 + ⟨0⟩ = amm4MintToken0FreePtr o1 := by
    rw [u256_add_comm, u256_zero_add]
  have rd5398' := rd5398
  rw [hzero] at rd5398'
  have rd5399 := RD.mload 0 v2 aw rd5398' (by native_decide)
    (by intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero]
        rw [show UInt256.ofNat
          (MachineState.M (amm4MintToken1CalldataWords o1).toNat
            (amm4MintToken0FreePtr o1).toNat 32) = amm4MintToken1CalldataWords o1 from by
          simpa only [aw, fp] using hsame]
        omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4686 := evm_run rd5399 with [
    swap1, pop, push2 ⟨5409⟩, dup2, push2 ⟨4686⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5409⟩ := RD.amm4CheckUint256Identity rd4686 (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5449 := evm_run rd5409 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1801 := evm_run rd5449 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v2, aw, fp] using rd1801⟩

theorem amm4MintX_token1Decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel v1 : UInt256} {o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1801⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        ⟨0⟩, v1, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1804⟩ [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        v1, ⟨0⟩, amm4MintToWord I, ⟨301⟩, sel]
      (amm4MintToken1DecodeMem I o1 o2) (amm4MintToken1CalldataWords o1)
      o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, swap1, pop]⟩

end Benchmarks.ActAmm4
