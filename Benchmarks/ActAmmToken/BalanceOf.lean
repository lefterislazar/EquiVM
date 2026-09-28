import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `balanceOf` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

abbrev balanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev balanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (balanceOfOwnerValue I)

def balanceOfCalldataSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat))

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (balanceOfCalldataSlot I) ⟨0⟩)

theorem tokenDecode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata =
        some (balanceOfStore I) := by
  show decodeCalldata ["owner"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfOwnerValue, balanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "owner") hsz36 hbig hcanon

theorem tokenDecode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "owner") hsz4 hshort

theorem tokenDecode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr, balanceOfOwnerWord, calldataWord] using
    decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "owner") hsz36 hbig hnc

theorem tokenDecode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "owner") hbig

theorem tokenBalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := contract, locals := balanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfCalldataSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [balanceOfStore, balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, balanceOfStore,
            balanceOfOwnerValue, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St,
          storageTypeStep?])
        (hloc := tokenConfig_storage_balanceOf
          (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)))]
      simp [balanceOfCalldataSlot, tokenStorageLocLoad_uint256])

theorem balanceOfMappingSlot_eq (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (balanceOfOwnerWord I) = balanceOfCalldataSlot I := by
  unfold balanceOfCalldataSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

set_option maxRecDepth 2000000 in
theorem tokenBalanceOfX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3253⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨392⟩, ⟨397⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨397⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨392⟩, swap2, swap1, push2 ⟨3253⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

set_option maxRecDepth 2000000 in
theorem tokenBalanceOfX_dec2906 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3287⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨392⟩, ⟨397⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨0⟩ := solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := tokenBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3274⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3287⟩, dup5, dup3, dup6, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem tokenBalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1851⟩
      (balanceOfOwnerWord I :: ⟨397⟩ :: [sel]) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenBalanceOfX_dec2906 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hreach
  obtain ⟨_, _, rd3287⟩ := RD.tokenDecodeAddrOk rd hcanon (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3287 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1851⟩, jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem tokenBalanceOfX_fromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hdecoded : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1851⟩
      (balanceOfOwnerWord I :: ⟨397⟩ :: [sel]) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  have hslot := balanceOfMappingSlot_eq I hcanon
  have hword :
      solcSlotWord σ I (solcMappingSlot ⟨1⟩ (balanceOfOwnerWord I)) =
        balanceOfWord σ I := by
    rw [hslot]
    rfl
  obtain ⟨_, _, rd1851⟩ := hdecoded
  obtain ⟨_, _, rd397⟩ := rd1851.tokenSingleMappingGetter (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  rw [hword] at rd397
  have rd3105 := evm_run rd397 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (solcMappingHashMem_mload64 ⟨1⟩ (balanceOfOwnerWord I))
      (by decide) (by evm_ov),
    push2 ⟨410⟩, swap2, swap1, push2 ⟨3105⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd410⟩ := rd3105.tokenRoutineEncodeUint256FromMem
    (memout := solcScratchReturnMem (solcMappingHashMem ⟨1⟩ (balanceOfOwnerWord I))
      (balanceOfWord σ I))
    (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd410 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide) mem_cost
      (solcScratchReturnMem_mload64 (balanceOfWord σ I)
        (solcMappingHashMem_size ⟨1⟩ (balanceOfOwnerWord I))
        (solcMappingHashMem_read64 ⟨1⟩ (balanceOfOwnerWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (balanceOfWord σ I)) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact solcScratchReturnMem_read128 (balanceOfWord σ I)
          (solcMappingHashMem_size ⟨1⟩ (balanceOfOwnerWord I)))
      (by evm_ov) ]

theorem tokenX_balanceOf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  have hdecoded := tokenBalanceOfX_decoded hsz36 hsize hszhi hcanon hreach
  exact tokenBalanceOfX_fromDecoded hcanon hdecoded

set_option maxRecDepth 2000000 in
theorem tokenBalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨1⟩ := solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := tokenBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3274⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨3273⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem tokenBalanceOfX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨1⟩ := solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := tokenBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3274⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨3273⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem tokenBalanceOfX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (balanceOfOwnerWord I)
      (UInt256.land (balanceOfOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨371⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tokenBalanceOfX_dec2906 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem tokenBalanceOfSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition])
    (post := [burnTransition, burnFromTransition, mintTransition,
      totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, balanceOfSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, allowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, approveSelectorBytes, hcd]; decide

theorem tokenBalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Ethereum.UInt256}
    (hcode : I.code = tokenBytecode)
    (hsize : I.calldata.size < Ethereum.UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨371⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenBalanceOfSelector_size hsel
  have hd := tokenDispatch_balanceOf (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hdec := tokenDecode_balanceOf_ok (I := I) hsz36 hbig hcanon
        have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfCalldataSlot I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (balanceOfStore I) balanceOfTransition.body
              (.returned { contract := contract, locals := balanceOfStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some [(.int (Int.ofNat (balanceOfWord σ_solm I).toNat))])) := by
          simpa [balanceOfWord, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using tokenBalanceOfBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
        exact (tokenX_balanceOf (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
            hAccounts
            (returnEquiv_of_encode (tokenUint256ReturnEncoding (balanceOfWord σ_evm I)))
      · have hdec := tokenDecode_balanceOf_none_noncanon (I := I) hsz36 hbig hcanon
        have hnc : UInt256.eq (balanceOfOwnerWord I)
            (UInt256.land (balanceOfOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (tokenBalanceOfX_noncanon (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_balanceOf_none_huge (I := I) hbigge
      exact (tokenBalanceOfX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := tokenDecode_balanceOf_none_short (I := I) hsz4 hshort
    exact (tokenBalanceOfX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
