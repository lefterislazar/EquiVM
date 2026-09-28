import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `allowance` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert
    "spender" (allowanceSpenderValue I)

def allowanceCalldataSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot
    (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))

theorem allowanceMappingSlot_eq (I : ExecutionEnv)
    (howner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hspender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (allowanceOwnerWord I))
      (allowanceSpenderWord I) = allowanceCalldataSlot I := by
  unfold allowanceCalldataSlot allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ howner,
    keyValueToWord_address_of_canonical _ hspender]

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (allowanceCalldataSlot I) ⟨0⟩)

def allowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
      .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] }

theorem tokenDecode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata =
        some (allowanceStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue,
    allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata)
      (x := "owner") (y := "spender") hsz68 hbig hcanonOwner hcanonSpender

theorem tokenDecode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem tokenDecode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem tokenDecode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem tokenDecode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

theorem allowanceStore_owner (I : ExecutionEnv) :
    (allowanceStore I).get? "owner" = some (allowanceOwnerValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_spender (I : ExecutionEnv) :
    (allowanceStore I).get? "spender" = some (allowanceSpenderValue I) := by
  rw [allowanceStore, store_get_self]

theorem tokenAllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceCalldataSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config
          { contract := contract, locals := allowanceStore I } evm
          (allowanceRef (.var "owner") (.var "spender")) =
            .ok (allowanceEvaledRef I) := by
        simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
          evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
          allowanceEvaledRef, allowanceOwnerValue, allowanceSpenderValue,
          allowanceStore_owner, allowanceStore_spender]
      have hty : storageTypeAt? contract.storage (allowanceEvaledRef I) =
          some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, contract, storageDecls, allowanceEvaledRef,
          uint256St, storageTypeStep?]
      have hloc : config.storage.layout (allowanceEvaledRef I) =
          fun _ => some (wordLoc (allowanceCalldataSlot I)) := by
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by
          rw [allowanceStore, store_get_ne _ _ (by decide),
            store_get_ne _ _ (by decide)]
          simp)
        (her := her) (hty := hty) (hloc := hloc)]
      simp [allowanceCalldataSlot, tokenStorageLocLoad_uint256])

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3358⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨536⟩, ⟨541⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨541⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨536⟩, swap2, swap1, push2 ⟨3358⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_dec2906_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3393⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨536⟩, ⟨541⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨0⟩ := solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3380⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3393⟩, dup6, dup3, dup7, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_dec2906_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3410⟩, ⟨32⟩, ⟨0⟩,
        allowanceOwnerWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨536⟩, ⟨541⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_dec2906_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd3393⟩ := RD.tokenDecodeAddrOk rd hcanonOwner
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3393 with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨3410⟩,
    dup6, dup3, dup7, add, push2 ⟨2906⟩, jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2800⟩
      [allowanceSpenderWord I, allowanceOwnerWord I, ⟨541⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_dec2906_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  obtain ⟨_, _, rd3410⟩ := RD.tokenDecodeAddrOk rd hcanonSpender
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3410 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨2800⟩, jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem tokenAllowanceX_fromDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hdecoded : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2800⟩ [allowanceSpenderWord I, allowanceOwnerWord I, ⟨541⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  have hslot := allowanceMappingSlot_eq I hcanonOwner hcanonSpender
  have hword :
      solcSlotWord σ I
        (solcMappingSlot (solcMappingSlot ⟨2⟩ (allowanceOwnerWord I))
          (allowanceSpenderWord I)) = allowanceWord σ I := by
    rw [hslot]
    rfl
  obtain ⟨_, _, rd2800⟩ := hdecoded
  obtain ⟨_, _, rd541⟩ := rd2800.tokenNestedMappingGetter (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  rw [hword] at rd541
  have rd3105 := evm_run rd541 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcNestedMappingHashMem_mload64 ⟨2⟩
        (allowanceOwnerWord I) (allowanceSpenderWord I))
      (by decide) (by evm_ov),
    push2 ⟨554⟩, swap2, swap1, push2 ⟨3105⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd554⟩ := rd3105.tokenRoutineEncodeUint256FromMem
    (memout := solcScratchReturnMem
      (solcNestedMappingHashMem ⟨2⟩ (allowanceOwnerWord I)
        (allowanceSpenderWord I)) (allowanceWord σ I))
    (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd554 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (solcScratchReturnMem_mload64 (allowanceWord σ I)
        (solcNestedMappingHashMem_size ⟨2⟩
          (allowanceOwnerWord I) (allowanceSpenderWord I))
        (solcNestedMappingHashMem_read64 ⟨2⟩
          (allowanceOwnerWord I) (allowanceSpenderWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (allowanceWord σ I))
      (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact solcScratchReturnMem_read128 (allowanceWord σ I)
          (solcNestedMappingHashMem_size ⟨2⟩
            (allowanceOwnerWord I) (allowanceSpenderWord I)))
      (by evm_ov) ]

theorem tokenX_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  have hdecoded := tokenAllowanceX_decoded hsz68 hsize hszhi hcanonOwner
    hcanonSpender hreach
  exact tokenAllowanceX_fromDecoded hcanonOwner hcanonSpender hdecoded

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3380⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3379⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem tokenAllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3380⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3379⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem tokenAllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (allowanceOwnerWord I)
      (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_dec2906_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem tokenAllowanceX_noncanon_spender {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (allowanceSpenderWord I)
      (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨515⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tokenAllowanceX_dec2906_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem tokenAllowanceSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [approveTransition, balanceOfTransition, burnTransition,
      burnFromTransition, mintTransition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, allowanceSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem tokenAllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Ethereum.UInt256}
    (hcode : I.code = tokenBytecode)
    (hsize : I.calldata.size < Ethereum.UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨515⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenAllowanceSelector_size hsel
  have hd := tokenDispatch_allowance (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases howner : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hspender : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := tokenDecode_allowance_ok (I := I)
            hsz68 hbig howner hspender
          have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (allowanceCalldataSlot I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (allowanceStore I) allowanceTransition.body
                (.returned { contract := contract, locals := allowanceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.int (Int.ofNat (allowanceWord σ_solm I).toNat))])) := by
            simpa [allowanceWord, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using tokenAllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (tokenX_allowance (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig howner hspender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
              hAccounts
              (returnEquiv_of_encode (tokenUint256ReturnEncoding
                (allowanceWord σ_evm I)))
        · have hdec := tokenDecode_allowance_none_noncanon_spender (I := I)
            hsz68 hbig howner hspender
          have hnc : UInt256.eq (allowanceSpenderWord I)
              (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hspender (solcAddrCanonical_of_clean he))
          exact (tokenAllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig howner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := tokenDecode_allowance_none_noncanon_owner (I := I)
          hsz68 hbig howner
        have hnc : UInt256.eq (allowanceOwnerWord I)
            (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => howner (solcAddrCanonical_of_clean he))
        exact (tokenAllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
          hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_allowance_none_huge (I := I) hbigge
      exact (tokenAllowanceX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := tokenDecode_allowance_none_short (I := I) hsz4 hshort
    exact (tokenAllowanceX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
