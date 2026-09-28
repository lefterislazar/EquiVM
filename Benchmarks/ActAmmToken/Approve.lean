import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `approve` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev approveSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev approveValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev approveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

abbrev approveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveValueWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (approveSpenderValue I)).insert
    "value" (approveValueValue I)

def approveSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))

theorem approveSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (solcSourceWord I))
      (approveSpenderWord I) = approveSlot I := by
  unfold approveSlot allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [tokenSource_keyValueToWord I.source,
    keyValueToWord_address_of_canonical _ hcanon]

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if I.source = AccountAddress.ofNat (approveSpenderWord I).toNat then evm
  else Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (approveSlot I) (approveValueWord I)

theorem approveSpenderWord_eq_source (I : ExecutionEnv)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (approveSpenderWord I).toNat = I.source) :
    approveSpenderWord I = solcSourceWord I := by
  apply u256_inj
  have h := congrArg Fin.val hself
  change (approveSpenderWord I).toNat % AccountAddress.size = I.source.val at h
  rw [Nat.mod_eq_of_lt
    (by simpa [EVM.addressModulus, AccountAddress.size] using hcanon)] at h
  rw [solcSourceWord_toNat]
  exact h

theorem tokenDecode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata =
        some (approveStore I) := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, approveStore, approveSpenderValue,
    approveValueValue, approveSpenderWord, approveValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hcanon

theorem tokenDecode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_short
    (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem tokenDecode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, approveSpenderWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hnc

theorem tokenDecode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_huge
    (cd := I.calldata) (x := "spender") (y := "value") hbig

theorem approveStore_spender (I : ExecutionEnv) :
    (approveStore I).get? "spender" = some (approveSpenderValue I) := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_self]

theorem approveStore_value (I : ExecutionEnv) :
    (approveStore I).get? "value" = some (approveValueValue I) := by
  rw [approveStore, store_get_self]

theorem approveStore_allowance (I : ExecutionEnv) :
    (approveStore I).get? "allowance" = none := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def approveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))] }

theorem approveEvalStorageRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := approveStore I } evm
      (allowanceRef sender (.var "spender")) = .ok (approveEvaledRef evm I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, approveEvaledRef, approveSpenderValue,
    approveStore_spender, sender, envValue]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "spender")) (approveValueValue I) =
      .ok ({ contract := contract, locals := approveStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (approveSlot I) (approveValueWord I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := approveStore_allowance I)
    (her := approveEvalStorageRef evm I)
    (hty := by simp [storageTypeAt?, approveEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by
      change (fun _ => some (wordLoc (allowanceSlot
        (.address evm.executionEnv.source)
        (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))))) =
        (fun _ => some (wordLoc (approveSlot I)))
      rw [hsrc]
      rfl)
  simpa [approveValueValue] using
    tokenStorageLocStore_uint256 evm (approveSlot I) (approveValueWord I)

theorem approveCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.binary .ne (.var "spender") sender) =
        .ok (.bool (!(approveSpenderValue I == .address I.source))) := by
  have hspender : evalExpr? config
      { contract := contract, locals := approveStore I } evm (.var "spender") =
      .ok (approveSpenderValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((approveStore I).get? "spender") = .ok (approveSpenderValue I)
    rw [approveStore_spender]
    rfl
  have hsender : evalExpr? config
      { contract := contract, locals := approveStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hspender, hsender, evalBinaryOp?]

theorem approveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (approveStore I)
      approveTransition.body
      (.returned { contract := contract, locals := approveStore I }
        (approvePostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  by_cases hself : AccountAddress.ofNat (approveSpenderWord I).toNat = I.source
  · have hcond : evalExpr? config
        { contract := contract, locals := approveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool false) := by
      simpa [approveSpenderValue, BEq.beq, hself] using approveCond evm I hsrc
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ?_
    simpa [approvePostState, hself.symm] using
      (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := approveStore I } evm
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := approveStore I }
            evm (some [(.bool true)])))
  · have hcond : evalExpr? config
        { contract := contract, locals := approveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool true) := by
      simpa [approveSpenderValue, BEq.beq, hself] using approveCond evm I hsrc
    let post := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (approveSlot I) (approveValueWord I)
    have hthen : ExecBlock config { contract := contract, locals := approveStore I }
        evm [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")]
        (.ok { contract := contract, locals := approveStore I } post) := by
      exact ExecBlock.consNormal
        (ExecStmt.assign (by
          simp [evalExpr?, EvalResult.ofOption])
          (approveAssign evm I hsrc)) ExecBlock.nil
    have hstmt : ExecStmt config { contract := contract, locals := approveStore I }
        evm (.ite (.binary .ne (.var "spender") sender)
          [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")] [])
        (.ok { contract := contract, locals := approveStore I } post) :=
      ExecStmt.iteTrue hcond hthen
    refine ExecBlock.consNormal hstmt ?_
    have hnot : I.source ≠ AccountAddress.ofNat (approveSpenderWord I).toNat :=
      Ne.symm hself
    simpa [approvePostState, hnot, post]
      using (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := approveStore I } post
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := approveStore I }
            post (some [(.bool true)])))

-- LIBRARY CANDIDATE: Reasoning.Memory, one-word ABI return from 96-byte scratch memory.
noncomputable def approveWordReturnMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem approveWordReturnMem_size_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (approveWordReturnMem mem val).size = 160 := by
  unfold approveWordReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hmem,
    ByteArray_zeroes_size, toByteArray_size]

theorem approveWordReturnMem_read64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (approveWordReturnMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveWordReturnMem
  rw [toByteArray_write_read_below_of_gap val mem 128 64
    (by rw [hmem]) (by omega)
    (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread

theorem approveWordReturnMem_mload64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveWordReturnMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((approveWordReturnMem mem val).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveWordReturnMem_size_of_size96 val hmem]; decide)
    (by decide) (by simpa using approveWordReturnMem_read64_of_size96 val hmem hread)

theorem approveWordReturnMem_read128_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (approveWordReturnMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold approveWordReturnMem
  exact toByteArray_write_read_back_of_gap val mem 128
    (by rw [hmem]; exact lt_usize _ (by norm_num))


theorem approveX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2977⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨175⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨170⟩, swap2, swap1, push2 ⟨2977⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem approveX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3012⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := approveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3012⟩, dup6, dup3, dup7, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

theorem approveX_dec5576 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3012⟩
      [approveSpenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := approveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem approveX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3029⟩, ⟨32⟩,
        ⟨0⟩, approveSpenderWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := approveX_dec5576 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨3029⟩,
    dup6, dup3, dup7, add, push2 ⟨2957⟩, jump (by jump_dest) ]⟩

theorem approveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨563⟩
      [approveValueWord I, approveSpenderWord I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5521⟩ := approveX_dec5521_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd5499 := evm_run rd5521 with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨2971⟩, dup2, push2 ⟨2935⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨2944⟩, dup2, push2 ⟨2926⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]
  have heq : UInt256.eq (approveValueWord I) (approveValueWord I) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨2954⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨563⟩, jump (by jump_dest) ]⟩

theorem approveX_condition {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨612⟩
      [UInt256.eq (approveSpenderWord I) (solcSourceWord I), ⟨0⟩,
        approveValueWord I, approveSpenderWord I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd562⟩ := approveX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hspenderClean : UInt256.land solcAddrMask (approveSpenderWord I) =
      approveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd611 := evm_run rd562 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, eq ]
  rw [hsourceClean, hspenderClean] at rd611
  exact ⟨_, _, rd611⟩

theorem approveX_return {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨741⟩
      [⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨175⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd740⟩ := h
  have rd186 := evm_run rd740 with [
    jumpdest, push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest) ]
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd5629 := evm_run rd186 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨188⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd199⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := approveWordReturnMem mem (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd199 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (approveWordReturnMem_mload64_of_size96 ⟨1⟩ hmem hread)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact approveWordReturnMem_read128_of_size96 ⟨1⟩ hmem)
      (by evm_ov) ]

theorem approveX_self {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (approveSpenderWord I).toNat = I.source)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd611⟩ := approveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hword := approveSpenderWord_eq_source I hcanonSpender hself
  have heq : UInt256.eq (approveSpenderWord I) (solcSourceWord I) = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl _
  have rd740 := evm_run rd611 with [
    push2 ⟨741⟩, jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact approveX_return solcFreePtrMem_size solcFreePtrMem_read64
    ⟨_, _, rd740⟩

theorem approveX_nonself_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (approveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨741⟩
      [⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨175⟩, sel]
      (twoWordHashMem (approveSpenderWord I)
        (solcMappingSlot ⟨2⟩ (solcSourceWord I))
        (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (approveSlot I) (approveValueWord I))
      k C := by
  obtain ⟨_, _, rd611⟩ := approveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hwordNe : approveSpenderWord I ≠ solcSourceWord I := by
    intro heq
    apply hnotself
    rw [heq, solcSource_ofNat]
  have hnc : UInt256.eq (approveSpenderWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hwordNe (uInt256_eq_one_eq he))
  have rd615 := evm_run rd611 with [
    push2 ⟨741⟩, jumpiNT (by rw [hnc]) ]
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd664₀ := evm_run rd615 with [
    dup2, push1 ⟨2⟩, push0, caller, push20 solcAddrMask, and,
    push20 solcAddrMask, and ]
  have rd664 := rd664₀
  rw [hsourceClean, hsourceClean] at rd664
  obtain ⟨_, _, rd677⟩ := RD.tokenMappingHashSuffix rd664 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hspenderClean : UInt256.land solcAddrMask (approveSpenderWord I) =
      approveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd723₀ := evm_run rd677 with [
    push0, dup6, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd723 := rd723₀
  rw [hspenderClean, hspenderClean] at rd723
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd736⟩ := RD.tokenMappingHashSuffix rd723 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by
      simpa [approveSlot_eq_solc I hcanonSpender] using
        (twoWordHashMem_solcMappingSlot
          (solcMappingSlot ⟨2⟩ (solcSourceWord I))
          (approveSpenderWord I) hinnerSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd738 := evm_run rd736 with [dup2, swap1]
  obtain ⟨_, _, rd739⟩ := rd738.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd739 with [pop]⟩

theorem approveX_nonself {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (approveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveSlot I) (approveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have h := approveX_nonself_stored (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonSpender hnotself hreach
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hinnerRead :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  exact approveX_return
    (twoWordHashMem_size_96 _ _ hinnerSize)
    (twoWordHashMem_read64 _ _ hinnerSize hinnerRead) h

theorem approveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := approveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem approveX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := approveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem approveX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (approveSpenderWord I)
      (UInt256.land (approveSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := approveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)


theorem approveSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some approveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition])
    (post := [balanceOfTransition, burnTransition, burnFromTransition,
      mintTransition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, approveSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, allowanceSelectorBytes, hcd]
  decide

/-- The approve wrapper, entered at PC 149, refines its Solm transition. -/
theorem tokenApproveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨149⟩ [tokenSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := approveSelector_size hsel
  have hd := tokenDispatch_approve (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (approveSpenderWord I).toNat < EVM.addressModulus
      · have hdec := tokenDecode_approve_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hbody := approveBodyReturns evmS I
          (by simp only [evmS, initState]; exact hwv)
          (by rfl)
        have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
            (some [(.bool true)]) approveTransition.returnType :=
          returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
        by_cases hself : AccountAddress.ofNat (approveSpenderWord I).toNat = I.source
        · have hpost : approvePostState evmS I = evmS := by
            simp [approvePostState, hself.symm]
          have hbody' : ExecTransitionBody config contract evmS (approveStore I)
              approveTransition.body
              (.returned { contract := contract, locals := approveStore I }
                evmS (some [(.bool true)])) := by
            simpa [hpost] using hbody
          exact (approveX_self (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hself hreach)
            |>.reEquivExecution hcode hd hdec hbody' hAccounts henc
        · have hnot : I.source ≠ AccountAddress.ofNat (approveSpenderWord I).toNat :=
            Ne.symm hself
          have hσPost : EVMStateEquiv
              (approvePostState evmE I) (approvePostState evmS I) := by
            simp only [approvePostState, if_neg hnot]
            exact hσ.storageStore_codeOwner (approveSlot I) rfl
          exact (approveX_nonself (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hperm hcanon hself hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by simp [evmE, approvePostState, hnot, initState,
                storageStore_createdAccounts])
              (accountMapEquiv.of_eq (by
                simp [evmE, approvePostState, hnot, initState,
                  storageStore_accountMap]))
              hσPost henc
      · have hdec := tokenDecode_approve_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (approveSpenderWord I)
            (UInt256.land (approveSpenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (approveX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_approve_none_huge (I := I) hbigge
      exact (approveX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := tokenDecode_approve_none_short (I := I) hsz4 hshort
    exact (approveX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec
end Benchmarks.ActAmmToken
