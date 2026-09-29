import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4ApproveSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4ApproveValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev amm4ApproveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat)

abbrev amm4ApproveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (amm4ApproveValueWord I).toNat)

abbrev amm4ApproveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (amm4ApproveSpenderValue I)).insert
    "value" (amm4ApproveValueValue I)

def amm4ApproveSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat))

theorem amm4ApproveSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (solcSourceWord I))
      (amm4ApproveSpenderWord I) = amm4ApproveSlot I := by
  unfold amm4ApproveSlot allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [amm4Source_keyValueToWord I.source,
    keyValueToWord_address_of_canonical _ hcanon]

def amm4ApprovePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if I.source = AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat then evm
  else Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4ApproveSlot I) (amm4ApproveValueWord I)

theorem amm4ApproveSpenderWord_eq_source (I : ExecutionEnv)
    (hcanon : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat = I.source) :
    amm4ApproveSpenderWord I = solcSourceWord I := by
  apply u256_inj
  have h := congrArg Fin.val hself
  change (amm4ApproveSpenderWord I).toNat % AccountAddress.size = I.source.val at h
  rw [Nat.mod_eq_of_lt (by simpa [EVM.addressModulus, AccountAddress.size] using hcanon)] at h
  rw [solcSourceWord_toNat]
  exact h

theorem amm4Decode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata =
        some (amm4ApproveStore I) := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, amm4ApproveStore, amm4ApproveSpenderValue,
    amm4ApproveValueValue, amm4ApproveSpenderWord, amm4ApproveValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hcanon

theorem amm4Decode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem amm4Decode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4ApproveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, amm4ApproveSpenderWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hnc

theorem amm4Decode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "spender") (y := "value") hbig

theorem amm4ApproveStore_spender (I : ExecutionEnv) :
    (amm4ApproveStore I).get? "spender" = some (amm4ApproveSpenderValue I) := by
  rw [amm4ApproveStore, store_get_ne _ _ (by decide), store_get_self]

theorem amm4ApproveStore_value (I : ExecutionEnv) :
    (amm4ApproveStore I).get? "value" = some (amm4ApproveValueValue I) := by
  rw [amm4ApproveStore, store_get_self]

theorem amm4ApproveStore_allowance (I : ExecutionEnv) :
    (amm4ApproveStore I).get? "allowance" = none := by
  rw [amm4ApproveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def amm4ApproveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat))] }

theorem amm4ApproveEvalStorageRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := amm4ApproveStore I } evm
      (allowanceRef sender (.var "spender")) = .ok (amm4ApproveEvaledRef evm I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4ApproveEvaledRef, amm4ApproveSpenderValue,
    amm4ApproveStore_spender, sender, envValue]

theorem amm4ApproveAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := amm4ApproveStore I } evm
      .storage (allowanceRef sender (.var "spender")) (amm4ApproveValueValue I) =
      .ok ({ contract := contract, locals := amm4ApproveStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (amm4ApproveSlot I) (amm4ApproveValueWord I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4ApproveStore_allowance I)
    (her := amm4ApproveEvalStorageRef evm I)
    (hty := by simp [storageTypeAt?, amm4ApproveEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by
      change (fun _ => some (wordLoc (allowanceSlot
        (.address evm.executionEnv.source)
        (.address (AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat))))) =
        (fun _ => some (wordLoc (amm4ApproveSlot I)))
      rw [hsrc]
      rfl)
  simpa [amm4ApproveValueValue] using
    amm4StorageLocStore_uint256 evm (amm4ApproveSlot I) (amm4ApproveValueWord I)

theorem amm4ApproveCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4ApproveStore I } evm
      (.binary .ne (.var "spender") sender) =
        .ok (.bool (!(amm4ApproveSpenderValue I == .address I.source))) := by
  have hspender : evalExpr? config
      { contract := contract, locals := amm4ApproveStore I } evm (.var "spender") =
      .ok (amm4ApproveSpenderValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((amm4ApproveStore I).get? "spender") = .ok (amm4ApproveSpenderValue I)
    rw [amm4ApproveStore_spender]
    rfl
  have hsender : evalExpr? config
      { contract := contract, locals := amm4ApproveStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hspender, hsender, evalBinaryOp?]

theorem amm4ApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (amm4ApproveStore I)
      approveTransition.body
      (.returned { contract := contract, locals := amm4ApproveStore I }
        (amm4ApprovePostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  by_cases hself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat = I.source
  · have hcond : evalExpr? config
        { contract := contract, locals := amm4ApproveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool false) := by
      simpa [amm4ApproveSpenderValue, BEq.beq, hself] using amm4ApproveCond evm I hsrc
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ?_
    simpa [amm4ApprovePostState, hself.symm] using
      (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := amm4ApproveStore I } evm
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := amm4ApproveStore I }
            evm (some [(.bool true)])))
  · have hcond : evalExpr? config
        { contract := contract, locals := amm4ApproveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool true) := by
      simpa [amm4ApproveSpenderValue, BEq.beq, hself] using amm4ApproveCond evm I hsrc
    let post := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (amm4ApproveSlot I) (amm4ApproveValueWord I)
    have hthen : ExecBlock config { contract := contract, locals := amm4ApproveStore I }
        evm [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")]
        (.ok { contract := contract, locals := amm4ApproveStore I } post) := by
      exact ExecBlock.consNormal
        (ExecStmt.assign (by
          simp [evalExpr?, EvalResult.ofOption])
          (amm4ApproveAssign evm I hsrc)) ExecBlock.nil
    have hstmt : ExecStmt config { contract := contract, locals := amm4ApproveStore I }
        evm (.ite (.binary .ne (.var "spender") sender)
          [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")] [])
        (.ok { contract := contract, locals := amm4ApproveStore I } post) :=
      ExecStmt.iteTrue hcond hthen
    refine ExecBlock.consNormal hstmt ?_
    have hnot : I.source ≠ AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat :=
      Ne.symm hself
    simpa [amm4ApprovePostState, hnot, post]
      using (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := amm4ApproveStore I } post
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := amm4ApproveStore I }
            post (some [(.bool true)])))

theorem amm4ApproveX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4728⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨175⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨170⟩, swap2, swap1, push2 ⟨4728⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4ApproveX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨4763⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨4750⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨4763⟩, dup6, dup3, dup7, add, push2 ⟨4657⟩,
    jump (by jump_dest) ]⟩

theorem amm4ApproveX_dec5576 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4763⟩
      [amm4ApproveSpenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4ApproveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.amm4DecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem amm4ApproveX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨4780⟩, ⟨32⟩,
        ⟨0⟩, amm4ApproveSpenderWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨170⟩, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4ApproveX_dec5576 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨4780⟩,
    dup6, dup3, dup7, add, push2 ⟨4708⟩, jump (by jump_dest) ]⟩

theorem amm4ApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨523⟩
      [amm4ApproveValueWord I, amm4ApproveSpenderWord I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4708⟩ := amm4ApproveX_dec5521_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd4686 := evm_run rd4708 with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨4722⟩, dup2, push2 ⟨4686⟩, jump (by jump_dest) ]
  have rd4695 := evm_run rd4686 with [
    jumpdest, push2 ⟨4695⟩, dup2, push2 ⟨4677⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]
  have heq : UInt256.eq (amm4ApproveValueWord I) (amm4ApproveValueWord I) = ⟨1⟩ :=
    u256_eq_refl _
  have rd4705 := evm_run rd4695 with [
    jumpdest, dup2, eq, push2 ⟨4705⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd4705 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨523⟩, jump (by jump_dest) ]⟩

theorem amm4ApproveX_condition {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨572⟩
      [UInt256.eq (amm4ApproveSpenderWord I) (solcSourceWord I), ⟨0⟩,
        amm4ApproveValueWord I, amm4ApproveSpenderWord I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd523⟩ := amm4ApproveX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hspenderClean : UInt256.land solcAddrMask (amm4ApproveSpenderWord I) =
      amm4ApproveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd572 := evm_run rd523 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, eq ]
  rw [hsourceClean, hspenderClean] at rd572
  exact ⟨_, _, rd572⟩

theorem amm4ApproveX_return {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨701⟩
      [⟨0⟩, amm4ApproveValueWord I, amm4ApproveSpenderWord I, ⟨175⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I) acc
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd701⟩ := h
  have rd175 := evm_run rd701 with [
    jumpdest, push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest) ]
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd4816 := evm_run rd175 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨188⟩, swap2, swap1, push2 ⟨4816⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd188⟩ := RD.amm4RoutineEncodeBoolFromMem
    (memout := amm4WordReturnMem mem (⟨1⟩ : UInt256))
    rd4816 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd188 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (amm4WordReturnMem_mload64_of_size96 ⟨1⟩ hmem hread)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact amm4WordReturnMem_read128_of_size96 ⟨1⟩ hmem)
      (by evm_ov) ]

theorem amm4ApproveX_self {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat = I.source)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd572⟩ := amm4ApproveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hword := amm4ApproveSpenderWord_eq_source I hcanonSpender hself
  have heq : UInt256.eq (amm4ApproveSpenderWord I) (solcSourceWord I) = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl _
  have rd701 := evm_run rd572 with [
    push2 ⟨701⟩, jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact amm4ApproveX_return solcFreePtrMem_size solcFreePtrMem_read64
    ⟨_, _, rd701⟩

theorem amm4ApproveX_nonself_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨701⟩
      [⟨0⟩, amm4ApproveValueWord I, amm4ApproveSpenderWord I, ⟨175⟩, sel]
      (twoWordHashMem (amm4ApproveSpenderWord I)
        (solcMappingSlot ⟨2⟩ (solcSourceWord I))
        (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (amm4ApproveSlot I) (amm4ApproveValueWord I))
      k C := by
  obtain ⟨_, _, rd572⟩ := amm4ApproveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hwordNe : amm4ApproveSpenderWord I ≠ solcSourceWord I := by
    intro heq
    apply hnotself
    rw [heq, solcSource_ofNat]
  have hnc : UInt256.eq (amm4ApproveSpenderWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hwordNe (uInt256_eq_one_eq he))
  have rd576 := evm_run rd572 with [
    push2 ⟨701⟩, jumpiNT (by rw [hnc]) ]
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd664₀ := evm_run rd576 with [
    dup2, push1 ⟨2⟩, push0, caller, push20 solcAddrMask, and,
    push20 solcAddrMask, and ]
  have rd625 := rd664₀
  rw [hsourceClean, hsourceClean] at rd625
  obtain ⟨_, _, rd638⟩ := RD.amm4MappingHashSuffix rd625 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hspenderClean : UInt256.land solcAddrMask (amm4ApproveSpenderWord I) =
      amm4ApproveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd723₀ := evm_run rd638 with [
    push0, dup6, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd684 := rd723₀
  rw [hspenderClean, hspenderClean] at rd684
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd736⟩ := RD.amm4MappingHashSuffix rd684 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by
      simpa [amm4ApproveSlot_eq_solc I hcanonSpender] using
        (twoWordHashMem_solcMappingSlot
          (solcMappingSlot ⟨2⟩ (solcSourceWord I))
          (amm4ApproveSpenderWord I) hinnerSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd738 := evm_run rd736 with [dup2, swap1]
  obtain ⟨_, _, rd739⟩ := rd738.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd739 with [pop]⟩

theorem amm4ApproveX_nonself {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (amm4ApproveSlot I) (amm4ApproveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have h := amm4ApproveX_nonself_stored (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonSpender hnotself hreach
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hinnerRead :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  exact amm4ApproveX_return
    (twoWordHashMem_size_96 _ _ hinnerSize)
    (twoWordHashMem_read64 _ _ hinnerSize hinnerRead) h

theorem amm4ApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨4750⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨4749⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4ApproveX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨4750⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨4749⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4ApproveX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (amm4ApproveSpenderWord I)
      (UInt256.land (amm4ApproveSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4ApproveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4ApproveSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some approveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition])
    (post := [balanceOfTransition, burnTransition, mintTransition,
      swapTransition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4ApproveSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
  decide

/-- The approve wrapper, entered at PC 160, refines its Solm transition. -/
theorem amm4ApproveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨149⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4ApproveSelector_size hsel
  have hd := amm4Dispatch_approve (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (amm4ApproveSpenderWord I).toNat < EVM.addressModulus
      · have hdec := amm4Decode_approve_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hbody := amm4ApproveBodyReturns evmS I
          (by simp only [evmS, initState]; exact hwv)
          (by rfl)
        have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
            (some [(.bool true)]) approveTransition.returnType :=
          returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
        by_cases hself : AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat = I.source
        · have hpost : amm4ApprovePostState evmS I = evmS := by
            simp [amm4ApprovePostState, hself.symm]
          have hbody' : ExecTransitionBody config contract evmS (amm4ApproveStore I)
              approveTransition.body
              (.returned { contract := contract, locals := amm4ApproveStore I }
                evmS (some [(.bool true)])) := by
            simpa [hpost] using hbody
          exact (amm4ApproveX_self (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hself hreach)
            |>.reEquivExecution hcode hd hdec hbody' hAccounts henc
        · have hnot : I.source ≠ AccountAddress.ofNat (amm4ApproveSpenderWord I).toNat :=
            Ne.symm hself
          have hσPost : EVMStateEquiv
              (amm4ApprovePostState evmE I) (amm4ApprovePostState evmS I) := by
            simp only [amm4ApprovePostState, if_neg hnot]
            exact hσ.storageStore_codeOwner (amm4ApproveSlot I) rfl
          exact (amm4ApproveX_nonself (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hperm hcanon hself hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by simp [evmE, amm4ApprovePostState, hnot, initState,
                storageStore_createdAccounts])
              (accountMapEquiv.of_eq (by
                simp [evmE, amm4ApprovePostState, hnot, initState,
                  storageStore_accountMap]))
              hσPost henc
      · have hdec := amm4Decode_approve_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (amm4ApproveSpenderWord I)
            (UInt256.land (amm4ApproveSpenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (amm4ApproveX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := amm4Decode_approve_none_huge (I := I) hbigge
      exact (amm4ApproveX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := amm4Decode_approve_none_short (I := I) hsz4 hshort
    exact (amm4ApproveX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm4
