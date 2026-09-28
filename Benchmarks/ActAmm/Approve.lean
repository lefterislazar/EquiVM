import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammApproveSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammApproveValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev ammApproveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammApproveSpenderWord I).toNat)

abbrev ammApproveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (ammApproveValueWord I).toNat)

abbrev ammApproveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (ammApproveSpenderValue I)).insert
    "value" (ammApproveValueValue I)

def ammApproveSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (ammApproveSpenderWord I).toNat))

theorem ammApproveSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammApproveSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (solcSourceWord I))
      (ammApproveSpenderWord I) = ammApproveSlot I := by
  unfold ammApproveSlot allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [ammSource_keyValueToWord I.source,
    keyValueToWord_address_of_canonical _ hcanon]

def ammApprovePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if I.source = AccountAddress.ofNat (ammApproveSpenderWord I).toNat then evm
  else Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammApproveSlot I) (ammApproveValueWord I)

theorem ammApproveSpenderWord_eq_source (I : ExecutionEnv)
    (hcanon : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat = I.source) :
    ammApproveSpenderWord I = solcSourceWord I := by
  apply u256_inj
  have h := congrArg Fin.val hself
  change (ammApproveSpenderWord I).toNat % AccountAddress.size = I.source.val at h
  rw [Nat.mod_eq_of_lt (by simpa [EVM.addressModulus, AccountAddress.size] using hcanon)] at h
  rw [solcSourceWord_toNat]
  exact h

theorem ammDecode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammApproveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata =
        some (ammApproveStore I) := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, ammApproveStore, ammApproveSpenderValue,
    ammApproveValueValue, ammApproveSpenderWord, ammApproveValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hcanon

theorem ammDecode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem ammDecode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammApproveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, ammApproveSpenderWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hnc

theorem ammDecode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "spender") (y := "value") hbig

theorem ammApproveStore_spender (I : ExecutionEnv) :
    (ammApproveStore I).get? "spender" = some (ammApproveSpenderValue I) := by
  rw [ammApproveStore, store_get_ne _ _ (by decide), store_get_self]

theorem ammApproveStore_value (I : ExecutionEnv) :
    (ammApproveStore I).get? "value" = some (ammApproveValueValue I) := by
  rw [ammApproveStore, store_get_self]

theorem ammApproveStore_allowance (I : ExecutionEnv) :
    (ammApproveStore I).get? "allowance" = none := by
  rw [ammApproveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def ammApproveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (ammApproveSpenderWord I).toNat))] }

theorem ammApproveEvalStorageRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := ammApproveStore I } evm
      (allowanceRef sender (.var "spender")) = .ok (ammApproveEvaledRef evm I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammApproveEvaledRef, ammApproveSpenderValue,
    ammApproveStore_spender, sender, envValue]

theorem ammApproveAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := ammApproveStore I } evm
      .storage (allowanceRef sender (.var "spender")) (ammApproveValueValue I) =
      .ok ({ contract := contract, locals := ammApproveStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (ammApproveSlot I) (ammApproveValueWord I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammApproveStore_allowance I)
    (her := ammApproveEvalStorageRef evm I)
    (hty := by simp [storageTypeAt?, ammApproveEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by
      change (fun _ => some (wordLoc (allowanceSlot
        (.address evm.executionEnv.source)
        (.address (AccountAddress.ofNat (ammApproveSpenderWord I).toNat))))) =
        (fun _ => some (wordLoc (ammApproveSlot I)))
      rw [hsrc]
      rfl)
  simpa [ammApproveValueValue] using
    ammStorageLocStore_uint256 evm (ammApproveSlot I) (ammApproveValueWord I)

theorem ammApproveCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammApproveStore I } evm
      (.binary .ne (.var "spender") sender) =
        .ok (.bool (!(ammApproveSpenderValue I == .address I.source))) := by
  have hspender : evalExpr? config
      { contract := contract, locals := ammApproveStore I } evm (.var "spender") =
      .ok (ammApproveSpenderValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((ammApproveStore I).get? "spender") = .ok (ammApproveSpenderValue I)
    rw [ammApproveStore_spender]
    rfl
  have hsender : evalExpr? config
      { contract := contract, locals := ammApproveStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hspender, hsender, evalBinaryOp?]

theorem ammApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (ammApproveStore I)
      approveTransition.body
      (.returned { contract := contract, locals := ammApproveStore I }
        (ammApprovePostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  by_cases hself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat = I.source
  · have hcond : evalExpr? config
        { contract := contract, locals := ammApproveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool false) := by
      simpa [ammApproveSpenderValue, BEq.beq, hself] using ammApproveCond evm I hsrc
    refine ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ?_
    simpa [ammApprovePostState, hself.symm] using
      (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := ammApproveStore I } evm
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := ammApproveStore I }
            evm (some [(.bool true)])))
  · have hcond : evalExpr? config
        { contract := contract, locals := ammApproveStore I } evm
        (.binary .ne (.var "spender") sender) = .ok (.bool true) := by
      simpa [ammApproveSpenderValue, BEq.beq, hself] using ammApproveCond evm I hsrc
    let post := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (ammApproveSlot I) (ammApproveValueWord I)
    have hthen : ExecBlock config { contract := contract, locals := ammApproveStore I }
        evm [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")]
        (.ok { contract := contract, locals := ammApproveStore I } post) := by
      exact ExecBlock.consNormal
        (ExecStmt.assign (by
          simp [evalExpr?, EvalResult.ofOption])
          (ammApproveAssign evm I hsrc)) ExecBlock.nil
    have hstmt : ExecStmt config { contract := contract, locals := ammApproveStore I }
        evm (.ite (.binary .ne (.var "spender") sender)
          [.assign .storage (allowanceRef sender (.var "spender")) (.var "value")] [])
        (.ok { contract := contract, locals := ammApproveStore I } post) :=
      ExecStmt.iteTrue hcond hthen
    refine ExecBlock.consNormal hstmt ?_
    have hnot : I.source ≠ AccountAddress.ofNat (ammApproveSpenderWord I).toNat :=
      Ne.symm hself
    simpa [ammApprovePostState, hnot, post]
      using (ExecBlock.consReturn (ExecStmt.return (by
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure])) :
        ExecBlock config { contract := contract, locals := ammApproveStore I } post
          [.return [(.boolLit true)]]
          (.returned { contract := contract, locals := ammApproveStore I }
            post (some [(.bool true)])))

theorem ammApproveX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5541⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨181⟩, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨186⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨181⟩, swap2, swap1, push2 ⟨5541⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammApproveX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5576⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨181⟩, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5563⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5576⟩, dup6, dup3, dup7, add, push2 ⟨5470⟩,
    jump (by jump_dest) ]⟩

theorem ammApproveX_dec5576 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5576⟩
      [ammApproveSpenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨181⟩, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammApproveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem ammApproveX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5521⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5593⟩, ⟨32⟩,
        ⟨0⟩, ammApproveSpenderWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨181⟩, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammApproveX_dec5576 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5593⟩,
    dup6, dup3, dup7, add, push2 ⟨5521⟩, jump (by jump_dest) ]⟩

theorem ammApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩
      [ammApproveValueWord I, ammApproveSpenderWord I, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5521⟩ := ammApproveX_dec5521_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd5499 := evm_run rd5521 with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨5535⟩, dup2, push2 ⟨5499⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨5508⟩, dup2, push2 ⟨5490⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]
  have heq : UInt256.eq (ammApproveValueWord I) (ammApproveValueWord I) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨5518⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨562⟩, jump (by jump_dest) ]⟩

theorem ammApproveX_condition {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨611⟩
      [UInt256.eq (ammApproveSpenderWord I) (solcSourceWord I), ⟨0⟩,
        ammApproveValueWord I, ammApproveSpenderWord I, ⟨186⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd562⟩ := ammApproveX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hspenderClean : UInt256.land solcAddrMask (ammApproveSpenderWord I) =
      ammApproveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd611 := evm_run rd562 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, eq ]
  rw [hsourceClean, hspenderClean] at rd611
  exact ⟨_, _, rd611⟩

theorem ammApproveX_return {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨740⟩
      [⟨0⟩, ammApproveValueWord I, ammApproveSpenderWord I, ⟨186⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I) acc
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
    push2 ⟨199⟩, swap2, swap1, push2 ⟨5629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd199⟩ := RD.ammRoutineEncodeBoolFromMem
    (memout := ammWordReturnMem mem (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd199 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (ammWordReturnMem_mload64_of_size96 ⟨1⟩ hmem hread)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact ammWordReturnMem_read128_of_size96 ⟨1⟩ hmem)
      (by evm_ov) ]

theorem ammApproveX_self {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat = I.source)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd611⟩ := ammApproveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hword := ammApproveSpenderWord_eq_source I hcanonSpender hself
  have heq : UInt256.eq (ammApproveSpenderWord I) (solcSourceWord I) = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl _
  have rd740 := evm_run rd611 with [
    push2 ⟨740⟩, jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ammApproveX_return solcFreePtrMem_size solcFreePtrMem_read64
    ⟨_, _, rd740⟩

theorem ammApproveX_nonself_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨740⟩
      [⟨0⟩, ammApproveValueWord I, ammApproveSpenderWord I, ⟨186⟩, sel]
      (twoWordHashMem (ammApproveSpenderWord I)
        (solcMappingSlot ⟨2⟩ (solcSourceWord I))
        (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (ammApproveSlot I) (ammApproveValueWord I))
      k C := by
  obtain ⟨_, _, rd611⟩ := ammApproveX_condition (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hwordNe : ammApproveSpenderWord I ≠ solcSourceWord I := by
    intro heq
    apply hnotself
    rw [heq, solcSource_ofNat]
  have hnc : UInt256.eq (ammApproveSpenderWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hwordNe (uInt256_eq_one_eq he))
  have rd615 := evm_run rd611 with [
    push2 ⟨740⟩, jumpiNT (by rw [hnc]) ]
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd664₀ := evm_run rd615 with [
    dup2, push1 ⟨2⟩, push0, caller, push20 solcAddrMask, and,
    push20 solcAddrMask, and ]
  have rd664 := rd664₀
  rw [hsourceClean, hsourceClean] at rd664
  obtain ⟨_, _, rd677⟩ := RD.ammMappingHashSuffix rd664 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hspenderClean : UInt256.land solcAddrMask (ammApproveSpenderWord I) =
      ammApproveSpenderWord I := solcAddrMask_clean_left hcanonSpender
  have rd723₀ := evm_run rd677 with [
    push0, dup6, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd723 := rd723₀
  rw [hspenderClean, hspenderClean] at rd723
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd736⟩ := RD.ammMappingHashSuffix rd723 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by
      simpa [ammApproveSlot_eq_solc I hcanonSpender] using
        (twoWordHashMem_solcMappingSlot
          (solcMappingSlot ⟨2⟩ (solcSourceWord I))
          (ammApproveSpenderWord I) hinnerSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd738 := evm_run rd736 with [dup2, swap1]
  obtain ⟨_, _, rd739⟩ := rd738.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd739 with [pop]⟩

theorem ammApproveX_nonself {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (ammApproveSpenderWord I).toNat < EVM.addressModulus)
    (hnotself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat ≠ I.source)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (ammApproveSlot I) (ammApproveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have h := ammApproveX_nonself_stored (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonSpender hnotself hreach
  have hinnerSize :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hinnerRead :
      (twoWordHashMem (solcSourceWord I) ⟨2⟩ solcFreePtrMem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  exact ammApproveX_return
    (twoWordHashMem_size_96 _ _ hinnerSize)
    (twoWordHashMem_read64 _ _ hinnerSize hinnerRead) h

theorem ammApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5563⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5562⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammApproveX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := ammApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5563⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5562⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammApproveX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (ammApproveSpenderWord I)
      (UInt256.land (ammApproveSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨160⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammApproveX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammApproveSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some approveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition])
    (post := [balanceOfTransition, burnTransition, mintTransition,
      swap0Transition, swap1Transition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammApproveSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, ammAllowanceSelectorBytes, hcd]
  decide

/-- The approve wrapper, entered at PC 160, refines its Solm transition. -/
theorem ammApproveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨160⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammApproveSelector_size hsel
  have hd := ammDispatch_approve (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (ammApproveSpenderWord I).toNat < EVM.addressModulus
      · have hdec := ammDecode_approve_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hbody := ammApproveBodyReturns evmS I
          (by simp only [evmS, initState]; exact hwv)
          (by rfl)
        have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
            (some [(.bool true)]) approveTransition.returnType :=
          returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
        by_cases hself : AccountAddress.ofNat (ammApproveSpenderWord I).toNat = I.source
        · have hpost : ammApprovePostState evmS I = evmS := by
            simp [ammApprovePostState, hself.symm]
          have hbody' : ExecTransitionBody config contract evmS (ammApproveStore I)
              approveTransition.body
              (.returned { contract := contract, locals := ammApproveStore I }
                evmS (some [(.bool true)])) := by
            simpa [hpost] using hbody
          exact (ammApproveX_self (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hself hreach)
            |>.reEquivExecution hcode hd hdec hbody' hAccounts henc
        · have hnot : I.source ≠ AccountAddress.ofNat (ammApproveSpenderWord I).toNat :=
            Ne.symm hself
          have hσPost : EVMStateEquiv
              (ammApprovePostState evmE I) (ammApprovePostState evmS I) := by
            simp only [ammApprovePostState, if_neg hnot]
            exact hσ.storageStore_codeOwner (ammApproveSlot I) rfl
          exact (ammApproveX_nonself (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hperm hcanon hself hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by simp [evmE, ammApprovePostState, hnot, initState,
                storageStore_createdAccounts])
              (accountMapEquiv.of_eq (by
                simp [evmE, ammApprovePostState, hnot, initState,
                  storageStore_accountMap]))
              hσPost henc
      · have hdec := ammDecode_approve_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (ammApproveSpenderWord I)
            (UInt256.land (ammApproveSpenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ammApproveX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ammDecode_approve_none_huge (I := I) hbigge
      exact (ammApproveX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := ammDecode_approve_none_short (I := I) hsz4 hshort
    exact (ammApproveX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm
