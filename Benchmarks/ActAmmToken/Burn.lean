import Benchmarks.ActAmmToken.Decode
import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `burn` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev burnValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev burnValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnValueWord I).toNat)

abbrev burnStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "value" (burnValueValue I)

def burnBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.source)

theorem burnBalanceSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (solcSourceWord I) = burnBalanceSlot I := by
  unfold burnBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [tokenSource_keyValueToWord I.source]

def burnSupplyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩

def burnSupplyDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnSupplyWord evm).toNat - (burnValueWord I).toNat)

def burnAfterSupply (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (burnSupplyDebitWord evm I)

def burnBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (burnAfterSupply evm I) evm.executionEnv.codeOwner
    (burnBalanceSlot I)

def burnBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnBalanceWord evm I).toNat - (burnValueWord I).toNat)

def burnPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (burnAfterSupply evm I) evm.executionEnv.codeOwner
    (burnBalanceSlot I) (burnBalanceDebitWord evm I)

def burnEvmSupplyMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩
    (UInt256.sub (solcSlotWord σ I ⟨0⟩) (burnValueWord I))

def burnEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (burnEvmSupplyMap σ I) (burnBalanceSlot I)
    (UInt256.sub (solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I))
      (burnValueWord I))

noncomputable def burnBalanceHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem

noncomputable def burnFinalHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩ (burnBalanceHashMem I)

theorem tokenDecode_burn_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata =
        some (burnStore I) := by
  show decodeCalldata ["value"] [uint256] I.calldata = _
  simpa [uint256, abiUInt256, burnStore, burnValueValue, burnValueWord,
    calldataWord] using decodeCalldata_uint256_ok
      (cd := I.calldata) (x := "value") hsz36 hbig

theorem tokenDecode_burn_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using decodeCalldata_uint256_none_short
    (cd := I.calldata) (x := "value") hshort

theorem tokenDecode_burn_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [uint256] I.calldata = none
  simpa [uint256, abiUInt256] using decodeCalldata_uint256_none_huge
    (cd := I.calldata) (x := "value") hbig

theorem burnStore_value (I : ExecutionEnv) :
    (burnStore I).get? "value" = some (burnValueValue I) := by
  rw [burnStore, store_get_self]

theorem burnStore_totalSupply (I : ExecutionEnv) :
    (burnStore I).get? "totalSupply" = none := by
  rw [burnStore, store_get_ne _ _ (by decide)]
  simp

theorem burnStore_balanceOf (I : ExecutionEnv) :
    (burnStore I).get? "balanceOf" = none := by
  rw [burnStore, store_get_ne _ _ (by decide)]
  simp

theorem burnEvalSupplyRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := burnStore I } evm
      totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
    EvalResult.bind, pure, bind]

theorem burnEvalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat (burnSupplyWord evm).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := burnStore_totalSupply I)
    (her := burnEvalSupplyRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)]
  simp [burnSupplyWord, tokenStorageLocLoad_uint256]

theorem burnEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.var "value") = .ok (burnValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, burnStore_value]

theorem burnEvalSupplyDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (burnValueWord I).toNat ≤ (burnSupplyWord evm).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (checkedSub (.storage totalSupplyRef) (.var "value")) =
        .ok (.int (Int.ofNat
          ((burnSupplyWord evm).toNat - (burnValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok (burnEvalSupply evm I)
    (burnEvalValue evm I) hle (burnSupplyWord evm).val.isLt

theorem burnEvalSupplyDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (burnSupplyWord evm).toNat < (burnValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (checkedSub (.storage totalSupplyRef) (.var "value")) = .revert := by
  exact tokenEvalCheckedSub_revert (burnEvalSupply evm I)
    (burnEvalValue evm I) hunder

theorem burnSupplyDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (burnSupplyDebitWord evm I).toNat =
      (burnSupplyWord evm).toNat - (burnValueWord I).toNat := by
  unfold burnSupplyDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (burnSupplyWord evm).val.isLt

theorem burnSupplyDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (burnValueWord I).toNat ≤ (burnSupplyWord evm).toNat) :
    burnSupplyDebitWord evm I =
      UInt256.sub (burnSupplyWord evm) (burnValueWord I) := by
  apply u256_inj
  rw [burnSupplyDebitWord_toNat evm I, usub_toNat hle]

theorem burnAssignSupply (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := burnStore I } evm
      .storage totalSupplyRef
      (.int (Int.ofNat (burnSupplyDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := burnStore I },
        burnAfterSupply evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := burnStore_totalSupply I)
    (her := burnEvalSupplyRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)
  simpa [burnAfterSupply] using
    tokenStorageLocStore_uint256 evm ⟨0⟩ (burnSupplyDebitWord evm I)

theorem burnAfterSupply_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (burnAfterSupply evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [burnAfterSupply, storageStore_executionEnv]

theorem burnAfterSupply_source (evm : EVM.State) (I : ExecutionEnv) :
    (burnAfterSupply evm I).executionEnv.source = evm.executionEnv.source := by
  simp [burnAfterSupply, storageStore_executionEnv]

def burnBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

theorem burnEvalBalanceRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := burnStore I } evm
      (balanceOfRef sender) = .ok (burnBalanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, burnBalanceRef, sender, envValue, hsrc]

theorem burnEvalBalance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := burnStore I } evm
      (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (burnBalanceSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := burnStore_balanceOf I)
    (her := burnEvalBalanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      burnBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [burnBalanceSlot, tokenStorageLocLoad_uint256]

theorem burnEvalBalanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (burnValueWord I).toNat ≤ (burnBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I }
      (burnAfterSupply evm I)
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) =
        .ok (.int (Int.ofNat
          ((burnBalanceWord evm I).toNat - (burnValueWord I).toNat))) := by
  have hload := burnEvalBalance (burnAfterSupply evm I) I
    ((burnAfterSupply_source evm I).trans hsrc)
  rw [burnAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedSub_ok hload
    (burnEvalValue (burnAfterSupply evm I) I) hle (burnBalanceWord evm I).val.isLt

theorem burnEvalBalanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (burnBalanceWord evm I).toNat < (burnValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := burnStore I }
      (burnAfterSupply evm I)
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) = .revert := by
  have hload := burnEvalBalance (burnAfterSupply evm I) I
    ((burnAfterSupply_source evm I).trans hsrc)
  rw [burnAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedSub_revert hload
    (burnEvalValue (burnAfterSupply evm I) I) hunder

theorem burnBalanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (burnBalanceDebitWord evm I).toNat =
      (burnBalanceWord evm I).toNat - (burnValueWord I).toNat := by
  unfold burnBalanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (burnBalanceWord evm I).val.isLt

theorem burnBalanceDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (burnValueWord I).toNat ≤ (burnBalanceWord evm I).toNat) :
    burnBalanceDebitWord evm I =
      UInt256.sub (burnBalanceWord evm I) (burnValueWord I) := by
  apply u256_inj
  rw [burnBalanceDebitWord_toNat evm I, usub_toNat hle]

theorem burnAssignBalance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := burnStore I }
      (burnAfterSupply evm I) .storage (balanceOfRef sender)
      (.int (Int.ofNat (burnBalanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := burnStore I },
        burnPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := burnStore_balanceOf I)
    (her := burnEvalBalanceRef (burnAfterSupply evm I) I
      ((burnAfterSupply_source evm I).trans hsrc))
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      burnBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [burnPostState, burnAfterSupply_codeOwner evm I] using
    tokenStorageLocStore_uint256 (burnAfterSupply evm I)
      (burnBalanceSlot I) (burnBalanceDebitWord evm I)

theorem burnBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsupply : (burnValueWord I).toNat ≤ (burnSupplyWord evm).toNat)
    (hbalance : (burnValueWord I).toNat ≤ (burnBalanceWord evm I).toNat) :
    ExecTransitionBody config contract evm (burnStore I)
      burnTransition.body
      (.returned { contract := contract, locals := burnStore I }
        (burnPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hdebit := burnEvalSupplyDebit_ok evm I hsupply
  have hassign := burnAssignSupply evm I
  rw [burnSupplyDebitWord_toNat evm I] at hassign
  refine ExecBlock.consNormal (ExecStmt.assign hdebit hassign) ?_
  have hdebit2 := burnEvalBalanceDebit_ok evm I hsrc hbalance
  have hassign2 := burnAssignBalance evm I hsrc
  rw [burnBalanceDebitWord_toNat evm I] at hassign2
  refine ExecBlock.consNormal (ExecStmt.assign hdebit2 hassign2) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem burnBodyReverts_supply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunder : (burnSupplyWord evm).toNat < (burnValueWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I)
      burnTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.assignExprRevert (burnEvalSupplyDebit_revert evm I hunder))

theorem burnBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hsupply : (burnValueWord I).toNat ≤ (burnSupplyWord evm).toNat)
    (hunder : (burnBalanceWord evm I).toNat < (burnValueWord I).toNat) :
    ExecTransitionBody config contract evm (burnStore I)
      burnTransition.body .reverted := by
  have hdebit := burnEvalSupplyDebit_ok evm I hsupply
  have hassign := burnAssignSupply evm I
  rw [burnSupplyDebitWord_toNat evm I] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hdebit hassign) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (burnEvalBalanceDebit_revert evm I hsrc hunder))

set_option maxRecDepth 2000000 in
theorem tokenBurnX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3210⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨349⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨344⟩, swap2, swap1, push2 ⟨3210⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

set_option maxRecDepth 2000000 in
theorem tokenBurnX_dec2906 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3244⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨0⟩ := solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := tokenBurnX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3231⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3244⟩, dup5, dup3, dup6, add, push2 ⟨2957⟩,
    jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem tokenBurnX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1685⟩
      (burnValueWord I :: ⟨349⟩ :: [sel]) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenBurnX_dec2906 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hreach
  obtain ⟨_, _, rd3287⟩ := RD.tokenDecodeUint256Ok rd (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3287 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1685⟩, jump (by jump_dest) ]⟩

theorem burnX_supplyLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1690⟩
      [solcSlotWord σ I ⟨0⟩, burnValueWord I, ⟨0⟩,
        burnValueWord I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenBurnX_decoded hsz36 hsize hszhi hreach
  have rdLoad := evm_run rd with [jumpdest, push0, dup2, push0]
  obtain ⟨_, _, rdLoaded⟩ := rdLoad.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rdLoaded⟩

theorem burnX_supplyDebit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hle : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1699⟩
      [UInt256.sub (solcSlotWord σ I ⟨0⟩) (burnValueWord I), ⟨0⟩,
        burnValueWord I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := burnX_supplyLoad hsz36 hsize hszhi hreach
  have rdSub := evm_run rd with [
    push2 ⟨1699⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubOk rdSub hle (by jump_dest) (by evm_ov)

theorem burnX_supplyUnderflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hunder : (solcSlotWord σ I ⟨0⟩).toNat < (burnValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := burnX_supplyLoad hsz36 hsize hszhi hreach
  have rdSub := evm_run rd with [
    push2 ⟨1699⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubUnderflow rdSub hunder (by evm_ov)

theorem burnX_supplyStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hle : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1705⟩
      [⟨0⟩, burnValueWord I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmSupplyMap σ I) k C := by
  obtain ⟨_, _, rd⟩ := burnX_supplyDebit hsz36 hsize hszhi hle hreach
  have rdStore := evm_run rd with [jumpdest, push0, dup2, swap1]
  obtain ⟨_, _, rdStored⟩ := rdStore.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnEvmSupplyMap] using (evm_run rdStored with [pop])⟩

theorem burnX_balanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hle : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1768⟩
      [solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I),
        burnValueWord I, ⟨0⟩, burnValueWord I, ⟨349⟩, sel]
      (burnBalanceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmSupplyMap σ I) k C := by
  obtain ⟨k, C, rd1705⟩ := burnX_supplyStore hsz36 hsize hszhi hperm hle hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd1754₀ := evm_run rd1705 with [
    dup2, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd1754 := rd1754₀
  rw [hsourceClean, hsourceClean] at rd1754
  obtain ⟨_, _, rd1767⟩ := RD.tokenMappingHashSuffix rd1754
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [burnBalanceHashMem, burnBalanceSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1768⟩ := rd1767.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnBalanceHashMem] using rd1768⟩

theorem burnX_balanceDebit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hsupply : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hbalance : (burnValueWord I).toNat ≤
      (solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1777⟩
      [UInt256.sub (solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I))
        (burnValueWord I), ⟨0⟩, burnValueWord I, ⟨349⟩, sel]
      (burnBalanceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmSupplyMap σ I) k C := by
  obtain ⟨_, _, rd⟩ := burnX_balanceLoad hsz36 hsize hszhi hperm hsupply hreach
  have rdSub := evm_run rd with [
    push2 ⟨1777⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubOk rdSub hbalance (by jump_dest) (by evm_ov)

theorem burnX_balanceUnderflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hsupply : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hunder : (solcSlotWord (burnEvmSupplyMap σ I) I
      (burnBalanceSlot I)).toNat < (burnValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := burnX_balanceLoad hsz36 hsize hszhi hperm hsupply hreach
  have rdSub := evm_run rd with [
    push2 ⟨1777⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubUnderflow rdSub hunder (by evm_ov)

theorem burnX_balanceStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hsupply : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hbalance : (burnValueWord I).toNat ≤
      (solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1843⟩
      [⟨0⟩, burnValueWord I, ⟨349⟩, sel]
      (burnFinalHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnEvmPostMap σ I) k C := by
  obtain ⟨_, _, rd1777⟩ := burnX_balanceDebit
    hsz36 hsize hszhi hperm hsupply hbalance hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd1826₀ := evm_run rd1777 with [
    jumpdest, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd1826 := rd1826₀
  rw [hsourceClean, hsourceClean] at rd1826
  have hmem : (burnBalanceHashMem I).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd1839⟩ := RD.tokenMappingHashSuffix rd1826
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [burnFinalHashMem, burnBalanceSlot_eq_solc I] using
      twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I) hmem)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1841 := evm_run rd1839 with [dup2, swap1]
  obtain ⟨_, _, rd1842⟩ := rd1841.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnEvmPostMap, burnFinalHashMem] using
    (evm_run rd1842 with [pop])⟩

theorem burnX_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hsupply : (burnValueWord I).toNat ≤ (solcSlotWord σ I ⟨0⟩).toNat)
    (hbalance : (burnValueWord I).toNat ≤
      (solcSlotWord (burnEvmSupplyMap σ I) I (burnBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, burnEvmPostMap σ I) (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1843⟩ := burnX_balanceStore
    hsz36 hsize hszhi hperm hsupply hbalance hreach
  have rd349 := evm_run rd1843 with [
    push1 ⟨1⟩, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hmem : (burnFinalHashMem I).size = 96 :=
    twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  have hread : (burnFinalHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold burnFinalHashMem burnBalanceHashMem
    apply twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (burnFinalHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((burnFinalHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd3065 := evm_run rd349 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨362⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd362⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := tokenWordReturnMem (burnFinalHashMem I) (⟨1⟩ : UInt256))
    rd3065 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd362 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (tokenWordReturnMem_mload64_of_size96 ⟨1⟩ hmem hread)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact tokenWordReturnMem_read128_of_size96 ⟨1⟩ hmem)
      (by evm_ov)]

set_option maxRecDepth 2000000 in
theorem tokenBurnX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨1⟩ := solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := tokenBurnX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3231⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨3230⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem tokenBurnX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨32⟩ = ⟨1⟩ := solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := tokenBurnX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨3231⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨3230⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem tokenBurnSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x42, 0x96, 0x6c, 0x68]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x42, 0x96, 0x6c, 0x68]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_burn {cd : ByteArray}
    (hsel : ((⟨#[0x42, 0x96, 0x6c, 0x68]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some burnTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x42, 0x96, 0x6c, 0x68]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition])
    (post := [burnFromTransition, mintTransition, totalSupplyTransition,
      transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, burnSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, allowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, approveSelectorBytes, hcd]; decide
  · rw [selectorOf, balanceOfSelectorBytes, hcd]; decide

theorem tokenBurnBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Ethereum.UInt256}
    (hcode : I.code = tokenBytecode)
    (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x42, 0x96, 0x6c, 0x68]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨323⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenBurnSelector_size hsel
  have hd := tokenDispatch_burn (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hdec := tokenDecode_burn_ok (I := I) hsz36 hbig
      let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hσ : EVMStateEquiv evmE evmS := by
        simpa [evmE, evmS] using
          EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
      have hsupplyE : burnSupplyWord evmE = solcSlotWord σ_evm I ⟨0⟩ := by
        rfl
      have hsupplyS : burnSupplyWord evmS = solcSlotWord σ_evm I ⟨0⟩ := by
        rw [show burnSupplyWord evmS = burnSupplyWord evmE from
          (hσ.storageLoad_codeOwner ⟨0⟩).symm, hsupplyE]
      by_cases hle : (burnValueWord I).toNat ≤ (solcSlotWord σ_evm I ⟨0⟩).toNat
      · have hleE : (burnValueWord I).toNat ≤ (burnSupplyWord evmE).toNat := by
          rwa [hsupplyE]
        have hleS : (burnValueWord I).toNat ≤ (burnSupplyWord evmS).toNat := by
          rwa [hsupplyS]
        have hdebit : burnSupplyDebitWord evmE I =
            burnSupplyDebitWord evmS I := by
          unfold burnSupplyDebitWord
          rw [hsupplyE, hsupplyS]
        have hσSupply : EVMStateEquiv
            (burnAfterSupply evmE I) (burnAfterSupply evmS I) := by
          unfold burnAfterSupply
          exact hσ.storageStore_codeOwner ⟨0⟩ hdebit
        have hmapSupply : (burnAfterSupply evmE I).accountMap =
            burnEvmSupplyMap σ_evm I := by
          unfold burnAfterSupply burnEvmSupplyMap
          rw [storageStore_accountMap,
            show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
            show evmE.accountMap = σ_evm from rfl,
            burnSupplyDebitWord_eq_sub evmE I hleE, hsupplyE]
        have hbalanceE : burnBalanceWord evmE I =
            solcSlotWord (burnEvmSupplyMap σ_evm I) I (burnBalanceSlot I) := by
          unfold burnBalanceWord
          rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
          simp only [Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, solcSlotWord, hmapSupply]
        have hbalanceS : burnBalanceWord evmS I =
            solcSlotWord (burnEvmSupplyMap σ_evm I) I (burnBalanceSlot I) := by
          rw [show burnBalanceWord evmS I = burnBalanceWord evmE I from by
              unfold burnBalanceWord
              rw [← burnAfterSupply_codeOwner evmE I,
                ← burnAfterSupply_codeOwner evmS I]
              exact (hσSupply.storageLoad_codeOwner (burnBalanceSlot I)).symm,
            hbalanceE]
        by_cases hbal : (burnValueWord I).toNat ≤
            (solcSlotWord (burnEvmSupplyMap σ_evm I) I
              (burnBalanceSlot I)).toNat
        · have hbalE : (burnValueWord I).toNat ≤
              (burnBalanceWord evmE I).toNat := by rwa [hbalanceE]
          have hbalS : (burnValueWord I).toNat ≤
              (burnBalanceWord evmS I).toNat := by rwa [hbalanceS]
          have hbalanceDebit : burnBalanceDebitWord evmE I =
              burnBalanceDebitWord evmS I := by
            unfold burnBalanceDebitWord
            rw [hbalanceE, hbalanceS]
          have hσPost : EVMStateEquiv
              (burnPostState evmE I) (burnPostState evmS I) := by
            unfold burnPostState
            rw [← burnAfterSupply_codeOwner evmE I,
              ← burnAfterSupply_codeOwner evmS I]
            exact hσSupply.storageStore_codeOwner (burnBalanceSlot I) hbalanceDebit
          have hmapPost : (burnPostState evmE I).accountMap =
              burnEvmPostMap σ_evm I := by
            unfold burnPostState burnEvmPostMap
            rw [storageStore_accountMap,
              show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
              hmapSupply, burnBalanceDebitWord_eq_sub evmE I hbalE, hbalanceE]
          have hbody := burnBodyReturns evmS I
            (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hbalS
          have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
              (some [(.bool true)]) burnTransition.returnType :=
            returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
          exact (burnX_return (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hperm hle hbal hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by simp [evmE, burnPostState, burnAfterSupply,
                initState, storageStore_createdAccounts])
              (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
        · have hunderE : (solcSlotWord (burnEvmSupplyMap σ_evm I) I
              (burnBalanceSlot I)).toNat < (burnValueWord I).toNat := by omega
          have hunderS : (burnBalanceWord evmS I).toNat <
              (burnValueWord I).toNat := by rw [hbalanceS]; exact hunderE
          have hbody := burnBodyReverts_balance evmS I
            (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hunderS
          exact (burnX_balanceUnderflow (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hperm hle hunderE hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hunderE : (solcSlotWord σ_evm I ⟨0⟩).toNat <
            (burnValueWord I).toNat := by omega
        have hunderS : (burnSupplyWord evmS).toNat <
            (burnValueWord I).toNat := by rw [hsupplyS]; exact hunderE
        have hbody := burnBodyReverts_supply evmS I
          (by simp only [evmS, initState]; exact hwv) hunderS
        exact (burnX_supplyUnderflow (g := Sat256.ofUInt256 g)
            hsz36 hsize hbig hunderE hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_burn_none_huge (I := I) hbigge
      exact (tokenBurnX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := tokenDecode_burn_none_short (I := I) hshort
    exact (tokenBurnX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
