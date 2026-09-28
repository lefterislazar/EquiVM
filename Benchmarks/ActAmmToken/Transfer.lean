import Benchmarks.ActAmmToken.Decode
import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `transfer` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev transferValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev transferToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev transferValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferValueWord I).toNat)

abbrev transferToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferToWord I).toNat)

abbrev transferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "value" (transferValueValue I)).insert
    "to" (transferToValue I)

def transferSenderSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.source)

def transferToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (transferToWord I).toNat))

theorem transferSenderSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (solcSourceWord I) = transferSenderSlot I := by
  unfold transferSenderSlot balanceOfSlot mapSlot solcMappingSlot
  rw [tokenSource_keyValueToWord I.source]

theorem transferToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (transferToWord I) = transferToSlot I := by
  unfold transferToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def transferFromWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferSenderSlot I)

def transferDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromWord evm I).toNat - (transferValueWord I).toNat)

def transferAfterDebit (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (transferSenderSlot I) (transferDebitWord evm I)

def transferToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferAfterDebit evm I) evm.executionEnv.codeOwner
    (transferToSlot I)

def transferNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferToBalanceWord evm I).toNat + (transferValueWord I).toNat

def transferNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferNewToNat evm I)

def transferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferAfterDebit evm I) evm.executionEnv.codeOwner
    (transferToSlot I) (transferNewToWord evm I)

def transferEvmDebitMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (transferSenderSlot I)
    (UInt256.sub (solcSlotWord σ I (transferSenderSlot I))
      (transferValueWord I))

noncomputable def transferSenderHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)

noncomputable def transferToHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (transferToWord I) ⟨1⟩ (transferSenderHashMem I)

noncomputable def transferFinalHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (transferToWord I) ⟨1⟩ (transferToHashMem I)

def transferEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (transferEvmDebitMap σ I)
    (transferToSlot I)
    (solcSlotWord (transferEvmDebitMap σ I) I (transferToSlot I) +
      transferValueWord I)

theorem tokenDecode_transfer_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata =
        some (transferStore I) := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferValueValue,
    transferToValue, transferValueWord, transferToWord, calldataWord]
    using tokenDecodeCalldata_uint256_address_ok
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hcanon

theorem tokenDecode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using tokenDecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "value") (y := "to") hsz4 hshort

theorem tokenDecode_transfer_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferToWord]
    using tokenDecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hnc

theorem tokenDecode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using tokenDecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "value") (y := "to") hbig

theorem transferStore_value (I : ExecutionEnv) :
    (transferStore I).get? "value" = some (transferValueValue I) := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferStore_to (I : ExecutionEnv) :
    (transferStore I).get? "to" = some (transferToValue I) := by
  rw [transferStore, store_get_self]

theorem transferStore_balanceOf (I : ExecutionEnv) :
    (transferStore I).get? "balanceOf" = none := by
  rw [transferStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

def transferSenderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

def transferToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferToWord I).toNat))] }

theorem transferEvalSenderRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := transferStore I } evm
      (balanceOfRef sender) = .ok (transferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, transferSenderRef, sender, envValue, hsrc]

theorem transferEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStore I } evm
      (balanceOfRef (.var "to")) = .ok (transferToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, transferToRef, transferToValue, transferStore_to]

theorem transferEvalSenderBalance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat (transferFromWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := transferStore_balanceOf I)
    (her := transferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      transferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferFromWord, transferSenderSlot, tokenStorageLocLoad_uint256]

theorem transferEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (transferToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := transferStore_balanceOf I)
    (her := transferEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      transferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferToSlot, tokenStorageLocLoad_uint256]

theorem transferEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.var "value") = .ok (transferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, transferStore_value]

theorem transferEvalDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (transferValueWord I).toNat ≤ (transferFromWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) =
        .ok (.int (Int.ofNat
          ((transferFromWord evm I).toNat - (transferValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok (transferEvalSenderBalance evm I hsrc)
    (transferEvalValue evm I) hle (transferFromWord evm I).val.isLt

theorem transferEvalDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (transferFromWord evm I).toNat < (transferValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) = .revert := by
  exact tokenEvalCheckedSub_revert (transferEvalSenderBalance evm I hsrc)
    (transferEvalValue evm I) hunder

theorem transferAfterDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferAfterDebit evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [transferAfterDebit, storageStore_executionEnv]

theorem transferAfterDebit_source (evm : EVM.State) (I : ExecutionEnv) :
    (transferAfterDebit evm I).executionEnv.source = evm.executionEnv.source := by
  simp [transferAfterDebit, storageStore_executionEnv]

theorem transferAssignSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := transferStore I } evm
      .storage (balanceOfRef sender)
      (.int (Int.ofNat (transferDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := transferStore I },
        transferAfterDebit evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := transferStore_balanceOf I)
    (her := transferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      transferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [transferAfterDebit, transferSenderSlot] using
    tokenStorageLocStore_uint256 evm (transferSenderSlot I)
      (transferDebitWord evm I)

theorem transferDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (_hle : (transferValueWord I).toNat ≤ (transferFromWord evm I).toNat) :
    (transferDebitWord evm I).toNat =
      (transferFromWord evm I).toNat - (transferValueWord I).toNat := by
  unfold transferDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (transferFromWord evm I).val.isLt

theorem transferDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (transferValueWord I).toNat ≤ (transferFromWord evm I).toNat) :
    transferDebitWord evm I =
      UInt256.sub (transferFromWord evm I) (transferValueWord I) := by
  apply u256_inj
  rw [transferDebitWord_toNat evm I hle, usub_toNat hle]

theorem transferEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferStore I }
      (transferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (transferNewToNat evm I))) := by
  have hload := transferEvalToBalance (transferAfterDebit evm I) I
  rw [transferAfterDebit_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_ok hload
    (transferEvalValue (transferAfterDebit evm I) I) hfit

theorem transferEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    evalExpr? config { contract := contract, locals := transferStore I }
      (transferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := transferEvalToBalance (transferAfterDebit evm I) I
  rw [transferAfterDebit_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_revert hload
    (transferEvalValue (transferAfterDebit evm I) I) hover

theorem transferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    (transferNewToWord evm I).toNat = transferNewToNat evm I := by
  unfold transferNewToWord
  exact ulit_toNat' _ hfit

theorem transferNewToWord_eq_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    transferNewToWord evm I =
      transferToBalanceWord evm I + transferValueWord I := by
  apply u256_inj
  rw [transferNewToWord_toNat evm I hfit, uadd_toNat]
  rw [show (transferToBalanceWord evm I).toNat +
    (transferValueWord I).toNat = transferNewToNat evm I from rfl,
    Nat.mod_eq_of_lt hfit]

theorem transferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferStore I }
      (transferAfterDebit evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (transferNewToNat evm I))) =
      .ok ({ contract := contract, locals := transferStore I },
        transferPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := transferStore_balanceOf I)
    (her := transferEvalToRef (transferAfterDebit evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      transferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [transferPostState, transferAfterDebit_codeOwner evm I,
    transferNewToWord_toNat evm I hfit] using
    tokenStorageLocStore_uint256 (transferAfterDebit evm I)
      (transferToSlot I) (transferNewToWord evm I)

theorem transferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (transferValueWord I).toNat ≤ (transferFromWord evm I).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body
      (.returned { contract := contract, locals := transferStore I }
        (transferPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hdebit := transferEvalDebit_ok evm I hsrc hle
  have hassign := transferAssignSender evm I hsrc
  rw [transferDebitWord_toNat evm I hle] at hassign
  refine ExecBlock.consNormal (ExecStmt.assign hdebit hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (transferEvalCredit_ok evm I hfit)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem transferBodyReverts_underflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (transferFromWord evm I).toNat < (transferValueWord I).toNat) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.assignExprRevert (transferEvalDebit_revert evm I hsrc hunder))

theorem transferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (transferValueWord I).toNat ≤ (transferFromWord evm I).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecTransitionBody config contract evm (transferStore I)
      transferTransition.body .reverted := by
  have hdebit := transferEvalDebit_ok evm I hsrc hle
  have hassign := transferAssignSender evm I hsrc
  rw [transferDebitWord_toNat evm I hle] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hdebit hassign) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (transferEvalCredit_revert evm I hover))

theorem transferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3296⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨488⟩, ⟨493⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨493⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨488⟩, swap2, swap1, push2 ⟨3296⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem transferX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3331⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨488⟩, ⟨493⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := transferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3318⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3331⟩, dup6, dup3, dup7, add, push2 ⟨2957⟩,
    jump (by jump_dest) ]⟩

theorem transferX_dec5689 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3331⟩
      [transferValueWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨488⟩, ⟨493⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := transferX_dec5521_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem transferX_dec5470_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3348⟩, ⟨32⟩,
        ⟨0⟩, transferValueWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨488⟩, ⟨493⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := transferX_dec5689 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨3348⟩,
    dup6, dup3, dup7, add, push2 ⟨2906⟩, jump (by jump_dest) ]⟩

theorem transferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2513⟩
      [transferToWord I, transferValueWord I, ⟨493⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := transferX_dec5470_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5706⟩ := RD.tokenDecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5706 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨2513⟩, jump (by jump_dest) ]⟩

theorem transferX_senderLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2578⟩
      [solcSlotWord σ I (transferSenderSlot I), transferValueWord I,
        ⟨0⟩, transferToWord I, transferValueWord I, ⟨493⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4263⟩ := transferX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd4314₀ := evm_run rd4263 with [
    jumpdest, push0, dup3, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4314 := rd4314₀
  rw [hsourceClean, hsourceClean] at rd4314
  obtain ⟨_, _, rd4327⟩ := RD.tokenMappingHashSuffix rd4314 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [transferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd4328⟩ := rd4327.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4328⟩

theorem transferX_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2587⟩
      [UInt256.sub (solcSlotWord σ I (transferSenderSlot I))
        (transferValueWord I), ⟨0⟩, transferToWord I,
        transferValueWord I, ⟨493⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4328⟩ := transferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd6645 := evm_run rd4328 with [
    push2 ⟨2587⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem transferX_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hunder : (solcSlotWord σ I (transferSenderSlot I)).toNat <
      (transferValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4328⟩ := transferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd6645 := evm_run rd4328 with [
    push2 ⟨2587⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubUnderflow rd6645 hunder (by evm_ov)

theorem transferX_senderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2653⟩
      [⟨0⟩, transferToWord I, transferValueWord I, ⟨493⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩
        (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlot I)
        (UInt256.sub (solcSlotWord σ I (transferSenderSlot I))
          (transferValueWord I))) k C := by
  obtain ⟨_, _, rd4337⟩ := transferX_debit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hle hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd4386₀ := evm_run rd4337 with [
    jumpdest, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4386 := rd4386₀
  rw [hsourceClean, hsourceClean] at rd4386
  have hmem : (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd4399⟩ := RD.tokenMappingHashSuffix rd4386 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [transferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4401 := evm_run rd4399 with [dup2, swap1]
  obtain ⟨_, _, rd4402⟩ := rd4401.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4402 with [pop]⟩

theorem transferX_toBalanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2716⟩
      [solcSlotWord (transferEvmDebitMap σ I) I (transferToSlot I),
        transferValueWord I, ⟨0⟩, transferToWord I,
        transferValueWord I, ⟨493⟩, sel]
      (transferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferEvmDebitMap σ I) k C := by
  obtain ⟨k, C, rd4403₀⟩ := transferX_senderStore (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd4403 : RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2653⟩
      [⟨0⟩, transferToWord I, transferValueWord I, ⟨493⟩, sel]
      (transferSenderHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferEvmDebitMap σ I) k C := by
    simpa [transferSenderHashMem, transferEvmDebitMap] using rd4403₀
  have htoClean : UInt256.land solcAddrMask (transferToWord I) =
      transferToWord I := solcAddrMask_clean_left hcanonTo
  have rd4452₀ := evm_run rd4403 with [
    dup3, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4452 := rd4452₀
  rw [htoClean, htoClean] at rd4452
  have hmem : (transferSenderHashMem I).size = 96 := by
    unfold transferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd4465⟩ := RD.tokenMappingHashSuffix rd4452 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [transferToHashMem, transferToSlot_eq_solc I hcanonTo]
      using (twoWordHashMem_solcMappingSlot ⟨1⟩ (transferToWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd4466⟩ := rd4465.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4466⟩

theorem transferX_credit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (transferEvmDebitMap σ I) I
      (transferToSlot I)).toNat + (transferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2725⟩
      [solcSlotWord (transferEvmDebitMap σ I) I (transferToSlot I) +
        transferValueWord I, ⟨0⟩, transferToWord I,
        transferValueWord I, ⟨493⟩, sel]
      (transferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferEvmDebitMap σ I) k C := by
  obtain ⟨_, _, rd4466⟩ := transferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd6696 := evm_run rd4466 with [
    push2 ⟨2725⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedAddOk rd6696 hfit (by jump_dest) (by evm_ov)

theorem transferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (transferEvmDebitMap σ I) I
      (transferToSlot I)).toNat + (transferValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4466⟩ := transferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd6696 := evm_run rd4466 with [
    push2 ⟨2725⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedAddOverflow rd6696 hover (by evm_ov)

theorem transferX_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (transferEvmDebitMap σ I) I
      (transferToSlot I)).toNat + (transferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2791⟩
      [⟨0⟩, transferToWord I, transferValueWord I, ⟨493⟩, sel]
      (transferFinalHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferEvmPostMap σ I) k C := by
  obtain ⟨k, C, rd4475⟩ := transferX_credit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (transferToWord I) =
      transferToWord I := solcAddrMask_clean_left hcanonTo
  have rd4524₀ := evm_run rd4475 with [
    jumpdest, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4524 := rd4524₀
  rw [htoClean, htoClean] at rd4524
  have hsenderSize : (transferSenderHashMem I).size = 96 := by
    unfold transferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have htoSize : (transferToHashMem I).size = 96 := by
    unfold transferToHashMem
    exact twoWordHashMem_size_96 _ _ hsenderSize
  obtain ⟨_, _, rd4537⟩ := RD.tokenMappingHashSuffix rd4524 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [transferFinalHashMem,
      transferToSlot_eq_solc I hcanonTo] using
        (twoWordHashMem_solcMappingSlot ⟨1⟩ (transferToWord I) htoSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4539 := evm_run rd4537 with [dup2, swap1]
  obtain ⟨_, _, rd4540⟩ := rd4539.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [transferEvmPostMap] using
    (evm_run rd4540 with [pop])⟩

theorem tokenX_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hle : (transferValueWord I).toNat ≤
      (solcSlotWord σ I (transferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (transferEvmDebitMap σ I) I
      (transferToSlot I)).toNat + (transferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, transferEvmPostMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd4541⟩ := transferX_stored (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have rd464 := evm_run rd4541 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump (by jump_dest) ]
  have hmem : (transferFinalHashMem I).size = 96 := by
    unfold transferFinalHashMem transferToHashMem transferSenderHashMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hread : (transferFinalHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold transferFinalHashMem transferToHashMem transferSenderHashMem
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (transferFinalHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((transferFinalHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd5629 := evm_run rd464 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨506⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd477⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := tokenWordReturnMem (transferFinalHashMem I) (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd477 with [
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
      (by evm_ov) ]

theorem transferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := transferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3318⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3317⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem transferX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := transferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨3318⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3317⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem transferX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferToWord I)
      (UInt256.land (transferToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := transferX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem transferSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, burnFromTransition, mintTransition,
      totalSupplyTransition])
    (post := [transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, transferSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, allowanceSelectorBytes, hcd]
    | rw [selectorOf, approveSelectorBytes, hcd]
    | rw [selectorOf, balanceOfSelectorBytes, hcd]
    | rw [selectorOf, burnSelectorBytes, hcd]
    | rw [selectorOf, burnFromSelectorBytes, hcd]
    | rw [selectorOf, mintSelectorBytes, hcd]
    | rw [selectorOf, totalSupplySelectorBytes, hcd]
  all_goals decide


theorem tokenTransferBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨467⟩ [tokenSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := transferSelector_size hsel
  have hd := tokenDispatch_transfer (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (transferToWord I).toNat < EVM.addressModulus
      · have hdec := tokenDecode_transfer_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hfromE : transferFromWord evmE I =
            solcSlotWord σ_evm I (transferSenderSlot I) := by
          simpa [transferFromWord, solcSlotWord, codeOwnerStorageWord] using
            (codeOwnerStorageWord_initState
              (g := Sat256.ofUInt256 g) (σ := σ_evm)
              (slot := transferSenderSlot I) (cA := cA) (gh := gh)
              (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
        have hfromS : transferFromWord evmS I =
            solcSlotWord σ_evm I (transferSenderSlot I) := by
          rw [show transferFromWord evmS I = transferFromWord evmE I
            from (hσ.storageLoad_codeOwner (transferSenderSlot I)).symm, hfromE]
        by_cases hle : (transferValueWord I).toNat ≤
            (solcSlotWord σ_evm I (transferSenderSlot I)).toNat
        · have hleE : (transferValueWord I).toNat ≤
              (transferFromWord evmE I).toNat := by rwa [hfromE]
          have hleS : (transferValueWord I).toNat ≤
              (transferFromWord evmS I).toNat := by rwa [hfromS]
          have hdebit : transferDebitWord evmE I =
              transferDebitWord evmS I := by
            unfold transferDebitWord
            rw [hfromE, hfromS]
          have hσDebit : EVMStateEquiv
              (transferAfterDebit evmE I) (transferAfterDebit evmS I) := by
            unfold transferAfterDebit
            exact hσ.storageStore_codeOwner (transferSenderSlot I) hdebit
          have hmapDebit : (transferAfterDebit evmE I).accountMap =
              transferEvmDebitMap σ_evm I := by
            unfold transferAfterDebit transferEvmDebitMap
            rw [storageStore_accountMap,
              show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
              show evmE.accountMap = σ_evm from rfl,
              transferDebitWord_eq_sub evmE I hleE, hfromE]
          have htoE : transferToBalanceWord evmE I =
              solcSlotWord (transferEvmDebitMap σ_evm I) I
                (transferToSlot I) := by
            unfold transferToBalanceWord
            rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
            simp only [Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, solcSlotWord, hmapDebit]
          have htoS : transferToBalanceWord evmS I =
              solcSlotWord (transferEvmDebitMap σ_evm I) I
                (transferToSlot I) := by
            rw [show transferToBalanceWord evmS I =
                transferToBalanceWord evmE I from by
                  unfold transferToBalanceWord
                  rw [← transferAfterDebit_codeOwner evmE I,
                    ← transferAfterDebit_codeOwner evmS I]
                  exact (hσDebit.storageLoad_codeOwner (transferToSlot I)).symm,
              htoE]
          have hnewE : transferNewToNat evmE I =
              (solcSlotWord (transferEvmDebitMap σ_evm I) I
                (transferToSlot I)).toNat + (transferValueWord I).toNat := by
            rw [transferNewToNat, htoE]
          have hnewS : transferNewToNat evmS I =
              (solcSlotWord (transferEvmDebitMap σ_evm I) I
                (transferToSlot I)).toNat + (transferValueWord I).toNat := by
            rw [transferNewToNat, htoS]
          by_cases hfit : (solcSlotWord (transferEvmDebitMap σ_evm I) I
              (transferToSlot I)).toNat + (transferValueWord I).toNat < UInt256.size
          · have hfitE : transferNewToNat evmE I < UInt256.size := by
              rwa [hnewE]
            have hfitS : transferNewToNat evmS I < UInt256.size := by
              rwa [hnewS]
            have hnewWord : transferNewToWord evmE I =
                transferNewToWord evmS I := by
              unfold transferNewToWord
              rw [hnewE, hnewS]
            have hσPost : EVMStateEquiv
                (transferPostState evmE I) (transferPostState evmS I) := by
              unfold transferPostState
              rw [← transferAfterDebit_codeOwner evmE I,
                ← transferAfterDebit_codeOwner evmS I]
              exact hσDebit.storageStore_codeOwner (transferToSlot I) hnewWord
            have hmapPost : (transferPostState evmE I).accountMap =
                transferEvmPostMap σ_evm I := by
              unfold transferPostState transferEvmPostMap
              rw [storageStore_accountMap,
                show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
                hmapDebit, transferNewToWord_eq_add evmE I hfitE, htoE]
            have hbody := transferBodyReturns evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hfitS
            have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
                (some [(.bool true)]) transferTransition.returnType :=
              returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
            exact (tokenX_transfer (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle hfit hreach)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [evmE, transferPostState, transferAfterDebit,
                  initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
          · have hover : UInt256.size ≤ transferNewToNat evmS I := by
              rw [hnewS]
              omega
            have hbody := transferBodyReverts_overflow evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hover
            exact (transferX_overflow (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle (by omega) hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hunderE : (solcSlotWord σ_evm I (transferSenderSlot I)).toNat <
              (transferValueWord I).toNat := by omega
          have hunderS : (transferFromWord evmS I).toNat <
              (transferValueWord I).toNat := by rw [hfromS]; exact hunderE
          have hbody := transferBodyReverts_underflow evmS I
            (by simp only [evmS, initState]; exact hwv) (by rfl) hunderS
          exact (transferX_underflow (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hunderE hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := tokenDecode_transfer_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (transferToWord I)
            (UInt256.land (transferToWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (transferX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_transfer_none_huge (I := I) hbigge
      exact (transferX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := tokenDecode_transfer_none_short (I := I) hsz4 hshort
    exact (transferX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec
end Benchmarks.ActAmmToken
