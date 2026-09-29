import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Decode
import Benchmarks.ActAmm4.Arithmetic

import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4TransferValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4TransferToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev amm4TransferValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (amm4TransferValueWord I).toNat)

abbrev amm4TransferToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4TransferToWord I).toNat)

abbrev amm4TransferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "value" (amm4TransferValueValue I)).insert
    "to" (amm4TransferToValue I)

def amm4TransferSenderSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.source)

def amm4TransferToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (amm4TransferToWord I).toNat))

theorem amm4TransferSenderSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (solcSourceWord I) = amm4TransferSenderSlot I := by
  unfold amm4TransferSenderSlot balanceOfSlot mapSlot solcMappingSlot
  rw [amm4Source_keyValueToWord I.source]

theorem amm4TransferToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4TransferToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (amm4TransferToWord I) = amm4TransferToSlot I := by
  unfold amm4TransferToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def amm4TransferFromWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (amm4TransferSenderSlot I)

def amm4TransferDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((amm4TransferFromWord evm I).toNat - (amm4TransferValueWord I).toNat)

def amm4TransferAfterDebit (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4TransferSenderSlot I) (amm4TransferDebitWord evm I)

def amm4TransferToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (amm4TransferAfterDebit evm I) evm.executionEnv.codeOwner
    (amm4TransferToSlot I)

def amm4TransferNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (amm4TransferToBalanceWord evm I).toNat + (amm4TransferValueWord I).toNat

def amm4TransferNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (amm4TransferNewToNat evm I)

def amm4TransferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (amm4TransferAfterDebit evm I) evm.executionEnv.codeOwner
    (amm4TransferToSlot I) (amm4TransferNewToWord evm I)

def amm4TransferEvmDebitMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (amm4TransferSenderSlot I)
    (UInt256.sub (solcSlotWord σ I (amm4TransferSenderSlot I))
      (amm4TransferValueWord I))

noncomputable def amm4TransferSenderHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)

noncomputable def amm4TransferToHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (amm4TransferToWord I) ⟨1⟩ (amm4TransferSenderHashMem I)

noncomputable def amm4TransferFinalHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (amm4TransferToWord I) ⟨1⟩ (amm4TransferToHashMem I)

def amm4TransferEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (amm4TransferEvmDebitMap σ I)
    (amm4TransferToSlot I)
    (solcSlotWord (amm4TransferEvmDebitMap σ I) I (amm4TransferToSlot I) +
      amm4TransferValueWord I)

theorem amm4Decode_transfer_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4TransferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata =
        some (amm4TransferStore I) := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, amm4TransferStore, amm4TransferValueValue,
    amm4TransferToValue, amm4TransferValueWord, amm4TransferToWord, calldataWord]
    using amm4DecodeCalldata_uint256_address_ok
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hcanon

theorem amm4Decode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using amm4DecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "value") (y := "to") hsz4 hshort

theorem amm4Decode_transfer_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4TransferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, amm4TransferToWord]
    using amm4DecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hnc

theorem amm4Decode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using amm4DecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "value") (y := "to") hbig

theorem amm4TransferStore_value (I : ExecutionEnv) :
    (amm4TransferStore I).get? "value" = some (amm4TransferValueValue I) := by
  rw [amm4TransferStore, store_get_ne _ _ (by decide), store_get_self]

theorem amm4TransferStore_to (I : ExecutionEnv) :
    (amm4TransferStore I).get? "to" = some (amm4TransferToValue I) := by
  rw [amm4TransferStore, store_get_self]

theorem amm4TransferStore_balanceOf (I : ExecutionEnv) :
    (amm4TransferStore I).get? "balanceOf" = none := by
  rw [amm4TransferStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

def amm4TransferSenderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

def amm4TransferToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (amm4TransferToWord I).toNat))] }

theorem amm4TransferEvalSenderRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := amm4TransferStore I } evm
      (balanceOfRef sender) = .ok (amm4TransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferSenderRef, sender, envValue, hsrc]

theorem amm4TransferEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := amm4TransferStore I } evm
      (balanceOfRef (.var "to")) = .ok (amm4TransferToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferToRef, amm4TransferToValue, amm4TransferStore_to]

theorem amm4TransferEvalSenderBalance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I } evm
      (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat (amm4TransferFromWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := amm4TransferStore_balanceOf I)
    (her := amm4TransferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [amm4TransferFromWord, amm4TransferSenderSlot, amm4StorageLocLoad_uint256]

theorem amm4TransferEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (amm4TransferToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := amm4TransferStore_balanceOf I)
    (her := amm4TransferEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [amm4TransferToSlot, amm4StorageLocLoad_uint256]

theorem amm4TransferEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I } evm
      (.var "value") = .ok (amm4TransferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4TransferStore_value]

theorem amm4TransferEvalDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (amm4TransferValueWord I).toNat ≤ (amm4TransferFromWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) =
        .ok (.int (Int.ofNat
          ((amm4TransferFromWord evm I).toNat - (amm4TransferValueWord I).toNat))) := by
  exact amm4EvalCheckedSub_ok (amm4TransferEvalSenderBalance evm I hsrc)
    (amm4TransferEvalValue evm I) hle (amm4TransferFromWord evm I).val.isLt

theorem amm4TransferEvalDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (amm4TransferFromWord evm I).toNat < (amm4TransferValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) = .revert := by
  exact amm4EvalCheckedSub_revert (amm4TransferEvalSenderBalance evm I hsrc)
    (amm4TransferEvalValue evm I) hunder

theorem amm4TransferAfterDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferAfterDebit evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [amm4TransferAfterDebit, storageStore_executionEnv]

theorem amm4TransferAfterDebit_source (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferAfterDebit evm I).executionEnv.source = evm.executionEnv.source := by
  simp [amm4TransferAfterDebit, storageStore_executionEnv]

theorem amm4TransferAssignSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := amm4TransferStore I } evm
      .storage (balanceOfRef sender)
      (.int (Int.ofNat (amm4TransferDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := amm4TransferStore I },
        amm4TransferAfterDebit evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4TransferStore_balanceOf I)
    (her := amm4TransferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [amm4TransferAfterDebit, amm4TransferSenderSlot] using
    amm4StorageLocStore_uint256 evm (amm4TransferSenderSlot I)
      (amm4TransferDebitWord evm I)

theorem amm4TransferDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (_hle : (amm4TransferValueWord I).toNat ≤ (amm4TransferFromWord evm I).toNat) :
    (amm4TransferDebitWord evm I).toNat =
      (amm4TransferFromWord evm I).toNat - (amm4TransferValueWord I).toNat := by
  unfold amm4TransferDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (amm4TransferFromWord evm I).val.isLt

theorem amm4TransferDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (amm4TransferValueWord I).toNat ≤ (amm4TransferFromWord evm I).toNat) :
    amm4TransferDebitWord evm I =
      UInt256.sub (amm4TransferFromWord evm I) (amm4TransferValueWord I) := by
  apply u256_inj
  rw [amm4TransferDebitWord_toNat evm I hle, usub_toNat hle]

theorem amm4TransferEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I }
      (amm4TransferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (amm4TransferNewToNat evm I))) := by
  have hload := amm4TransferEvalToBalance (amm4TransferAfterDebit evm I) I
  rw [amm4TransferAfterDebit_codeOwner evm I] at hload
  exact amm4EvalCheckedAdd_ok hload
    (amm4TransferEvalValue (amm4TransferAfterDebit evm I) I) hfit

theorem amm4TransferEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ amm4TransferNewToNat evm I) :
    evalExpr? config { contract := contract, locals := amm4TransferStore I }
      (amm4TransferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := amm4TransferEvalToBalance (amm4TransferAfterDebit evm I) I
  rw [amm4TransferAfterDebit_codeOwner evm I] at hload
  exact amm4EvalCheckedAdd_revert hload
    (amm4TransferEvalValue (amm4TransferAfterDebit evm I) I) hover

theorem amm4TransferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferNewToNat evm I < UInt256.size) :
    (amm4TransferNewToWord evm I).toNat = amm4TransferNewToNat evm I := by
  unfold amm4TransferNewToWord
  exact ulit_toNat' _ hfit

theorem amm4TransferNewToWord_eq_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferNewToNat evm I < UInt256.size) :
    amm4TransferNewToWord evm I =
      amm4TransferToBalanceWord evm I + amm4TransferValueWord I := by
  apply u256_inj
  rw [amm4TransferNewToWord_toNat evm I hfit, uadd_toNat]
  rw [show (amm4TransferToBalanceWord evm I).toNat +
    (amm4TransferValueWord I).toNat = amm4TransferNewToNat evm I from rfl,
    Nat.mod_eq_of_lt hfit]

theorem amm4TransferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := amm4TransferStore I }
      (amm4TransferAfterDebit evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (amm4TransferNewToNat evm I))) =
      .ok ({ contract := contract, locals := amm4TransferStore I },
        amm4TransferPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4TransferStore_balanceOf I)
    (her := amm4TransferEvalToRef (amm4TransferAfterDebit evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [amm4TransferPostState, amm4TransferAfterDebit_codeOwner evm I,
    amm4TransferNewToWord_toNat evm I hfit] using
    amm4StorageLocStore_uint256 (amm4TransferAfterDebit evm I)
      (amm4TransferToSlot I) (amm4TransferNewToWord evm I)

theorem amm4TransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (amm4TransferValueWord I).toNat ≤ (amm4TransferFromWord evm I).toNat)
    (hfit : amm4TransferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (amm4TransferStore I)
      transferTransition.body
      (.returned { contract := contract, locals := amm4TransferStore I }
        (amm4TransferPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hdebit := amm4TransferEvalDebit_ok evm I hsrc hle
  have hassign := amm4TransferAssignSender evm I hsrc
  rw [amm4TransferDebitWord_toNat evm I hle] at hassign
  refine ExecBlock.consNormal (ExecStmt.assign hdebit hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (amm4TransferEvalCredit_ok evm I hfit)
      (amm4TransferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem amm4TransferBodyReverts_underflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (amm4TransferFromWord evm I).toNat < (amm4TransferValueWord I).toNat) :
    ExecTransitionBody config contract evm (amm4TransferStore I)
      transferTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.assignExprRevert (amm4TransferEvalDebit_revert evm I hsrc hunder))

theorem amm4TransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (amm4TransferValueWord I).toNat ≤ (amm4TransferFromWord evm I).toNat)
    (hover : UInt256.size ≤ amm4TransferNewToNat evm I) :
    ExecTransitionBody config contract evm (amm4TransferStore I)
      transferTransition.body .reverted := by
  have hdebit := amm4TransferEvalDebit_ok evm I hsrc hle
  have hassign := amm4TransferAssignSender evm I hsrc
  rw [amm4TransferDebitWord_toNat evm I hle] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hdebit hassign) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (amm4TransferEvalCredit_revert evm I hover))

theorem amm4TransferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5084⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨420⟩, ⟨425⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨425⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨420⟩, swap2, swap1, push2 ⟨5084⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4TransferX_dec4708_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5119⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨420⟩, ⟨425⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5119⟩, dup6, dup3, dup7, add, push2 ⟨4708⟩,
    jump (by jump_dest) ]⟩

theorem amm4TransferX_dec5119 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5119⟩
      [amm4TransferValueWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨420⟩, ⟨425⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferX_dec4708_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.amm4DecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem amm4TransferX_dec4657_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5136⟩, ⟨32⟩,
        ⟨0⟩, amm4TransferValueWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨420⟩, ⟨425⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferX_dec5119 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5136⟩,
    dup6, dup3, dup7, add, push2 ⟨4657⟩, jump (by jump_dest) ]⟩

theorem amm4TransferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3450⟩
      [amm4TransferToWord I, amm4TransferValueWord I, ⟨425⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferX_dec4657_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5136⟩ := RD.amm4DecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5136 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨3450⟩, jump (by jump_dest) ]⟩

theorem amm4TransferX_senderLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3515⟩
      [solcSlotWord σ I (amm4TransferSenderSlot I), amm4TransferValueWord I,
        ⟨0⟩, amm4TransferToWord I, amm4TransferValueWord I, ⟨425⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3450⟩ := amm4TransferX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd3501₀ := evm_run rd3450 with [
    jumpdest, push0, dup3, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd3501 := rd3501₀
  rw [hsourceClean, hsourceClean] at rd3501
  obtain ⟨_, _, rd3514⟩ := RD.amm4MappingHashSuffix rd3501 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3515⟩ := rd3514.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3515⟩

theorem amm4TransferX_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3524⟩
      [UInt256.sub (solcSlotWord σ I (amm4TransferSenderSlot I))
        (amm4TransferValueWord I), ⟨0⟩, amm4TransferToWord I,
        amm4TransferValueWord I, ⟨425⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3515⟩ := amm4TransferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd5253 := evm_run rd3515 with [
    push2 ⟨3524⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubOk rd5253 hle (by jump_dest) (by evm_ov)

theorem amm4TransferX_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hunder : (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat <
      (amm4TransferValueWord I).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3515⟩ := amm4TransferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd5253 := evm_run rd3515 with [
    push2 ⟨3524⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubUnderflow rd5253 hunder (by evm_ov)

theorem amm4TransferX_senderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3590⟩
      [⟨0⟩, amm4TransferToWord I, amm4TransferValueWord I, ⟨425⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩
        (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (amm4TransferSenderSlot I)
        (UInt256.sub (solcSlotWord σ I (amm4TransferSenderSlot I))
          (amm4TransferValueWord I))) k C := by
  obtain ⟨_, _, rd3524⟩ := amm4TransferX_debit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hle hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd3573₀ := evm_run rd3524 with [
    jumpdest, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd3573 := rd3573₀
  rw [hsourceClean, hsourceClean] at rd3573
  have hmem : (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd3586⟩ := RD.amm4MappingHashSuffix rd3573 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3588 := evm_run rd3586 with [dup2, swap1]
  obtain ⟨_, _, rd3589⟩ := rd3588.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3589 with [pop]⟩

theorem amm4TransferX_toBalanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
      [solcSlotWord (amm4TransferEvmDebitMap σ I) I (amm4TransferToSlot I),
        amm4TransferValueWord I, ⟨0⟩, amm4TransferToWord I,
        amm4TransferValueWord I, ⟨425⟩, sel]
      (amm4TransferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferEvmDebitMap σ I) k C := by
  obtain ⟨k, C, rd3590₀⟩ := amm4TransferX_senderStore (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd3590 : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3590⟩
      [⟨0⟩, amm4TransferToWord I, amm4TransferValueWord I, ⟨425⟩, sel]
      (amm4TransferSenderHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferEvmDebitMap σ I) k C := by
    simpa [amm4TransferSenderHashMem, amm4TransferEvmDebitMap] using rd3590₀
  have htoClean : UInt256.land solcAddrMask (amm4TransferToWord I) =
      amm4TransferToWord I := solcAddrMask_clean_left hcanonTo
  have rd3639₀ := evm_run rd3590 with [
    dup3, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd3639 := rd3639₀
  rw [htoClean, htoClean] at rd3639
  have hmem : (amm4TransferSenderHashMem I).size = 96 := by
    unfold amm4TransferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd3652⟩ := RD.amm4MappingHashSuffix rd3639 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferToHashMem, amm4TransferToSlot_eq_solc I hcanonTo]
      using (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferToWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd3653⟩ := rd3652.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3653⟩

theorem amm4TransferX_credit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferEvmDebitMap σ I) I
      (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3662⟩
      [solcSlotWord (amm4TransferEvmDebitMap σ I) I (amm4TransferToSlot I) +
        amm4TransferValueWord I, ⟨0⟩, amm4TransferToWord I,
        amm4TransferValueWord I, ⟨425⟩, sel]
      (amm4TransferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferEvmDebitMap σ I) k C := by
  obtain ⟨_, _, rd3653⟩ := amm4TransferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd5304 := evm_run rd3653 with [
    push2 ⟨3662⟩, swap2, swap1, push2 ⟨5304⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedAddOk rd5304 hfit (by jump_dest) (by evm_ov)

theorem amm4TransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (amm4TransferEvmDebitMap σ I) I
      (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3653⟩ := amm4TransferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd5304 := evm_run rd3653 with [
    push2 ⟨3662⟩, swap2, swap1, push2 ⟨5304⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedAddOverflow rd5304 hover (by evm_ov)

theorem amm4TransferX_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferEvmDebitMap σ I) I
      (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3728⟩
      [⟨0⟩, amm4TransferToWord I, amm4TransferValueWord I, ⟨425⟩, sel]
      (amm4TransferFinalHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferEvmPostMap σ I) k C := by
  obtain ⟨k, C, rd3662⟩ := amm4TransferX_credit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (amm4TransferToWord I) =
      amm4TransferToWord I := solcAddrMask_clean_left hcanonTo
  have rd3711₀ := evm_run rd3662 with [
    jumpdest, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd3711 := rd3711₀
  rw [htoClean, htoClean] at rd3711
  have hsenderSize : (amm4TransferSenderHashMem I).size = 96 := by
    unfold amm4TransferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have htoSize : (amm4TransferToHashMem I).size = 96 := by
    unfold amm4TransferToHashMem
    exact twoWordHashMem_size_96 _ _ hsenderSize
  obtain ⟨_, _, rd3724⟩ := RD.amm4MappingHashSuffix rd3711 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFinalHashMem,
      amm4TransferToSlot_eq_solc I hcanonTo] using
        (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferToWord I) htoSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3726 := evm_run rd3724 with [dup2, swap1]
  obtain ⟨_, _, rd3727⟩ := rd3726.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [amm4TransferEvmPostMap] using
    (evm_run rd3727 with [pop])⟩

theorem amm4X_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (amm4TransferToWord I).toNat < EVM.addressModulus)
    (hle : (amm4TransferValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferEvmDebitMap σ I) I
      (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, amm4TransferEvmPostMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd3728⟩ := amm4TransferX_stored (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have rd425 := evm_run rd3728 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump (by jump_dest) ]
  have hmem : (amm4TransferFinalHashMem I).size = 96 := by
    unfold amm4TransferFinalHashMem amm4TransferToHashMem amm4TransferSenderHashMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hread : (amm4TransferFinalHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold amm4TransferFinalHashMem amm4TransferToHashMem amm4TransferSenderHashMem
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4TransferFinalHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4TransferFinalHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd4816 := evm_run rd425 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨438⟩, swap2, swap1, push2 ⟨4816⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd438⟩ := RD.amm4RoutineEncodeBoolFromMem
    (memout := amm4WordReturnMem (amm4TransferFinalHashMem I) (⟨1⟩ : UInt256))
    rd4816 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd438 with [
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

theorem amm4TransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5105⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4TransferX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5105⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4TransferX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (amm4TransferToWord I)
      (UInt256.land (amm4TransferToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨399⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4TransferX_dec4657_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4TransferSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swapTransition,
      totalSupplyTransition])
    (post := [transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4TransferSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
    | rw [selectorOf, amm4ApproveSelectorBytes, hcd]
    | rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]
    | rw [selectorOf, amm4BurnSelectorBytes, hcd]
    | rw [selectorOf, amm4MintSelectorBytes, hcd]
    | rw [selectorOf, amm4SwapSelectorBytes, hcd]
    | rw [selectorOf, amm4TotalSupplySelectorBytes, hcd]
  all_goals decide

/-- The transfer wrapper, entered at PC 399, refines its Solm transition. -/
theorem amm4TransferBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨399⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4TransferSelector_size hsel
  have hd := amm4Dispatch_transfer (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (amm4TransferToWord I).toNat < EVM.addressModulus
      · have hdec := amm4Decode_transfer_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hfromE : amm4TransferFromWord evmE I =
            solcSlotWord σ_evm I (amm4TransferSenderSlot I) := by
          simpa [amm4TransferFromWord, solcSlotWord, codeOwnerStorageWord] using
            (codeOwnerStorageWord_initState
              (g := Sat256.ofUInt256 g) (σ := σ_evm)
              (slot := amm4TransferSenderSlot I) (cA := cA) (gh := gh)
              (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
        have hfromS : amm4TransferFromWord evmS I =
            solcSlotWord σ_evm I (amm4TransferSenderSlot I) := by
          rw [show amm4TransferFromWord evmS I = amm4TransferFromWord evmE I
            from (hσ.storageLoad_codeOwner (amm4TransferSenderSlot I)).symm, hfromE]
        by_cases hle : (amm4TransferValueWord I).toNat ≤
            (solcSlotWord σ_evm I (amm4TransferSenderSlot I)).toNat
        · have hleE : (amm4TransferValueWord I).toNat ≤
              (amm4TransferFromWord evmE I).toNat := by rwa [hfromE]
          have hleS : (amm4TransferValueWord I).toNat ≤
              (amm4TransferFromWord evmS I).toNat := by rwa [hfromS]
          have hdebit : amm4TransferDebitWord evmE I =
              amm4TransferDebitWord evmS I := by
            unfold amm4TransferDebitWord
            rw [hfromE, hfromS]
          have hσDebit : EVMStateEquiv
              (amm4TransferAfterDebit evmE I) (amm4TransferAfterDebit evmS I) := by
            unfold amm4TransferAfterDebit
            exact hσ.storageStore_codeOwner (amm4TransferSenderSlot I) hdebit
          have hmapDebit : (amm4TransferAfterDebit evmE I).accountMap =
              amm4TransferEvmDebitMap σ_evm I := by
            unfold amm4TransferAfterDebit amm4TransferEvmDebitMap
            rw [storageStore_accountMap,
              show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
              show evmE.accountMap = σ_evm from rfl,
              amm4TransferDebitWord_eq_sub evmE I hleE, hfromE]
          have htoE : amm4TransferToBalanceWord evmE I =
              solcSlotWord (amm4TransferEvmDebitMap σ_evm I) I
                (amm4TransferToSlot I) := by
            unfold amm4TransferToBalanceWord
            rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
            simp only [Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, solcSlotWord, hmapDebit]
          have htoS : amm4TransferToBalanceWord evmS I =
              solcSlotWord (amm4TransferEvmDebitMap σ_evm I) I
                (amm4TransferToSlot I) := by
            rw [show amm4TransferToBalanceWord evmS I =
                amm4TransferToBalanceWord evmE I from by
                  unfold amm4TransferToBalanceWord
                  rw [← amm4TransferAfterDebit_codeOwner evmE I,
                    ← amm4TransferAfterDebit_codeOwner evmS I]
                  exact (hσDebit.storageLoad_codeOwner (amm4TransferToSlot I)).symm,
              htoE]
          have hnewE : amm4TransferNewToNat evmE I =
              (solcSlotWord (amm4TransferEvmDebitMap σ_evm I) I
                (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat := by
            rw [amm4TransferNewToNat, htoE]
          have hnewS : amm4TransferNewToNat evmS I =
              (solcSlotWord (amm4TransferEvmDebitMap σ_evm I) I
                (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat := by
            rw [amm4TransferNewToNat, htoS]
          by_cases hfit : (solcSlotWord (amm4TransferEvmDebitMap σ_evm I) I
              (amm4TransferToSlot I)).toNat + (amm4TransferValueWord I).toNat < UInt256.size
          · have hfitE : amm4TransferNewToNat evmE I < UInt256.size := by
              rwa [hnewE]
            have hfitS : amm4TransferNewToNat evmS I < UInt256.size := by
              rwa [hnewS]
            have hnewWord : amm4TransferNewToWord evmE I =
                amm4TransferNewToWord evmS I := by
              unfold amm4TransferNewToWord
              rw [hnewE, hnewS]
            have hσPost : EVMStateEquiv
                (amm4TransferPostState evmE I) (amm4TransferPostState evmS I) := by
              unfold amm4TransferPostState
              rw [← amm4TransferAfterDebit_codeOwner evmE I,
                ← amm4TransferAfterDebit_codeOwner evmS I]
              exact hσDebit.storageStore_codeOwner (amm4TransferToSlot I) hnewWord
            have hmapPost : (amm4TransferPostState evmE I).accountMap =
                amm4TransferEvmPostMap σ_evm I := by
              unfold amm4TransferPostState amm4TransferEvmPostMap
              rw [storageStore_accountMap,
                show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
                hmapDebit, amm4TransferNewToWord_eq_add evmE I hfitE, htoE]
            have hbody := amm4TransferBodyReturns evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hfitS
            have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
                (some [(.bool true)]) transferTransition.returnType :=
              returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
            exact (amm4X_transfer (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle hfit hreach)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [evmE, amm4TransferPostState, amm4TransferAfterDebit,
                  initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
          · have hover : UInt256.size ≤ amm4TransferNewToNat evmS I := by
              rw [hnewS]
              omega
            have hbody := amm4TransferBodyReverts_overflow evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hover
            exact (amm4TransferX_overflow (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle (by omega) hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hunderE : (solcSlotWord σ_evm I (amm4TransferSenderSlot I)).toNat <
              (amm4TransferValueWord I).toNat := by omega
          have hunderS : (amm4TransferFromWord evmS I).toNat <
              (amm4TransferValueWord I).toNat := by rw [hfromS]; exact hunderE
          have hbody := amm4TransferBodyReverts_underflow evmS I
            (by simp only [evmS, initState]; exact hwv) (by rfl) hunderS
          exact (amm4TransferX_underflow (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hunderE hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := amm4Decode_transfer_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (amm4TransferToWord I)
            (UInt256.land (amm4TransferToWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (amm4TransferX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := amm4Decode_transfer_none_huge (I := I) hbigge
      exact (amm4TransferX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := amm4Decode_transfer_none_short (I := I) hsz4 hshort
    exact (amm4TransferX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm4
