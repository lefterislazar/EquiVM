import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Decode
import Benchmarks.ActAmm.Arithmetic
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammTransferValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammTransferToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev ammTransferValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (ammTransferValueWord I).toNat)

abbrev ammTransferToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammTransferToWord I).toNat)

abbrev ammTransferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "value" (ammTransferValueValue I)).insert
    "to" (ammTransferToValue I)

def ammTransferSenderSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.source)

def ammTransferToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (ammTransferToWord I).toNat))

theorem ammTransferSenderSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (solcSourceWord I) = ammTransferSenderSlot I := by
  unfold ammTransferSenderSlot balanceOfSlot mapSlot solcMappingSlot
  rw [ammSource_keyValueToWord I.source]

theorem ammTransferToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammTransferToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (ammTransferToWord I) = ammTransferToSlot I := by
  unfold ammTransferToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def ammTransferFromWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ammTransferSenderSlot I)

def ammTransferDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((ammTransferFromWord evm I).toNat - (ammTransferValueWord I).toNat)

def ammTransferAfterDebit (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammTransferSenderSlot I) (ammTransferDebitWord evm I)

def ammTransferToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (ammTransferAfterDebit evm I) evm.executionEnv.codeOwner
    (ammTransferToSlot I)

def ammTransferNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (ammTransferToBalanceWord evm I).toNat + (ammTransferValueWord I).toNat

def ammTransferNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (ammTransferNewToNat evm I)

def ammTransferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (ammTransferAfterDebit evm I) evm.executionEnv.codeOwner
    (ammTransferToSlot I) (ammTransferNewToWord evm I)

def ammTransferEvmDebitMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (ammTransferSenderSlot I)
    (UInt256.sub (solcSlotWord σ I (ammTransferSenderSlot I))
      (ammTransferValueWord I))

noncomputable def ammTransferSenderHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨1⟩
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)

noncomputable def ammTransferToHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (ammTransferToWord I) ⟨1⟩ (ammTransferSenderHashMem I)

noncomputable def ammTransferFinalHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (ammTransferToWord I) ⟨1⟩ (ammTransferToHashMem I)

def ammTransferEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (ammTransferEvmDebitMap σ I)
    (ammTransferToSlot I)
    (solcSlotWord (ammTransferEvmDebitMap σ I) I (ammTransferToSlot I) +
      ammTransferValueWord I)

theorem ammDecode_transfer_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammTransferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata =
        some (ammTransferStore I) := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = _
  simpa [addr, uint256, abiUInt256, ammTransferStore, ammTransferValueValue,
    ammTransferToValue, ammTransferValueWord, ammTransferToWord, calldataWord]
    using ammDecodeCalldata_uint256_address_ok
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hcanon

theorem ammDecode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using ammDecodeCalldata_uint256_address_none_short
      (cd := I.calldata) (x := "value") (y := "to") hsz4 hshort

theorem ammDecode_transfer_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammTransferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, ammTransferToWord]
    using ammDecodeCalldata_uint256_address_none_noncanon
      (cd := I.calldata) (x := "value") (y := "to") hsz68 hbig hnc

theorem ammDecode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "to"] [uint256, addr] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using ammDecodeCalldata_uint256_address_none_huge
      (cd := I.calldata) (x := "value") (y := "to") hbig

theorem ammTransferStore_value (I : ExecutionEnv) :
    (ammTransferStore I).get? "value" = some (ammTransferValueValue I) := by
  rw [ammTransferStore, store_get_ne _ _ (by decide), store_get_self]

theorem ammTransferStore_to (I : ExecutionEnv) :
    (ammTransferStore I).get? "to" = some (ammTransferToValue I) := by
  rw [ammTransferStore, store_get_self]

theorem ammTransferStore_balanceOf (I : ExecutionEnv) :
    (ammTransferStore I).get? "balanceOf" = none := by
  rw [ammTransferStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

def ammTransferSenderRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.source)] }

def ammTransferToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (ammTransferToWord I).toNat))] }

theorem ammTransferEvalSenderRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := ammTransferStore I } evm
      (balanceOfRef sender) = .ok (ammTransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferSenderRef, sender, envValue, hsrc]

theorem ammTransferEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := ammTransferStore I } evm
      (balanceOfRef (.var "to")) = .ok (ammTransferToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferToRef, ammTransferToValue, ammTransferStore_to]

theorem ammTransferEvalSenderBalance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferStore I } evm
      (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat (ammTransferFromWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := ammTransferStore_balanceOf I)
    (her := ammTransferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [ammTransferFromWord, ammTransferSenderSlot, ammStorageLocLoad_uint256]

theorem ammTransferEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ammTransferStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (ammTransferToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := ammTransferStore_balanceOf I)
    (her := ammTransferEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [ammTransferToSlot, ammStorageLocLoad_uint256]

theorem ammTransferEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ammTransferStore I } evm
      (.var "value") = .ok (ammTransferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, ammTransferStore_value]

theorem ammTransferEvalDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (ammTransferValueWord I).toNat ≤ (ammTransferFromWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) =
        .ok (.int (Int.ofNat
          ((ammTransferFromWord evm I).toNat - (ammTransferValueWord I).toNat))) := by
  exact ammEvalCheckedSub_ok (ammTransferEvalSenderBalance evm I hsrc)
    (ammTransferEvalValue evm I) hle (ammTransferFromWord evm I).val.isLt

theorem ammTransferEvalDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (ammTransferFromWord evm I).toNat < (ammTransferValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferStore I } evm
      (checkedSub (.storage (balanceOfRef sender)) (.var "value")) = .revert := by
  exact ammEvalCheckedSub_revert (ammTransferEvalSenderBalance evm I hsrc)
    (ammTransferEvalValue evm I) hunder

theorem ammTransferAfterDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferAfterDebit evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [ammTransferAfterDebit, storageStore_executionEnv]

theorem ammTransferAfterDebit_source (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferAfterDebit evm I).executionEnv.source = evm.executionEnv.source := by
  simp [ammTransferAfterDebit, storageStore_executionEnv]

theorem ammTransferAssignSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := ammTransferStore I } evm
      .storage (balanceOfRef sender)
      (.int (Int.ofNat (ammTransferDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := ammTransferStore I },
        ammTransferAfterDebit evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammTransferStore_balanceOf I)
    (her := ammTransferEvalSenderRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [ammTransferAfterDebit, ammTransferSenderSlot] using
    ammStorageLocStore_uint256 evm (ammTransferSenderSlot I)
      (ammTransferDebitWord evm I)

theorem ammTransferDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (_hle : (ammTransferValueWord I).toNat ≤ (ammTransferFromWord evm I).toNat) :
    (ammTransferDebitWord evm I).toNat =
      (ammTransferFromWord evm I).toNat - (ammTransferValueWord I).toNat := by
  unfold ammTransferDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (ammTransferFromWord evm I).val.isLt

theorem ammTransferDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (ammTransferValueWord I).toNat ≤ (ammTransferFromWord evm I).toNat) :
    ammTransferDebitWord evm I =
      UInt256.sub (ammTransferFromWord evm I) (ammTransferValueWord I) := by
  apply u256_inj
  rw [ammTransferDebitWord_toNat evm I hle, usub_toNat hle]

theorem ammTransferEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := ammTransferStore I }
      (ammTransferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (ammTransferNewToNat evm I))) := by
  have hload := ammTransferEvalToBalance (ammTransferAfterDebit evm I) I
  rw [ammTransferAfterDebit_codeOwner evm I] at hload
  exact ammEvalCheckedAdd_ok hload
    (ammTransferEvalValue (ammTransferAfterDebit evm I) I) hfit

theorem ammTransferEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ ammTransferNewToNat evm I) :
    evalExpr? config { contract := contract, locals := ammTransferStore I }
      (ammTransferAfterDebit evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := ammTransferEvalToBalance (ammTransferAfterDebit evm I) I
  rw [ammTransferAfterDebit_codeOwner evm I] at hload
  exact ammEvalCheckedAdd_revert hload
    (ammTransferEvalValue (ammTransferAfterDebit evm I) I) hover

theorem ammTransferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferNewToNat evm I < UInt256.size) :
    (ammTransferNewToWord evm I).toNat = ammTransferNewToNat evm I := by
  unfold ammTransferNewToWord
  exact ulit_toNat' _ hfit

theorem ammTransferNewToWord_eq_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferNewToNat evm I < UInt256.size) :
    ammTransferNewToWord evm I =
      ammTransferToBalanceWord evm I + ammTransferValueWord I := by
  apply u256_inj
  rw [ammTransferNewToWord_toNat evm I hfit, uadd_toNat]
  rw [show (ammTransferToBalanceWord evm I).toNat +
    (ammTransferValueWord I).toNat = ammTransferNewToNat evm I from rfl,
    Nat.mod_eq_of_lt hfit]

theorem ammTransferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := ammTransferStore I }
      (ammTransferAfterDebit evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (ammTransferNewToNat evm I))) =
      .ok ({ contract := contract, locals := ammTransferStore I },
        ammTransferPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammTransferStore_balanceOf I)
    (her := ammTransferEvalToRef (ammTransferAfterDebit evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [ammTransferPostState, ammTransferAfterDebit_codeOwner evm I,
    ammTransferNewToWord_toNat evm I hfit] using
    ammStorageLocStore_uint256 (ammTransferAfterDebit evm I)
      (ammTransferToSlot I) (ammTransferNewToWord evm I)

theorem ammTransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (ammTransferValueWord I).toNat ≤ (ammTransferFromWord evm I).toNat)
    (hfit : ammTransferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (ammTransferStore I)
      transferTransition.body
      (.returned { contract := contract, locals := ammTransferStore I }
        (ammTransferPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hdebit := ammTransferEvalDebit_ok evm I hsrc hle
  have hassign := ammTransferAssignSender evm I hsrc
  rw [ammTransferDebitWord_toNat evm I hle] at hassign
  refine ExecBlock.consNormal (ExecStmt.assign hdebit hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (ammTransferEvalCredit_ok evm I hfit)
      (ammTransferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem ammTransferBodyReverts_underflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (ammTransferFromWord evm I).toNat < (ammTransferValueWord I).toNat) :
    ExecTransitionBody config contract evm (ammTransferStore I)
      transferTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.assignExprRevert (ammTransferEvalDebit_revert evm I hsrc hunder))

theorem ammTransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (ammTransferValueWord I).toNat ≤ (ammTransferFromWord evm I).toNat)
    (hover : UInt256.size ≤ ammTransferNewToNat evm I) :
    ExecTransitionBody config contract evm (ammTransferStore I)
      transferTransition.body .reverted := by
  have hdebit := ammTransferEvalDebit_ok evm I hsrc hle
  have hassign := ammTransferAssignSender evm I hsrc
  rw [ammTransferDebitWord_toNat evm I hle] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hdebit hassign) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (ammTransferEvalCredit_revert evm I hover))

theorem ammTransferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5654⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨459⟩, ⟨464⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨464⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨459⟩, swap2, swap1, push2 ⟨5654⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammTransferX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5521⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5689⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨459⟩, ⟨464⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammTransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5689⟩, dup6, dup3, dup7, add, push2 ⟨5521⟩,
    jump (by jump_dest) ]⟩

theorem ammTransferX_dec5689 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5689⟩
      [ammTransferValueWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨459⟩, ⟨464⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferX_dec5521_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem ammTransferX_dec5470_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5706⟩, ⟨32⟩,
        ⟨0⟩, ammTransferValueWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨459⟩, ⟨464⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferX_dec5689 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5706⟩,
    dup6, dup3, dup7, add, push2 ⟨5470⟩, jump (by jump_dest) ]⟩

theorem ammTransferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4263⟩
      [ammTransferToWord I, ammTransferValueWord I, ⟨464⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferX_dec5470_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5706⟩ := RD.ammDecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5706 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨4263⟩, jump (by jump_dest) ]⟩

theorem ammTransferX_senderLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4328⟩
      [solcSlotWord σ I (ammTransferSenderSlot I), ammTransferValueWord I,
        ⟨0⟩, ammTransferToWord I, ammTransferValueWord I, ⟨464⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4263⟩ := ammTransferX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd4314₀ := evm_run rd4263 with [
    jumpdest, push0, dup3, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4314 := rd4314₀
  rw [hsourceClean, hsourceClean] at rd4314
  obtain ⟨_, _, rd4327⟩ := RD.ammMappingHashSuffix rd4314 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd4328⟩ := rd4327.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4328⟩

theorem ammTransferX_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4337⟩
      [UInt256.sub (solcSlotWord σ I (ammTransferSenderSlot I))
        (ammTransferValueWord I), ⟨0⟩, ammTransferToWord I,
        ammTransferValueWord I, ⟨464⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4328⟩ := ammTransferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd6645 := evm_run rd4328 with [
    push2 ⟨4337⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem ammTransferX_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hunder : (solcSlotWord σ I (ammTransferSenderSlot I)).toNat <
      (ammTransferValueWord I).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4328⟩ := ammTransferX_senderLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd6645 := evm_run rd4328 with [
    push2 ⟨4337⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubUnderflow rd6645 hunder (by evm_ov)

theorem ammTransferX_senderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4403⟩
      [⟨0⟩, ammTransferToWord I, ammTransferValueWord I, ⟨464⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩
        (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (ammTransferSenderSlot I)
        (UInt256.sub (solcSlotWord σ I (ammTransferSenderSlot I))
          (ammTransferValueWord I))) k C := by
  obtain ⟨_, _, rd4337⟩ := ammTransferX_debit (cA := cA) (gh := gh)
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
  obtain ⟨_, _, rd4399⟩ := RD.ammMappingHashSuffix rd4386 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4401 := evm_run rd4399 with [dup2, swap1]
  obtain ⟨_, _, rd4402⟩ := rd4401.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4402 with [pop]⟩

theorem ammTransferX_toBalanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4466⟩
      [solcSlotWord (ammTransferEvmDebitMap σ I) I (ammTransferToSlot I),
        ammTransferValueWord I, ⟨0⟩, ammTransferToWord I,
        ammTransferValueWord I, ⟨464⟩, sel]
      (ammTransferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferEvmDebitMap σ I) k C := by
  obtain ⟨k, C, rd4403₀⟩ := ammTransferX_senderStore (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd4403 : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4403⟩
      [⟨0⟩, ammTransferToWord I, ammTransferValueWord I, ⟨464⟩, sel]
      (ammTransferSenderHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferEvmDebitMap σ I) k C := by
    simpa [ammTransferSenderHashMem, ammTransferEvmDebitMap] using rd4403₀
  have htoClean : UInt256.land solcAddrMask (ammTransferToWord I) =
      ammTransferToWord I := solcAddrMask_clean_left hcanonTo
  have rd4452₀ := evm_run rd4403 with [
    dup3, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4452 := rd4452₀
  rw [htoClean, htoClean] at rd4452
  have hmem : (ammTransferSenderHashMem I).size = 96 := by
    unfold ammTransferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd4465⟩ := RD.ammMappingHashSuffix rd4452 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferToHashMem, ammTransferToSlot_eq_solc I hcanonTo]
      using (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferToWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd4466⟩ := rd4465.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4466⟩

theorem ammTransferX_credit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferEvmDebitMap σ I) I
      (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4475⟩
      [solcSlotWord (ammTransferEvmDebitMap σ I) I (ammTransferToSlot I) +
        ammTransferValueWord I, ⟨0⟩, ammTransferToWord I,
        ammTransferValueWord I, ⟨464⟩, sel]
      (ammTransferToHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferEvmDebitMap σ I) k C := by
  obtain ⟨_, _, rd4466⟩ := ammTransferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd6696 := evm_run rd4466 with [
    push2 ⟨4475⟩, swap2, swap1, push2 ⟨6696⟩, jump (by jump_dest) ]
  exact RD.ammCheckedAddOk rd6696 hfit (by jump_dest) (by evm_ov)

theorem ammTransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (ammTransferEvmDebitMap σ I) I
      (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4466⟩ := ammTransferX_toBalanceLoad (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hreach
  have rd6696 := evm_run rd4466 with [
    push2 ⟨4475⟩, swap2, swap1, push2 ⟨6696⟩, jump (by jump_dest) ]
  exact RD.ammCheckedAddOverflow rd6696 hover (by evm_ov)

theorem ammTransferX_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferEvmDebitMap σ I) I
      (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4541⟩
      [⟨0⟩, ammTransferToWord I, ammTransferValueWord I, ⟨464⟩, sel]
      (ammTransferFinalHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferEvmPostMap σ I) k C := by
  obtain ⟨k, C, rd4475⟩ := ammTransferX_credit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (ammTransferToWord I) =
      ammTransferToWord I := solcAddrMask_clean_left hcanonTo
  have rd4524₀ := evm_run rd4475 with [
    jumpdest, push1 ⟨1⟩, push0, dup5,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd4524 := rd4524₀
  rw [htoClean, htoClean] at rd4524
  have hsenderSize : (ammTransferSenderHashMem I).size = 96 := by
    unfold ammTransferSenderHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have htoSize : (ammTransferToHashMem I).size = 96 := by
    unfold ammTransferToHashMem
    exact twoWordHashMem_size_96 _ _ hsenderSize
  obtain ⟨_, _, rd4537⟩ := RD.ammMappingHashSuffix rd4524 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFinalHashMem,
      ammTransferToSlot_eq_solc I hcanonTo] using
        (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferToWord I) htoSize))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4539 := evm_run rd4537 with [dup2, swap1]
  obtain ⟨_, _, rd4540⟩ := rd4539.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [ammTransferEvmPostMap] using
    (evm_run rd4540 with [pop])⟩

theorem ammX_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (ammTransferToWord I).toNat < EVM.addressModulus)
    (hle : (ammTransferValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferEvmDebitMap σ I) I
      (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, ammTransferEvmPostMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd4541⟩ := ammTransferX_stored (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo hle hfit hreach
  have rd464 := evm_run rd4541 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump (by jump_dest) ]
  have hmem : (ammTransferFinalHashMem I).size = 96 := by
    unfold ammTransferFinalHashMem ammTransferToHashMem ammTransferSenderHashMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hread : (ammTransferFinalHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold ammTransferFinalHashMem ammTransferToHashMem ammTransferSenderHashMem
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammTransferFinalHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammTransferFinalHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd5629 := evm_run rd464 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨477⟩, swap2, swap1, push2 ⟨5629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd477⟩ := RD.ammRoutineEncodeBoolFromMem
    (memout := ammWordReturnMem (ammTransferFinalHashMem I) (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd477 with [
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

theorem ammTransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammTransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammTransferX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := ammTransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammTransferX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (ammTransferToWord I)
      (UInt256.land (ammTransferToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨438⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammTransferX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammTransferSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swap0Transition, swap1Transition,
      totalSupplyTransition])
    (post := [transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammTransferSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, ammAllowanceSelectorBytes, hcd]
    | rw [selectorOf, ammApproveSelectorBytes, hcd]
    | rw [selectorOf, ammBalanceOfSelectorBytes, hcd]
    | rw [selectorOf, ammBurnSelectorBytes, hcd]
    | rw [selectorOf, ammMintSelectorBytes, hcd]
    | rw [selectorOf, ammSwap0SelectorBytes, hcd]
    | rw [selectorOf, ammSwap1SelectorBytes, hcd]
    | rw [selectorOf, ammTotalSupplySelectorBytes, hcd]
  all_goals decide

/-- The transfer wrapper, entered at PC 438, refines its Solm transition. -/
theorem ammTransferBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨438⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammTransferSelector_size hsel
  have hd := ammDispatch_transfer (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (ammTransferToWord I).toNat < EVM.addressModulus
      · have hdec := ammDecode_transfer_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hfromE : ammTransferFromWord evmE I =
            solcSlotWord σ_evm I (ammTransferSenderSlot I) := by
          simpa [ammTransferFromWord, solcSlotWord, codeOwnerStorageWord] using
            (codeOwnerStorageWord_initState
              (g := Sat256.ofUInt256 g) (σ := σ_evm)
              (slot := ammTransferSenderSlot I) (cA := cA) (gh := gh)
              (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
        have hfromS : ammTransferFromWord evmS I =
            solcSlotWord σ_evm I (ammTransferSenderSlot I) := by
          rw [show ammTransferFromWord evmS I = ammTransferFromWord evmE I
            from (hσ.storageLoad_codeOwner (ammTransferSenderSlot I)).symm, hfromE]
        by_cases hle : (ammTransferValueWord I).toNat ≤
            (solcSlotWord σ_evm I (ammTransferSenderSlot I)).toNat
        · have hleE : (ammTransferValueWord I).toNat ≤
              (ammTransferFromWord evmE I).toNat := by rwa [hfromE]
          have hleS : (ammTransferValueWord I).toNat ≤
              (ammTransferFromWord evmS I).toNat := by rwa [hfromS]
          have hdebit : ammTransferDebitWord evmE I =
              ammTransferDebitWord evmS I := by
            unfold ammTransferDebitWord
            rw [hfromE, hfromS]
          have hσDebit : EVMStateEquiv
              (ammTransferAfterDebit evmE I) (ammTransferAfterDebit evmS I) := by
            unfold ammTransferAfterDebit
            exact hσ.storageStore_codeOwner (ammTransferSenderSlot I) hdebit
          have hmapDebit : (ammTransferAfterDebit evmE I).accountMap =
              ammTransferEvmDebitMap σ_evm I := by
            unfold ammTransferAfterDebit ammTransferEvmDebitMap
            rw [storageStore_accountMap,
              show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
              show evmE.accountMap = σ_evm from rfl,
              ammTransferDebitWord_eq_sub evmE I hleE, hfromE]
          have htoE : ammTransferToBalanceWord evmE I =
              solcSlotWord (ammTransferEvmDebitMap σ_evm I) I
                (ammTransferToSlot I) := by
            unfold ammTransferToBalanceWord
            rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
            simp only [Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, solcSlotWord, hmapDebit]
          have htoS : ammTransferToBalanceWord evmS I =
              solcSlotWord (ammTransferEvmDebitMap σ_evm I) I
                (ammTransferToSlot I) := by
            rw [show ammTransferToBalanceWord evmS I =
                ammTransferToBalanceWord evmE I from by
                  unfold ammTransferToBalanceWord
                  rw [← ammTransferAfterDebit_codeOwner evmE I,
                    ← ammTransferAfterDebit_codeOwner evmS I]
                  exact (hσDebit.storageLoad_codeOwner (ammTransferToSlot I)).symm,
              htoE]
          have hnewE : ammTransferNewToNat evmE I =
              (solcSlotWord (ammTransferEvmDebitMap σ_evm I) I
                (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat := by
            rw [ammTransferNewToNat, htoE]
          have hnewS : ammTransferNewToNat evmS I =
              (solcSlotWord (ammTransferEvmDebitMap σ_evm I) I
                (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat := by
            rw [ammTransferNewToNat, htoS]
          by_cases hfit : (solcSlotWord (ammTransferEvmDebitMap σ_evm I) I
              (ammTransferToSlot I)).toNat + (ammTransferValueWord I).toNat < UInt256.size
          · have hfitE : ammTransferNewToNat evmE I < UInt256.size := by
              rwa [hnewE]
            have hfitS : ammTransferNewToNat evmS I < UInt256.size := by
              rwa [hnewS]
            have hnewWord : ammTransferNewToWord evmE I =
                ammTransferNewToWord evmS I := by
              unfold ammTransferNewToWord
              rw [hnewE, hnewS]
            have hσPost : EVMStateEquiv
                (ammTransferPostState evmE I) (ammTransferPostState evmS I) := by
              unfold ammTransferPostState
              rw [← ammTransferAfterDebit_codeOwner evmE I,
                ← ammTransferAfterDebit_codeOwner evmS I]
              exact hσDebit.storageStore_codeOwner (ammTransferToSlot I) hnewWord
            have hmapPost : (ammTransferPostState evmE I).accountMap =
                ammTransferEvmPostMap σ_evm I := by
              unfold ammTransferPostState ammTransferEvmPostMap
              rw [storageStore_accountMap,
                show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
                hmapDebit, ammTransferNewToWord_eq_add evmE I hfitE, htoE]
            have hbody := ammTransferBodyReturns evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hfitS
            have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
                (some [(.bool true)]) transferTransition.returnType :=
              returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
            exact (ammX_transfer (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle hfit hreach)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [evmE, ammTransferPostState, ammTransferAfterDebit,
                  initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
          · have hover : UInt256.size ≤ ammTransferNewToNat evmS I := by
              rw [hnewS]
              omega
            have hbody := ammTransferBodyReverts_overflow evmS I
              (by simp only [evmS, initState]; exact hwv) (by rfl) hleS hover
            exact (ammTransferX_overflow (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hle (by omega) hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hunderE : (solcSlotWord σ_evm I (ammTransferSenderSlot I)).toNat <
              (ammTransferValueWord I).toNat := by omega
          have hunderS : (ammTransferFromWord evmS I).toNat <
              (ammTransferValueWord I).toNat := by rw [hfromS]; exact hunderE
          have hbody := ammTransferBodyReverts_underflow evmS I
            (by simp only [evmS, initState]; exact hwv) (by rfl) hunderS
          exact (ammTransferX_underflow (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hunderE hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := ammDecode_transfer_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (ammTransferToWord I)
            (UInt256.land (ammTransferToWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ammTransferX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ammDecode_transfer_none_huge (I := I) hbigge
      exact (ammTransferX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := ammDecode_transfer_none_short (I := I) hsz4 hshort
    exact (ammTransferX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm
