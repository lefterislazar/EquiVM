import Benchmarks.ActAmmToken.Decode
import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `mint` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev mintAccountWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev mintValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev mintAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (mintAccountWord I).toNat)

abbrev mintValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (mintValueWord I).toNat)

abbrev mintStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "account" (mintAccountValue I)).insert
    "value" (mintValueValue I)

def mintBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (mintAccountWord I).toNat))

theorem mintBalanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (mintAccountWord I) = mintBalanceSlot I := by
  unfold mintBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def mintSupplyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩

def mintSupplyCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (mintSupplyWord evm).toNat + (mintValueWord I).toNat

def mintSupplyCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (mintSupplyCreditNat evm I)

def mintAfterSupply (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (mintSupplyCreditWord evm I)

def mintBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (mintAfterSupply evm I) evm.executionEnv.codeOwner
    (mintBalanceSlot I)

def mintBalanceCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (mintBalanceWord evm I).toNat + (mintValueWord I).toNat

def mintBalanceCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (mintBalanceCreditNat evm I)

def mintPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (mintAfterSupply evm I) evm.executionEnv.codeOwner
    (mintBalanceSlot I) (mintBalanceCreditWord evm I)

def mintEvmSupplyMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩
    (solcSlotWord σ I ⟨0⟩ + mintValueWord I)

def mintEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (mintEvmSupplyMap σ I) (mintBalanceSlot I)
    (solcSlotWord (mintEvmSupplyMap σ I) I (mintBalanceSlot I) + mintValueWord I)

noncomputable def mintBalanceHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨1⟩ solcFreePtrMem

noncomputable def mintFinalHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨1⟩ (mintBalanceHashMem I)

theorem mintStore_account (I : ExecutionEnv) :
    (mintStore I).get? "account" = some (mintAccountValue I) := by
  rw [mintStore, store_get_ne _ _ (by decide), store_get_self]

theorem mintStore_value (I : ExecutionEnv) :
    (mintStore I).get? "value" = some (mintValueValue I) := by
  rw [mintStore, store_get_self]

theorem mintStore_totalSupply (I : ExecutionEnv) :
    (mintStore I).get? "totalSupply" = none := by
  rw [mintStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintStore_balanceOf (I : ExecutionEnv) :
    (mintStore I).get? "balanceOf" = none := by
  rw [mintStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintEvalSupplyRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
    EvalResult.bind, pure, bind]

theorem mintEvalSupply (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat (mintSupplyWord evm).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := mintStore_totalSupply I)
    (her := mintEvalSupplyRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)]
  simp [mintSupplyWord, tokenStorageLocLoad_uint256]

theorem mintEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.var "value") = .ok (mintValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, mintStore_value]

theorem mintEvalSupplyCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (checkedAdd (.storage totalSupplyRef) (.var "value")) =
        .ok (.int (Int.ofNat (mintSupplyCreditNat evm I))) := by
  exact tokenEvalCheckedAdd_ok (mintEvalSupply evm I)
    (mintEvalValue evm I) hfit

theorem mintEvalSupplyCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintSupplyCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (checkedAdd (.storage totalSupplyRef) (.var "value")) = .revert := by
  exact tokenEvalCheckedAdd_revert (mintEvalSupply evm I)
    (mintEvalValue evm I) hover

theorem mintSupplyCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    (mintSupplyCreditWord evm I).toNat = mintSupplyCreditNat evm I := by
  unfold mintSupplyCreditWord
  exact ulit_toNat' _ hfit

theorem mintSupplyCreditWord_eq_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    mintSupplyCreditWord evm I = mintSupplyWord evm + mintValueWord I := by
  apply u256_inj
  rw [mintSupplyCreditWord_toNat evm I hfit, uadd_toNat]
  rw [show (mintSupplyWord evm).toNat + (mintValueWord I).toNat =
    mintSupplyCreditNat evm I from rfl, Nat.mod_eq_of_lt hfit]

theorem mintAssignSupply (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintSupplyCreditNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := mintStore I } evm
      .storage totalSupplyRef
      (.int (Int.ofNat (mintSupplyCreditNat evm I))) =
      .ok ({ contract := contract, locals := mintStore I },
        mintAfterSupply evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := mintStore_totalSupply I)
    (her := mintEvalSupplyRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)
  simpa [mintAfterSupply, mintSupplyCreditWord_toNat evm I hfit] using
    tokenStorageLocStore_uint256 evm ⟨0⟩ (mintSupplyCreditWord evm I)

theorem mintAfterSupply_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (mintAfterSupply evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [mintAfterSupply, storageStore_executionEnv]

def mintBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (mintAccountWord I).toNat))] }

theorem mintEvalBalanceRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      (balanceOfRef (.var "account")) = .ok (mintBalanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, mintBalanceRef, mintAccountValue, mintStore_account]

theorem mintEvalBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.storage (balanceOfRef (.var "account"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (mintBalanceSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := mintStore_balanceOf I)
    (her := mintEvalBalanceRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      mintBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [mintBalanceSlot, tokenStorageLocLoad_uint256]

theorem mintEvalBalanceCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintBalanceCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (mintAfterSupply evm I)
      (checkedAdd (.storage (balanceOfRef (.var "account"))) (.var "value")) =
        .ok (.int (Int.ofNat (mintBalanceCreditNat evm I))) := by
  have hload := mintEvalBalance (mintAfterSupply evm I) I
  rw [mintAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_ok hload
    (mintEvalValue (mintAfterSupply evm I) I) hfit

theorem mintEvalBalanceCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ mintBalanceCreditNat evm I) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (mintAfterSupply evm I)
      (checkedAdd (.storage (balanceOfRef (.var "account"))) (.var "value")) =
        .revert := by
  have hload := mintEvalBalance (mintAfterSupply evm I) I
  rw [mintAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_revert hload
    (mintEvalValue (mintAfterSupply evm I) I) hover

theorem mintBalanceCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintBalanceCreditNat evm I < UInt256.size) :
    (mintBalanceCreditWord evm I).toNat = mintBalanceCreditNat evm I := by
  unfold mintBalanceCreditWord
  exact ulit_toNat' _ hfit

theorem mintBalanceCreditWord_eq_add (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintBalanceCreditNat evm I < UInt256.size) :
    mintBalanceCreditWord evm I = mintBalanceWord evm I + mintValueWord I := by
  apply u256_inj
  rw [mintBalanceCreditWord_toNat evm I hfit, uadd_toNat]
  rw [show (mintBalanceWord evm I).toNat + (mintValueWord I).toNat =
    mintBalanceCreditNat evm I from rfl, Nat.mod_eq_of_lt hfit]

theorem mintAssignBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : mintBalanceCreditNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := mintStore I }
      (mintAfterSupply evm I) .storage (balanceOfRef (.var "account"))
      (.int (Int.ofNat (mintBalanceCreditNat evm I))) =
      .ok ({ contract := contract, locals := mintStore I },
        mintPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := mintStore_balanceOf I)
    (her := mintEvalBalanceRef (mintAfterSupply evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      mintBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [mintPostState, mintAfterSupply_codeOwner evm I,
    mintBalanceCreditWord_toNat evm I hfit] using
    tokenStorageLocStore_uint256 (mintAfterSupply evm I)
      (mintBalanceSlot I) (mintBalanceCreditWord evm I)

theorem mintBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsupply : mintSupplyCreditNat evm I < UInt256.size)
    (hbalance : mintBalanceCreditNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (mintStore I)
      mintTransition.body
      (.returned { contract := contract, locals := mintStore I }
        (mintPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (mintEvalSupplyCredit_ok evm I hsupply)
      (mintAssignSupply evm I hsupply)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (mintEvalBalanceCredit_ok evm I hbalance)
      (mintAssignBalance evm I hbalance)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem mintBodyReverts_supply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤ mintSupplyCreditNat evm I) :
    ExecTransitionBody config contract evm (mintStore I)
      mintTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.assignExprRevert (mintEvalSupplyCredit_revert evm I hover))

theorem mintBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsupply : mintSupplyCreditNat evm I < UInt256.size)
    (hover : UInt256.size ≤ mintBalanceCreditNat evm I) :
    ExecTransitionBody config contract evm (mintStore I)
      mintTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (mintEvalSupplyCredit_ok evm I hsupply)
          (mintAssignSupply evm I hsupply)) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (mintEvalBalanceCredit_revert evm I hover))


theorem tokenDecode_mint_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata =
        some (mintStore I) := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, mintStore, mintAccountValue,
    mintValueValue, mintAccountWord, mintValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "account") (y := "value") hsz68 hbig hcanon

theorem tokenDecode_mint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_short
    (cd := I.calldata) (x := "account") (y := "value") hsz4 hshort

theorem tokenDecode_mint_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (mintAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, mintAccountWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "account") (y := "value") hsz68 hbig hnc

theorem tokenDecode_mint_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (mintTransition.params.map Param.name)
      (transitionSignature mintTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_huge
    (cd := I.calldata) (x := "account") (y := "value") hbig

theorem mintX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2977⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨301⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨296⟩, swap2, swap1, push2 ⟨2977⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem mintX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3012⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := mintX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3012⟩, dup6, dup3, dup7, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

theorem mintX_dec5576 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3012⟩
      [mintAccountWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := mintX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem mintX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3029⟩, ⟨32⟩,
        ⟨0⟩, mintAccountWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨296⟩, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := mintX_dec5576 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨3029⟩,
    dup6, dup3, dup7, add, push2 ⟨2957⟩, jump (by jump_dest) ]⟩

theorem mintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1518⟩
      [mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5521⟩ := mintX_dec5521_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd5499 := evm_run rd5521 with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨2971⟩, dup2, push2 ⟨2935⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨2944⟩, dup2, push2 ⟨2926⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]
  have heq : UInt256.eq (mintValueWord I) (mintValueWord I) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨2954⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1518⟩, jump (by jump_dest) ]⟩

theorem mintX_supplyLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1523⟩
      [solcSlotWord σ I ⟨0⟩, mintValueWord I, ⟨0⟩,
        mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := mintX_decoded hsz68 hsize hszhi hcanon hreach
  have rdLoad := evm_run rd with [jumpdest, push0, dup2, push0]
  obtain ⟨_, _, rdLoaded⟩ := rdLoad.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rdLoaded⟩

theorem mintX_supplyCredit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfit : (solcSlotWord σ I ⟨0⟩).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1532⟩
      [solcSlotWord σ I ⟨0⟩ + mintValueWord I, ⟨0⟩,
        mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := mintX_supplyLoad hsz68 hsize hszhi hcanon hreach
  have rdAdd := evm_run rd with [
    push2 ⟨1532⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest)]
  exact RD.tokenCheckedAddOk rdAdd hfit (by jump_dest) (by evm_ov)

theorem mintX_supplyOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hover : UInt256.size ≤ (solcSlotWord σ I ⟨0⟩).toNat + (mintValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := mintX_supplyLoad hsz68 hsize hszhi hcanon hreach
  have rdAdd := evm_run rd with [
    push2 ⟨1532⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest)]
  exact RD.tokenCheckedAddOverflow rdAdd hover (by evm_ov)

theorem mintX_supplyStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfit : (solcSlotWord σ I ⟨0⟩).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1538⟩
      [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmSupplyMap σ I) k C := by
  obtain ⟨_, _, rd⟩ := mintX_supplyCredit hsz68 hsize hszhi hcanon hfit hreach
  have rdStore := evm_run rd with [jumpdest, push0, dup2, swap1]
  obtain ⟨_, _, rdStored⟩ := rdStore.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [mintEvmSupplyMap] using (evm_run rdStored with [pop])⟩

theorem mintX_balanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfit : (solcSlotWord σ I ⟨0⟩).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1601⟩
      [solcSlotWord (mintEvmSupplyMap σ I) I (mintBalanceSlot I),
        mintValueWord I, ⟨0⟩, mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      (mintBalanceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmSupplyMap σ I) k C := by
  obtain ⟨k, C, rd1538⟩ := mintX_supplyStore
    hsz68 hsize hszhi hperm hcanon hfit hreach
  have haccountClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanon
  have rd1587₀ := evm_run rd1538 with [
    dup2, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd1587 := rd1587₀
  rw [haccountClean, haccountClean] at rd1587
  obtain ⟨_, _, rd1600⟩ := RD.tokenMappingHashSuffix rd1587
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [mintBalanceHashMem, mintBalanceSlot_eq_solc I hcanon] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (mintAccountWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1601⟩ := rd1600.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [mintBalanceHashMem] using rd1601⟩

theorem mintX_balanceCredit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfitSupply : (solcSlotWord σ I ⟨0⟩).toNat +
      (mintValueWord I).toNat < UInt256.size)
    (hfitBalance : (solcSlotWord (mintEvmSupplyMap σ I) I
      (mintBalanceSlot I)).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1610⟩
      [solcSlotWord (mintEvmSupplyMap σ I) I (mintBalanceSlot I) +
        mintValueWord I, ⟨0⟩, mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      (mintBalanceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmSupplyMap σ I) k C := by
  obtain ⟨_, _, rd⟩ := mintX_balanceLoad
    hsz68 hsize hszhi hperm hcanon hfitSupply hreach
  have rdAdd := evm_run rd with [
    push2 ⟨1610⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest)]
  exact RD.tokenCheckedAddOk rdAdd hfitBalance (by jump_dest) (by evm_ov)

theorem mintX_balanceOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfitSupply : (solcSlotWord σ I ⟨0⟩).toNat +
      (mintValueWord I).toNat < UInt256.size)
    (hover : UInt256.size ≤ (solcSlotWord (mintEvmSupplyMap σ I) I
      (mintBalanceSlot I)).toNat + (mintValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := mintX_balanceLoad
    hsz68 hsize hszhi hperm hcanon hfitSupply hreach
  have rdAdd := evm_run rd with [
    push2 ⟨1610⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest)]
  exact RD.tokenCheckedAddOverflow rdAdd hover (by evm_ov)

theorem mintX_balanceStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfitSupply : (solcSlotWord σ I ⟨0⟩).toNat +
      (mintValueWord I).toNat < UInt256.size)
    (hfitBalance : (solcSlotWord (mintEvmSupplyMap σ I) I
      (mintBalanceSlot I)).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1676⟩
      [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨301⟩, sel]
      (mintFinalHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, mintEvmPostMap σ I) k C := by
  obtain ⟨_, _, rd1610⟩ := mintX_balanceCredit
    hsz68 hsize hszhi hperm hcanon hfitSupply hfitBalance hreach
  have haccountClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanon
  have rd1659₀ := evm_run rd1610 with [
    jumpdest, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd1659 := rd1659₀
  rw [haccountClean, haccountClean] at rd1659
  have hmem : (mintBalanceHashMem I).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd1672⟩ := RD.tokenMappingHashSuffix rd1659
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [mintFinalHashMem, mintBalanceSlot_eq_solc I hcanon] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (mintAccountWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1674 := evm_run rd1672 with [dup2, swap1]
  obtain ⟨_, _, rd1675⟩ := rd1674.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [mintEvmPostMap, mintFinalHashMem] using
    (evm_run rd1675 with [pop])⟩



theorem mintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := mintX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem mintX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := mintX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem mintX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (mintAccountWord I)
      (UInt256.land (mintAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨275⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := mintX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)


theorem mintX_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hfitSupply : (solcSlotWord σ I ⟨0⟩).toNat + (mintValueWord I).toNat < UInt256.size)
    (hfitBalance : (solcSlotWord (mintEvmSupplyMap σ I) I
      (mintBalanceSlot I)).toNat + (mintValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨275⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, mintEvmPostMap σ I) (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1676⟩ := mintX_balanceStore
    hsz68 hsize hszhi hperm hcanon hfitSupply hfitBalance hreach
  have rd301 := evm_run rd1676 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hmem : (mintFinalHashMem I).size = 96 :=
    twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  have hread : (mintFinalHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold mintFinalHashMem mintBalanceHashMem
    apply twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (mintFinalHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((mintFinalHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread
  have rd3065 := evm_run rd301 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨314⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd314⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := tokenWordReturnMem (mintFinalHashMem I) (⟨1⟩ : UInt256))
    rd3065 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd314 with [
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

theorem tokenMintSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x40, 0xc1, 0x0f, 0x19]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_mint {cd : ByteArray}
    (hsel : ((⟨#[0x40, 0xc1, 0x0f, 0x19]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some mintTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x40, 0xc1, 0x0f, 0x19]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, burnFromTransition])
    (post := [totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, mintSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, allowanceSelectorBytes, hcd]
    | rw [selectorOf, approveSelectorBytes, hcd]
    | rw [selectorOf, balanceOfSelectorBytes, hcd]
    | rw [selectorOf, burnSelectorBytes, hcd]
    | rw [selectorOf, burnFromSelectorBytes, hcd]
  all_goals decide


theorem tokenMintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Ethereum.UInt256}
    (hcode : I.code = tokenBytecode)
    (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨275⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenMintSelector_size hsel
  have hd := tokenDispatch_mint (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (mintAccountWord I).toNat < EVM.addressModulus
      · have hdec := tokenDecode_mint_ok (I := I) hsz68 hbig hcanon
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hsupplyE : mintSupplyWord evmE = solcSlotWord σ_evm I ⟨0⟩ := by
          rfl
        have hsupplyS : mintSupplyWord evmS = solcSlotWord σ_evm I ⟨0⟩ := by
          rw [show mintSupplyWord evmS = mintSupplyWord evmE from
            (hσ.storageLoad_codeOwner ⟨0⟩).symm, hsupplyE]
        by_cases hfitSupply : (solcSlotWord σ_evm I ⟨0⟩).toNat +
            (mintValueWord I).toNat < UInt256.size
        · have hfitE : mintSupplyCreditNat evmE I < UInt256.size := by
            simpa [mintSupplyCreditNat, hsupplyE] using hfitSupply
          have hfitS : mintSupplyCreditNat evmS I < UInt256.size := by
            simpa [mintSupplyCreditNat, hsupplyS] using hfitSupply
          have hcredit : mintSupplyCreditWord evmE I =
              mintSupplyCreditWord evmS I := by
            unfold mintSupplyCreditWord mintSupplyCreditNat
            rw [hsupplyE, hsupplyS]
          have hσSupply : EVMStateEquiv
              (mintAfterSupply evmE I) (mintAfterSupply evmS I) := by
            unfold mintAfterSupply
            exact hσ.storageStore_codeOwner ⟨0⟩ hcredit
          have hmapSupply : (mintAfterSupply evmE I).accountMap =
              mintEvmSupplyMap σ_evm I := by
            unfold mintAfterSupply mintEvmSupplyMap
            rw [storageStore_accountMap,
              show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
              show evmE.accountMap = σ_evm from rfl,
              mintSupplyCreditWord_eq_add evmE I hfitE, hsupplyE]
          have hbalanceE : mintBalanceWord evmE I =
              solcSlotWord (mintEvmSupplyMap σ_evm I) I (mintBalanceSlot I) := by
            unfold mintBalanceWord
            rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
            simp only [Solm.EVM.storageLoad, State.lookupAccount,
              Account.lookupStorage, solcSlotWord, hmapSupply]
          have hbalanceS : mintBalanceWord evmS I =
              solcSlotWord (mintEvmSupplyMap σ_evm I) I (mintBalanceSlot I) := by
            rw [show mintBalanceWord evmS I = mintBalanceWord evmE I from by
                unfold mintBalanceWord
                rw [← mintAfterSupply_codeOwner evmE I,
                  ← mintAfterSupply_codeOwner evmS I]
                exact (hσSupply.storageLoad_codeOwner (mintBalanceSlot I)).symm,
              hbalanceE]
          by_cases hfitBalance : (solcSlotWord (mintEvmSupplyMap σ_evm I) I
              (mintBalanceSlot I)).toNat + (mintValueWord I).toNat < UInt256.size
          · have hfitBalE : mintBalanceCreditNat evmE I < UInt256.size := by
              simpa [mintBalanceCreditNat, hbalanceE] using hfitBalance
            have hfitBalS : mintBalanceCreditNat evmS I < UInt256.size := by
              simpa [mintBalanceCreditNat, hbalanceS] using hfitBalance
            have hbalanceCredit : mintBalanceCreditWord evmE I =
                mintBalanceCreditWord evmS I := by
              unfold mintBalanceCreditWord mintBalanceCreditNat
              rw [hbalanceE, hbalanceS]
            have hσPost : EVMStateEquiv
                (mintPostState evmE I) (mintPostState evmS I) := by
              unfold mintPostState
              rw [← mintAfterSupply_codeOwner evmE I,
                ← mintAfterSupply_codeOwner evmS I]
              exact hσSupply.storageStore_codeOwner (mintBalanceSlot I) hbalanceCredit
            have hmapPost : (mintPostState evmE I).accountMap =
                mintEvmPostMap σ_evm I := by
              unfold mintPostState mintEvmPostMap
              rw [storageStore_accountMap,
                show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
                hmapSupply, mintBalanceCreditWord_eq_add evmE I hfitBalE,
                hbalanceE]
            have hbody := mintBodyReturns evmS I
              (by simp only [evmS, initState]; exact hwv) hfitS hfitBalS
            have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
                (some [(.bool true)]) mintTransition.returnType :=
              returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
            exact (mintX_return (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hfitSupply hfitBalance hreach)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [evmE, mintPostState, mintAfterSupply,
                  initState, storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
          · have hoverE : UInt256.size ≤
                (solcSlotWord (mintEvmSupplyMap σ_evm I) I
                  (mintBalanceSlot I)).toNat + (mintValueWord I).toNat := by omega
            have hoverS : UInt256.size ≤ mintBalanceCreditNat evmS I := by
              simpa [mintBalanceCreditNat, hbalanceS] using hoverE
            have hbody := mintBodyReverts_balance evmS I
              (by simp only [evmS, initState]; exact hwv) hfitS hoverS
            exact (mintX_balanceOverflow (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanon hfitSupply hoverE hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hoverE : UInt256.size ≤
              (solcSlotWord σ_evm I ⟨0⟩).toNat + (mintValueWord I).toNat := by omega
          have hoverS : UInt256.size ≤ mintSupplyCreditNat evmS I := by
            simpa [mintSupplyCreditNat, hsupplyS] using hoverE
          have hbody := mintBodyReverts_supply evmS I
            (by simp only [evmS, initState]; exact hwv) hoverS
          exact (mintX_supplyOverflow (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanon hoverE hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := tokenDecode_mint_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (mintAccountWord I)
            (UInt256.land (mintAccountWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (mintX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_mint_none_huge (I := I) hbigge
      exact (mintX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := tokenDecode_mint_none_short (I := I) hsz4 hshort
    exact (mintX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
