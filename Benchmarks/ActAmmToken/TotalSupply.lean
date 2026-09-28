import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `totalSupply` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

def totalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

theorem totalSupplyWord_eq_storageLoad_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    totalSupplyWord σ I =
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨0⟩ :=
  rfl

theorem tokenTotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "totalSupply" = none) :
    ExecTransitionBody config contract evm locals totalSupplyTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "totalSupply", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := tokenConfig_storage_totalSupply), tokenStorageLocLoad_uint256])

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem tokenX_totalSupply {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨197⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (totalSupplyWord σ I)) := by
  obtain ⟨k, C, rd197⟩ := hreach
  have rd752 := evm_run rd197 with [
    jumpdest, push2 ⟨205⟩, push2 ⟨751⟩, jump (by jump_dest),
    jumpdest, push0 ]
  obtain ⟨k1, C1, rd753⟩ := rd752.sload (by decide) (by evm_ov)
  have rd205 := evm_run rd753 with [dup2, jump (by jump_dest)]
  have rd3105 := evm_run rd205 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨218⟩, swap2, swap1, push2 ⟨3105⟩, jump (by jump_dest) ]
  obtain ⟨k2, C2, rd218⟩ := rd3105.tokenRoutineEncodeUint256 (by jump_dest) (by
    simp only [List.length_cons, List.length_nil]
    omega)
  exact evm_run rd218 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 (totalSupplyWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (totalSupplyWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128]
        rfl)
      (by evm_ov) ]

theorem tokenTotalSupplySelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some totalSupplyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, burnFromTransition, mintTransition])
    (post := [transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, totalSupplySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, allowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, approveSelectorBytes, hcd]; decide
  · rw [selectorOf, balanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, burnSelectorBytes, hcd]; decide
  · rw [selectorOf, burnFromSelectorBytes, hcd]; decide
  · rw [selectorOf, mintSelectorBytes, hcd]; decide

theorem tokenDecode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem tokenTotalSupplyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Ethereum.UInt256}
    (hcode : I.code = tokenBytecode)
    (_hsize : I.calldata.size < Ethereum.UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨197⟩
      [tokenSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := tokenTotalSupplySelector_size hsel
  have hd := tokenDispatch_totalSupply (cd := I.calldata) hsel
  have hdec := tokenDecode_totalSupply (I := I) hsz
  have hword : totalSupplyWord σ_evm I = totalSupplyWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ totalSupplyTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (totalSupplyWord σ_solm I).toNat))])) := by
    simpa [totalSupplyWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      tokenTotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (tokenX_totalSupply (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport
    hcode hd hdec hbody (by rw [hword]) hAccounts
    (returnEquiv_of_encode (tokenUint256ReturnEncoding (totalSupplyWord σ_evm I)))

end Benchmarks.ActAmmToken
