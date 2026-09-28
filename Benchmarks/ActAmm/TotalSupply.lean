import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

def ammTotalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

theorem ammTotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "totalSupply" = none) :
    ExecTransitionBody config contract evm locals totalSupplyTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          totalSupplyRef = .ok { base := "totalSupply", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
          EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage
          ({ base := "totalSupply", steps := [] } : EvaledStorageRef) =
            some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := hlocals) (her := her) (hty := hty) (hloc := by rfl),
        ammStorageLocLoad_uint256])

theorem ammTotalSupplySelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some totalSupplyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swap0Transition, swap1Transition])
    (post := [transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammTotalSupplySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ammAllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, ammApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, ammBalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, ammBurnSelectorBytes, hcd]; decide
  · rw [selectorOf, ammMintSelectorBytes, hcd]; decide
  · rw [selectorOf, ammSwap0SelectorBytes, hcd]; decide
  · rw [selectorOf, ammSwap1SelectorBytes, hcd]; decide

theorem ammDecode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammX_totalSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨236⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (ammTotalSupplyWord σ I)) := by
  obtain ⟨_, _, rd236⟩ := hreach
  have rd1798 := evm_run rd236 with [
    jumpdest, push2 ⟨244⟩, push2 ⟨1796⟩, jump (by jump_dest),
    jumpdest, push0 ]
  obtain ⟨_, _, rd1799⟩ := rd1798.sload (by native_decide) (by evm_ov)
  have rd244 := evm_run rd1799 with [dup2, jump (by jump_dest)]
  have rd5731 := evm_run rd244 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨257⟩, swap2, swap1, push2 ⟨5731⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd257⟩ := RD.ammRoutineEncodeUint256FromMem rd5731
    (by rfl) (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd257 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcReturnMem_mload64 (ammTotalSupplyWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (ammTotalSupplyWord σ I)) (by native_decide)
      mem_cost
      (by
        change (solcReturnMem (ammTotalSupplyWord σ I)).readWithPadding
          (⟨128⟩ : UInt256).toNat
          (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat =
            UInt256.toByteArray (ammTotalSupplyWord σ I)
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov) ]

/-- The totalSupply wrapper, entered at PC 236, refines its Solm transition. -/
theorem ammTotalSupplyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨236⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := ammTotalSupplySelector_size hsel
  have hd := ammDispatch_totalSupply (cd := I.calldata) hsel
  have hdec := ammDecode_totalSupply (I := I) hsz
  have hword : ammTotalSupplyWord σ_evm I = ammTotalSupplyWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        totalSupplyTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (ammTotalSupplyWord σ_solm I).toNat))])) := by
    simpa [ammTotalSupplyWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using ammTotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (ammX_totalSupply (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by
        simpa [uint256, uint256Int] using
          (uint256ReturnEncoding (ammTotalSupplyWord σ_evm I))))

end Benchmarks.ActAmm
