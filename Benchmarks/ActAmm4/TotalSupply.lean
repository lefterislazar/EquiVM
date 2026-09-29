import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

def amm4TotalSupplyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

theorem amm4TotalSupplyBodyReturns (evm : EVM.State) (locals : Store)
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
        amm4StorageLocLoad_uint256])

theorem amm4TotalSupplySelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    4 ≤ I.calldata.size := by
  exact calldata_size_ge_of_selIs I _ rfl hsel

theorem amm4Dispatch_totalSupply {cd : ByteArray}
    (hsel : ((⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some totalSupplyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swapTransition])
    (post := [transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4TotalSupplySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, amm4AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4BurnSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4MintSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4SwapSelectorBytes, hcd]; decide

theorem amm4Decode_totalSupply {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (totalSupplyTransition.params.map Param.name)
      (transitionSignature totalSupplyTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4X_totalSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨197⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (amm4TotalSupplyWord σ I)) := by
  obtain ⟨_, _, rd197⟩ := hreach
  have rd713 := evm_run rd197 with [
    jumpdest, push2 ⟨205⟩, push2 ⟨711⟩, jump (by jump_dest),
    jumpdest, push0 ]
  obtain ⟨_, _, rd714⟩ := rd713.sload (by native_decide) (by evm_ov)
  have rd205 := evm_run rd714 with [dup2, jump (by jump_dest)]
  have rd4856 := evm_run rd205 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨218⟩, swap2, swap1, push2 ⟨4856⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd218⟩ := RD.amm4RoutineEncodeUint256FromMem rd4856
    (by rfl) (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd218 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (solcReturnMem_mload64 (amm4TotalSupplyWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (amm4TotalSupplyWord σ I)) (by native_decide)
      mem_cost
      (by
        change (solcReturnMem (amm4TotalSupplyWord σ I)).readWithPadding
          (⟨128⟩ : UInt256).toNat
          (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat =
            UInt256.toByteArray (amm4TotalSupplyWord σ I)
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov) ]

/-- The totalSupply wrapper, entered at PC 197, refines its Solm transition. -/
theorem amm4TotalSupplyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨197⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := amm4TotalSupplySelector_size hsel
  have hd := amm4Dispatch_totalSupply (cd := I.calldata) hsel
  have hdec := amm4Decode_totalSupply (I := I) hsz
  have hword : amm4TotalSupplyWord σ_evm I = amm4TotalSupplyWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        totalSupplyTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (amm4TotalSupplyWord σ_solm I).toNat))])) := by
    simpa [amm4TotalSupplyWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using amm4TotalSupplyBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (amm4X_totalSupply (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody
      (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by
        simpa [uint256, uint256Int] using
          (uint256ReturnEncoding (amm4TotalSupplyWord σ_evm I))))

end Benchmarks.ActAmm4
