import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammAllowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammAllowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev ammAllowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammAllowanceOwnerWord I).toNat)

abbrev ammAllowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammAllowanceSpenderWord I).toNat)

abbrev ammAllowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (ammAllowanceOwnerValue I)).insert
    "spender" (ammAllowanceSpenderValue I)

def ammAllowanceSlotFromCalldata (I : ExecutionEnv) : UInt256 :=
  allowanceSlot
    (.address (AccountAddress.ofNat (ammAllowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (ammAllowanceSpenderWord I).toNat))

theorem ammAllowanceSlot_eq_solc (I : ExecutionEnv)
    (howner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hspender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (ammAllowanceOwnerWord I))
      (ammAllowanceSpenderWord I) = ammAllowanceSlotFromCalldata I := by
  unfold ammAllowanceSlotFromCalldata allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ howner,
    keyValueToWord_address_of_canonical _ hspender]

def ammAllowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (ammAllowanceSlotFromCalldata I) ⟨0⟩)

def ammAllowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address (AccountAddress.ofNat (ammAllowanceOwnerWord I).toNat)),
      .mindex (.address (AccountAddress.ofNat (ammAllowanceSpenderWord I).toNat))] }

theorem ammDecode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata =
        some (ammAllowanceStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [ammAllowanceStore, ammAllowanceOwnerValue, ammAllowanceSpenderValue,
    ammAllowanceOwnerWord, ammAllowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata)
      (x := "owner") (y := "spender") hsz68 hbig hcanonOwner hcanonSpender

theorem ammDecode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem ammDecode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (ammAllowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, ammAllowanceOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem ammDecode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (ammAllowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, ammAllowanceOwnerWord, ammAllowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem ammDecode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

theorem ammAllowanceStore_owner (I : ExecutionEnv) :
    (ammAllowanceStore I).get? "owner" = some (ammAllowanceOwnerValue I) := by
  rw [ammAllowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem ammAllowanceStore_spender (I : ExecutionEnv) :
    (ammAllowanceStore I).get? "spender" = some (ammAllowanceSpenderValue I) := by
  rw [ammAllowanceStore, store_get_self]

theorem ammAllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammAllowanceStore I)
      allowanceTransition.body
      (.returned { contract := contract, locals := ammAllowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (ammAllowanceSlotFromCalldata I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config
          { contract := contract, locals := ammAllowanceStore I } evm
          (allowanceRef (.var "owner") (.var "spender")) =
            .ok (ammAllowanceEvaledRef I) := by
        simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
          evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
          ammAllowanceEvaledRef, ammAllowanceOwnerValue, ammAllowanceSpenderValue,
          ammAllowanceStore_owner, ammAllowanceStore_spender]
      have hty : storageTypeAt? contract.storage (ammAllowanceEvaledRef I) =
          some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, contract, storageDecls, ammAllowanceEvaledRef,
          uint256St, storageTypeStep?]
      have hloc : config.storage.layout (ammAllowanceEvaledRef I) =
          fun _ => some (wordLoc (ammAllowanceSlotFromCalldata I)) := by
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by
          rw [ammAllowanceStore, store_get_ne _ _ (by decide),
            store_get_ne _ _ (by decide)]
          simp)
        (her := her) (hty := hty) (hloc := hloc)]
      simp [ammAllowanceSlotFromCalldata, ammStorageLocLoad_uint256])

theorem ammAllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5879⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨507⟩, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨512⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨507⟩, swap2, swap1, push2 ⟨5879⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammAllowanceX_dec5470_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5914⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨507⟩, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5901⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5914⟩, dup6, dup3, dup7, add, push2 ⟨5470⟩,
    jump (by jump_dest) ]⟩

theorem ammAllowanceX_dec5914 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5914⟩
      [ammAllowanceOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨507⟩, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5470_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.ammDecodeAddrOk rd hcanonOwner (by jump_dest) (by evm_ov)

theorem ammAllowanceX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5931⟩, ⟨32⟩, ⟨0⟩,
        ammAllowanceOwnerWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨507⟩, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5914 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5931⟩, dup6, dup3, dup7,
    add, push2 ⟨5470⟩, jump (by jump_dest) ]⟩

theorem ammAllowanceX_dec5931 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5931⟩
      [ammAllowanceSpenderWord I, ⟨32⟩, ⟨0⟩, ammAllowanceOwnerWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨507⟩, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5470_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.ammDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem ammAllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4550⟩
      [ammAllowanceSpenderWord I, ammAllowanceOwnerWord I, ⟨512⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5931 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨4550⟩, jump (by jump_dest) ]⟩

theorem ammX_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (ammAllowanceWord σ I)) := by
  obtain ⟨_, _, rd4550⟩ := ammAllowanceX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  have hslot : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcNestedMappingHashMem ⟨2⟩ (ammAllowanceOwnerWord I)
        (ammAllowanceSpenderWord I)).readWithPadding 0 64))) =
      ammAllowanceSlotFromCalldata I := by
    rw [solcNestedMappingKeccakSlot,
      ammAllowanceSlot_eq_solc I hcanonOwner hcanonSpender]
  have rd4579 := evm_run rd4550 with [
    jumpdest, push1 ⟨2⟩, push1 ⟨32⟩,
    raw mstore 0 (solcMappingBaseSlotMem ⟨2⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (solcMappingHashMem ⟨2⟩ (ammAllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (solcMappingSlot ⟨2⟩ (ammAllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcMappingKeccakSlot ⟨2⟩ (ammAllowanceOwnerWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (solcNestedMappingOuterBaseMem ⟨2⟩ (ammAllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (solcNestedMappingHashMem ⟨2⟩ (ammAllowanceOwnerWord I)
      (ammAllowanceSpenderWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (ammAllowanceSlotFromCalldata I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap2, pop, pop ]
  obtain ⟨_, _, rd4580⟩ := rd4579.sload (by native_decide) (by evm_ov)
  have rd512 := evm_run rd4580 with [dup2, jump (by jump_dest)]
  have rd5731 := evm_run rd512 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (solcNestedMappingHashMem_mload64 ⟨2⟩
        (ammAllowanceOwnerWord I) (ammAllowanceSpenderWord I))
      (by decide) (by evm_ov),
    push2 ⟨525⟩, swap2, swap1, push2 ⟨5731⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd525⟩ := RD.ammRoutineEncodeUint256FromMem
    (memout := ammWordReturnMem
      (solcNestedMappingHashMem ⟨2⟩ (ammAllowanceOwnerWord I)
        (ammAllowanceSpenderWord I)) (ammAllowanceWord σ I))
    rd5731 (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd525 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (ammWordReturnMem_mload64_of_size96 (ammAllowanceWord σ I)
        (solcNestedMappingHashMem_size ⟨2⟩
          (ammAllowanceOwnerWord I) (ammAllowanceSpenderWord I))
        (solcNestedMappingHashMem_read64 ⟨2⟩
          (ammAllowanceOwnerWord I) (ammAllowanceSpenderWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (ammAllowanceWord σ I)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact ammWordReturnMem_read128_of_size96 (ammAllowanceWord σ I)
          (solcNestedMappingHashMem_size ⟨2⟩
            (ammAllowanceOwnerWord I) (ammAllowanceSpenderWord I)))
      (by evm_ov) ]

theorem ammAllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5901⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5900⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammAllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := ammAllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5901⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5900⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammAllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (ammAllowanceOwnerWord I)
      (UInt256.land (ammAllowanceOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5470_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammAllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (ammAllowanceSpenderWord I)
      (UInt256.land (ammAllowanceSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammAllowanceX_dec5470_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammAllowanceSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some allowanceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [])
    (post := [approveTransition, balanceOfTransition, burnTransition, mintTransition,
      swap0Transition, swap1Transition, totalSupplyTransition, transferTransition,
      transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammAllowanceSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

/-- The allowance wrapper, entered at PC 486, refines its Solm transition. -/
theorem ammAllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨486⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammAllowanceSelector_size hsel
  have hd := ammDispatch_allowance (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (ammAllowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (ammAllowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := ammDecode_allowance_ok (I := I) hsz68 hbig
            hcanonOwner hcanonSpender
          have hword : ammAllowanceWord σ_evm I = ammAllowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (ammAllowanceSlotFromCalldata I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (ammAllowanceStore I) allowanceTransition.body
                (.returned { contract := contract, locals := ammAllowanceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.int (Int.ofNat (ammAllowanceWord σ_solm I).toNat))])) := by
            simpa [ammAllowanceWord, ammAllowanceSlotFromCalldata,
              initState, Solm.EVM.storageLoad, State.lookupAccount] using
              ammAllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (ammX_allowance (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [← hword])
              hAccounts
              (returnEquiv_of_encode (by
                simpa [uint256, uint256Int] using
                  (uint256ReturnEncoding (ammAllowanceWord σ_evm I))))
        · have hdec := ammDecode_allowance_none_noncanon_spender
            (I := I) hsz68 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (ammAllowanceSpenderWord I)
              (UInt256.land (ammAllowanceSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
          exact (ammAllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := ammDecode_allowance_none_noncanon_owner
          (I := I) hsz68 hbig hcanonOwner
        have hnc : UInt256.eq (ammAllowanceOwnerWord I)
            (UInt256.land (ammAllowanceOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonOwner (solcAddrCanonical_of_clean he))
        exact (ammAllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ammDecode_allowance_none_huge (I := I) hbigge
      exact (ammAllowanceX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := ammDecode_allowance_none_short (I := I) hsz4 hshort
    exact (ammAllowanceX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm
