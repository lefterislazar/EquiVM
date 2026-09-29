import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4AllowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4AllowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev amm4AllowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4AllowanceOwnerWord I).toNat)

abbrev amm4AllowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4AllowanceSpenderWord I).toNat)

abbrev amm4AllowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (amm4AllowanceOwnerValue I)).insert
    "spender" (amm4AllowanceSpenderValue I)

def amm4AllowanceSlotFromCalldata (I : ExecutionEnv) : UInt256 :=
  allowanceSlot
    (.address (AccountAddress.ofNat (amm4AllowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (amm4AllowanceSpenderWord I).toNat))

theorem amm4AllowanceSlot_eq_solc (I : ExecutionEnv)
    (howner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hspender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (amm4AllowanceOwnerWord I))
      (amm4AllowanceSpenderWord I) = amm4AllowanceSlotFromCalldata I := by
  unfold amm4AllowanceSlotFromCalldata allowanceSlot allowanceOwnerSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ howner,
    keyValueToWord_address_of_canonical _ hspender]

def amm4AllowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (amm4AllowanceSlotFromCalldata I) ⟨0⟩)

def amm4AllowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address (AccountAddress.ofNat (amm4AllowanceOwnerWord I).toNat)),
      .mindex (.address (AccountAddress.ofNat (amm4AllowanceSpenderWord I).toNat))] }

theorem amm4Decode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata =
        some (amm4AllowanceStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [amm4AllowanceStore, amm4AllowanceOwnerValue, amm4AllowanceSpenderValue,
    amm4AllowanceOwnerWord, amm4AllowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata)
      (x := "owner") (y := "spender") hsz68 hbig hcanonOwner hcanonSpender

theorem amm4Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem amm4Decode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, amm4AllowanceOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem amm4Decode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, amm4AllowanceOwnerWord, amm4AllowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem amm4Decode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

theorem amm4AllowanceStore_owner (I : ExecutionEnv) :
    (amm4AllowanceStore I).get? "owner" = some (amm4AllowanceOwnerValue I) := by
  rw [amm4AllowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem amm4AllowanceStore_spender (I : ExecutionEnv) :
    (amm4AllowanceStore I).get? "spender" = some (amm4AllowanceSpenderValue I) := by
  rw [amm4AllowanceStore, store_get_self]

theorem amm4AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4AllowanceStore I)
      allowanceTransition.body
      (.returned { contract := contract, locals := amm4AllowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (amm4AllowanceSlotFromCalldata I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config
          { contract := contract, locals := amm4AllowanceStore I } evm
          (allowanceRef (.var "owner") (.var "spender")) =
            .ok (amm4AllowanceEvaledRef I) := by
        simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
          evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
          amm4AllowanceEvaledRef, amm4AllowanceOwnerValue, amm4AllowanceSpenderValue,
          amm4AllowanceStore_owner, amm4AllowanceStore_spender]
      have hty : storageTypeAt? contract.storage (amm4AllowanceEvaledRef I) =
          some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, contract, storageDecls, amm4AllowanceEvaledRef,
          uint256St, storageTypeStep?]
      have hloc : config.storage.layout (amm4AllowanceEvaledRef I) =
          fun _ => some (wordLoc (amm4AllowanceSlotFromCalldata I)) := by
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by
          rw [amm4AllowanceStore, store_get_ne _ _ (by decide),
            store_get_ne _ _ (by decide)]
          simp)
        (her := her) (hty := hty) (hloc := hloc)]
      simp [amm4AllowanceSlotFromCalldata, amm4StorageLocLoad_uint256])

theorem amm4AllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5146⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨468⟩, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨473⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨468⟩, swap2, swap1, push2 ⟨5146⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4AllowanceX_dec5470_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5181⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨468⟩, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5168⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5181⟩, dup6, dup3, dup7, add, push2 ⟨4657⟩,
    jump (by jump_dest) ]⟩

theorem amm4AllowanceX_dec5914 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5181⟩
      [amm4AllowanceOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨468⟩, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5470_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.amm4DecodeAddrOk rd hcanonOwner (by jump_dest) (by evm_ov)

theorem amm4AllowanceX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5198⟩, ⟨32⟩, ⟨0⟩,
        amm4AllowanceOwnerWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨468⟩, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5914 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5198⟩, dup6, dup3, dup7,
    add, push2 ⟨4657⟩, jump (by jump_dest) ]⟩

theorem amm4AllowanceX_dec5931 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5198⟩
      [amm4AllowanceSpenderWord I, ⟨32⟩, ⟨0⟩, amm4AllowanceOwnerWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨468⟩, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5470_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.amm4DecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem amm4AllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3737⟩
      [amm4AllowanceSpenderWord I, amm4AllowanceOwnerWord I, ⟨473⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5931 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨3737⟩, jump (by jump_dest) ]⟩

theorem amm4X_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (amm4AllowanceWord σ I)) := by
  obtain ⟨_, _, rd3737⟩ := amm4AllowanceX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  have hslot : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcNestedMappingHashMem ⟨2⟩ (amm4AllowanceOwnerWord I)
        (amm4AllowanceSpenderWord I)).readWithPadding 0 64))) =
      amm4AllowanceSlotFromCalldata I := by
    rw [solcNestedMappingKeccakSlot,
      amm4AllowanceSlot_eq_solc I hcanonOwner hcanonSpender]
  have rd3766 := evm_run rd3737 with [
    jumpdest, push1 ⟨2⟩, push1 ⟨32⟩,
    raw mstore 0 (solcMappingBaseSlotMem ⟨2⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (solcMappingHashMem ⟨2⟩ (amm4AllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (solcMappingSlot ⟨2⟩ (amm4AllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcMappingKeccakSlot ⟨2⟩ (amm4AllowanceOwnerWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (solcNestedMappingOuterBaseMem ⟨2⟩ (amm4AllowanceOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (solcNestedMappingHashMem ⟨2⟩ (amm4AllowanceOwnerWord I)
      (amm4AllowanceSpenderWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (amm4AllowanceSlotFromCalldata I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap2, pop, pop ]
  obtain ⟨_, _, rd3767⟩ := rd3766.sload (by native_decide) (by evm_ov)
  have rd473 := evm_run rd3767 with [dup2, jump (by jump_dest)]
  have rd4856 := evm_run rd473 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (solcNestedMappingHashMem_mload64 ⟨2⟩
        (amm4AllowanceOwnerWord I) (amm4AllowanceSpenderWord I))
      (by decide) (by evm_ov),
    push2 ⟨486⟩, swap2, swap1, push2 ⟨4856⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd486⟩ := RD.amm4RoutineEncodeUint256FromMem
    (memout := amm4WordReturnMem
      (solcNestedMappingHashMem ⟨2⟩ (amm4AllowanceOwnerWord I)
        (amm4AllowanceSpenderWord I)) (amm4AllowanceWord σ I))
    rd4856 (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd486 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (amm4WordReturnMem_mload64_of_size96 (amm4AllowanceWord σ I)
        (solcNestedMappingHashMem_size ⟨2⟩
          (amm4AllowanceOwnerWord I) (amm4AllowanceSpenderWord I))
        (solcNestedMappingHashMem_read64 ⟨2⟩
          (amm4AllowanceOwnerWord I) (amm4AllowanceSpenderWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (amm4AllowanceWord σ I)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact amm4WordReturnMem_read128_of_size96 (amm4AllowanceWord σ I)
          (solcNestedMappingHashMem_size ⟨2⟩
            (amm4AllowanceOwnerWord I) (amm4AllowanceSpenderWord I)))
      (by evm_ov) ]

theorem amm4AllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5168⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5167⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4AllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5168⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5167⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4AllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (amm4AllowanceOwnerWord I)
      (UInt256.land (amm4AllowanceOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5470_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4AllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (amm4AllowanceSpenderWord I)
      (UInt256.land (amm4AllowanceSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨447⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4AllowanceX_dec5470_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4AllowanceSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some allowanceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [])
    (post := [approveTransition, balanceOfTransition, burnTransition, mintTransition,
      swapTransition, totalSupplyTransition, transferTransition,
      transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4AllowanceSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

/-- The allowance wrapper, entered at PC 447, refines its Solm transition. -/
theorem amm4AllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨447⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4AllowanceSelector_size hsel
  have hd := amm4Dispatch_allowance (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (amm4AllowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (amm4AllowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := amm4Decode_allowance_ok (I := I) hsz68 hbig
            hcanonOwner hcanonSpender
          have hword : amm4AllowanceWord σ_evm I = amm4AllowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (amm4AllowanceSlotFromCalldata I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (amm4AllowanceStore I) allowanceTransition.body
                (.returned { contract := contract, locals := amm4AllowanceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [(.int (Int.ofNat (amm4AllowanceWord σ_solm I).toNat))])) := by
            simpa [amm4AllowanceWord, amm4AllowanceSlotFromCalldata,
              initState, Solm.EVM.storageLoad, State.lookupAccount] using
              amm4AllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (amm4X_allowance (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [← hword])
              hAccounts
              (returnEquiv_of_encode (by
                simpa [uint256, uint256Int] using
                  (uint256ReturnEncoding (amm4AllowanceWord σ_evm I))))
        · have hdec := amm4Decode_allowance_none_noncanon_spender
            (I := I) hsz68 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (amm4AllowanceSpenderWord I)
              (UInt256.land (amm4AllowanceSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
          exact (amm4AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := amm4Decode_allowance_none_noncanon_owner
          (I := I) hsz68 hbig hcanonOwner
        have hnc : UInt256.eq (amm4AllowanceOwnerWord I)
            (UInt256.land (amm4AllowanceOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonOwner (solcAddrCanonical_of_clean he))
        exact (amm4AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := amm4Decode_allowance_none_huge (I := I) hbigge
      exact (amm4AllowanceX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := amm4Decode_allowance_none_short (I := I) hsz4 hshort
    exact (amm4AllowanceX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm4
