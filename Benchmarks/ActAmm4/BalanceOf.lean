import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

abbrev amm4BalanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev amm4BalanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4BalanceOfOwnerWord I).toNat)

abbrev amm4BalanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (amm4BalanceOfOwnerValue I)

def amm4BalanceOfSlotFromCalldata (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (amm4BalanceOfOwnerWord I).toNat))

theorem amm4BalanceOfSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (amm4BalanceOfOwnerWord I) =
      amm4BalanceOfSlotFromCalldata I := by
  unfold amm4BalanceOfSlotFromCalldata balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def amm4BalanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (amm4BalanceOfSlotFromCalldata I) ⟨0⟩)

def amm4BalanceOfEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (amm4BalanceOfOwnerWord I).toNat))] }

theorem amm4Decode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata =
        some (amm4BalanceOfStore I) := by
  show decodeCalldata ["owner"] [addr] I.calldata = _
  simpa [amm4BalanceOfStore, amm4BalanceOfOwnerValue, amm4BalanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "owner") hsz36 hbig hcanon

theorem amm4Decode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "owner") hsz4 hshort

theorem amm4Decode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr, amm4BalanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "owner") hsz36 hbig hnc

theorem amm4Decode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "owner") hbig

theorem amm4BalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4BalanceOfStore I)
      balanceOfTransition.body
      (.returned { contract := contract, locals := amm4BalanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (amm4BalanceOfSlotFromCalldata I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config
          { contract := contract, locals := amm4BalanceOfStore I } evm
          (balanceOfRef (.var "owner")) = .ok (amm4BalanceOfEvaledRef I) := by
        simp [evalStorageRef, evalStorageRefStep, balanceOfRef, amm4BalanceOfStore,
          amm4BalanceOfOwnerValue, amm4BalanceOfEvaledRef, valueToKey?,
          EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
      have hty : storageTypeAt? contract.storage (amm4BalanceOfEvaledRef I) =
          some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, contract, storageDecls, amm4BalanceOfEvaledRef,
          uint256St, storageTypeStep?]
      have hloc : config.storage.layout (amm4BalanceOfEvaledRef I) =
          fun _ => some (wordLoc (amm4BalanceOfSlotFromCalldata I)) := by
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [amm4BalanceOfStore, balanceOfRef])
        (her := her) (hty := hty) (hloc := hloc)]
      simp [amm4BalanceOfSlotFromCalldata, amm4StorageLocLoad_uint256])

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4961⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨372⟩, ⟨377⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨377⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨372⟩, swap2, swap1, push2 ⟨4961⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_dec5470 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨4995⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨372⟩, ⟨377⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨4995⟩, dup5, dup3, dup6, add, push2 ⟨4657⟩,
    jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_dec5870 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4995⟩
      [amm4BalanceOfOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨372⟩, ⟨377⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_dec5470 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  exact RD.amm4DecodeAddrOk rd hcanon (by jump_dest) (by evm_ov)

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3429⟩
      [amm4BalanceOfOwnerWord I, ⟨377⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_dec5870 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨3429⟩, jump (by jump_dest) ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_getter {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨377⟩
      [amm4BalanceOfWord σ I, ⟨377⟩, sel]
      (solcMappingHashMem ⟨1⟩ (amm4BalanceOfOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3429⟩ := amm4BalanceOfX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have hslot : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcMappingHashMem ⟨1⟩ (amm4BalanceOfOwnerWord I)).readWithPadding 0 64))) =
      amm4BalanceOfSlotFromCalldata I := by
    rw [solcMappingKeccakSlot, amm4BalanceOfSlot_eq_solc I hcanon]
  have rd3447 := evm_run rd3429 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (solcMappingBaseSlotMem ⟨1⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (solcMappingHashMem ⟨1⟩ (amm4BalanceOfOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (amm4BalanceOfSlotFromCalldata I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap1, pop ]
  obtain ⟨_, _, rd3448⟩ := rd3447.sload (by native_decide) (by evm_ov)
  have rd377 := evm_run rd3448 with [dup2, jump (by jump_dest)]
  exact ⟨_, _, by simpa [amm4BalanceOfWord, amm4BalanceOfSlotFromCalldata] using rd377⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4X_balanceOf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (amm4BalanceOfWord σ I)) := by
  obtain ⟨_, _, rd377⟩ := amm4BalanceOfX_getter (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd4856 := evm_run rd377 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (solcMappingHashMem_mload64 ⟨1⟩ (amm4BalanceOfOwnerWord I))
      (by decide) (by evm_ov),
    push2 ⟨390⟩, swap2, swap1, push2 ⟨4856⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd390⟩ := RD.amm4RoutineEncodeUint256FromMem
    (memout := amm4WordReturnMem
      (solcMappingHashMem ⟨1⟩ (amm4BalanceOfOwnerWord I)) (amm4BalanceOfWord σ I))
    rd4856 (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd390 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (amm4WordReturnMem_mload64_of_size96 (amm4BalanceOfWord σ I)
        (solcMappingHashMem_size ⟨1⟩ (amm4BalanceOfOwnerWord I))
        (solcMappingHashMem_read64 ⟨1⟩ (amm4BalanceOfOwnerWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (amm4BalanceOfWord σ I)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact amm4WordReturnMem_read128_of_size96 (amm4BalanceOfWord σ I)
          (solcMappingHashMem_size ⟨1⟩ (amm4BalanceOfOwnerWord I)))
      (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨4981⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4982⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨4981⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem amm4BalanceOfX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (amm4BalanceOfOwnerWord I)
      (UInt256.land (amm4BalanceOfOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨351⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4BalanceOfX_dec5470 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4BalanceOfSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition])
    (post := [burnTransition, mintTransition, swapTransition, totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, amm4BalanceOfSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, amm4AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, amm4ApproveSelectorBytes, hcd]; decide

/-- The balanceOf wrapper, entered at PC 351, refines its Solm transition. -/
theorem amm4BalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨351⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4BalanceOfSelector_size hsel
  have hd := amm4Dispatch_balanceOf (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (amm4BalanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hdec := amm4Decode_balanceOf_ok (I := I) hsz36 hbig hcanon
        have hword : amm4BalanceOfWord σ_evm I = amm4BalanceOfWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (amm4BalanceOfSlotFromCalldata I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (amm4BalanceOfStore I) balanceOfTransition.body
              (.returned { contract := contract, locals := amm4BalanceOfStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some [(.int (Int.ofNat (amm4BalanceOfWord σ_solm I).toNat))])) := by
          simpa [amm4BalanceOfWord, amm4BalanceOfSlotFromCalldata,
            initState, Solm.EVM.storageLoad, State.lookupAccount] using
            amm4BalanceOfBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
        exact (amm4X_balanceOf (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody
            (by rw [← hword]) hAccounts
            (returnEquiv_of_encode (by
              simpa [uint256, uint256Int] using
                (uint256ReturnEncoding (amm4BalanceOfWord σ_evm I))))
      · have hdec := amm4Decode_balanceOf_none_noncanon (I := I)
          hsz36 hbig hcanon
        have hnc : UInt256.eq (amm4BalanceOfOwnerWord I)
            (UInt256.land (amm4BalanceOfOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (amm4BalanceOfX_noncanon (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := amm4Decode_balanceOf_none_huge (I := I) hbigge
      exact (amm4BalanceOfX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := amm4Decode_balanceOf_none_short (I := I) hsz4 hshort
    exact (amm4BalanceOfX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm4
