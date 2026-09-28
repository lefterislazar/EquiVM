import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Reasoning.SolmBody
import Benchmarks.ActAmm.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

abbrev ammBalanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev ammBalanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammBalanceOfOwnerWord I).toNat)

abbrev ammBalanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (ammBalanceOfOwnerValue I)

def ammBalanceOfSlotFromCalldata (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (ammBalanceOfOwnerWord I).toNat))

theorem ammBalanceOfSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (ammBalanceOfOwnerWord I) =
      ammBalanceOfSlotFromCalldata I := by
  unfold ammBalanceOfSlotFromCalldata balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

def ammBalanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (ammBalanceOfSlotFromCalldata I) ⟨0⟩)

def ammBalanceOfEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (ammBalanceOfOwnerWord I).toNat))] }

theorem ammDecode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata =
        some (ammBalanceOfStore I) := by
  show decodeCalldata ["owner"] [addr] I.calldata = _
  simpa [ammBalanceOfStore, ammBalanceOfOwnerValue, ammBalanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "owner") hsz36 hbig hcanon

theorem ammDecode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "owner") hsz4 hshort

theorem ammDecode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr, ammBalanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "owner") hsz36 hbig hnc

theorem ammDecode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "owner") hbig

theorem ammBalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammBalanceOfStore I)
      balanceOfTransition.body
      (.returned { contract := contract, locals := ammBalanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (ammBalanceOfSlotFromCalldata I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config
          { contract := contract, locals := ammBalanceOfStore I } evm
          (balanceOfRef (.var "owner")) = .ok (ammBalanceOfEvaledRef I) := by
        simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ammBalanceOfStore,
          ammBalanceOfOwnerValue, ammBalanceOfEvaledRef, valueToKey?,
          EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
      have hty : storageTypeAt? contract.storage (ammBalanceOfEvaledRef I) =
          some (.elem (.int uint256Int)) := by
        simp [storageTypeAt?, contract, storageDecls, ammBalanceOfEvaledRef,
          uint256St, storageTypeStep?]
      have hloc : config.storage.layout (ammBalanceOfEvaledRef I) =
          fun _ => some (wordLoc (ammBalanceOfSlotFromCalldata I)) := by
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [ammBalanceOfStore, balanceOfRef])
        (her := her) (hty := hty) (hloc := hloc)]
      simp [ammBalanceOfSlotFromCalldata, ammStorageLocLoad_uint256])

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5836⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨411⟩, ⟨416⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨416⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨411⟩, swap2, swap1, push2 ⟨5836⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_dec5470 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5870⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨411⟩, ⟨416⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5870⟩, dup5, dup3, dup6, add, push2 ⟨5470⟩,
    jump (by jump_dest) ]⟩

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_dec5870 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5870⟩
      [ammBalanceOfOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨411⟩, ⟨416⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_dec5470 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  exact RD.ammDecodeAddrOk rd hcanon (by jump_dest) (by evm_ov)

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4242⟩
      [ammBalanceOfOwnerWord I, ⟨416⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_dec5870 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, push2 ⟨4242⟩, jump (by jump_dest) ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_getter {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨416⟩
      [ammBalanceOfWord σ I, ⟨416⟩, sel]
      (solcMappingHashMem ⟨1⟩ (ammBalanceOfOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4242⟩ := ammBalanceOfX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have hslot : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcMappingHashMem ⟨1⟩ (ammBalanceOfOwnerWord I)).readWithPadding 0 64))) =
      ammBalanceOfSlotFromCalldata I := by
    rw [solcMappingKeccakSlot, ammBalanceOfSlot_eq_solc I hcanon]
  have rd4260 := evm_run rd4242 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (solcMappingBaseSlotMem ⟨1⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (solcMappingHashMem ⟨1⟩ (ammBalanceOfOwnerWord I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (ammBalanceOfSlotFromCalldata I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap1, pop ]
  obtain ⟨_, _, rd4261⟩ := rd4260.sload (by native_decide) (by evm_ov)
  have rd416 := evm_run rd4261 with [dup2, jump (by jump_dest)]
  exact ⟨_, _, by simpa [ammBalanceOfWord, ammBalanceOfSlotFromCalldata] using rd416⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammX_balanceOf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (ammBalanceOfWord σ I)) := by
  obtain ⟨_, _, rd416⟩ := ammBalanceOfX_getter (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have rd5731 := evm_run rd416 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (solcMappingHashMem_mload64 ⟨1⟩ (ammBalanceOfOwnerWord I))
      (by decide) (by evm_ov),
    push2 ⟨429⟩, swap2, swap1, push2 ⟨5731⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd429⟩ := RD.ammRoutineEncodeUint256FromMem
    (memout := ammWordReturnMem
      (solcMappingHashMem ⟨1⟩ (ammBalanceOfOwnerWord I)) (ammBalanceOfWord σ I))
    rd5731 (by rfl) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd429 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (ammWordReturnMem_mload64_of_size96 (ammBalanceOfWord σ I)
        (solcMappingHashMem_size ⟨1⟩ (ammBalanceOfOwnerWord I))
        (solcMappingHashMem_read64 ⟨1⟩ (ammBalanceOfOwnerWord I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (ammBalanceOfWord σ I)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact ammWordReturnMem_read128_of_size96 (ammBalanceOfWord σ I)
          (solcMappingHashMem_size ⟨1⟩ (ammBalanceOfOwnerWord I)))
      (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨5856⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5857⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨5856⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

set_option maxRecDepth 2000000 in
theorem ammBalanceOfX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (ammBalanceOfOwnerWord I)
      (UInt256.land (ammBalanceOfOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨390⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammBalanceOfX_dec5470 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammBalanceOfSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition])
    (post := [burnTransition, mintTransition, swap0Transition,
      swap1Transition, totalSupplyTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, ammBalanceOfSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, ammAllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, ammApproveSelectorBytes, hcd]; decide

/-- The balanceOf wrapper, entered at PC 390, refines its Solm transition. -/
theorem ammBalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨390⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammBalanceOfSelector_size hsel
  have hd := ammDispatch_balanceOf (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (ammBalanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hdec := ammDecode_balanceOf_ok (I := I) hsz36 hbig hcanon
        have hword : ammBalanceOfWord σ_evm I = ammBalanceOfWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (ammBalanceOfSlotFromCalldata I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (ammBalanceOfStore I) balanceOfTransition.body
              (.returned { contract := contract, locals := ammBalanceOfStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some [(.int (Int.ofNat (ammBalanceOfWord σ_solm I).toNat))])) := by
          simpa [ammBalanceOfWord, ammBalanceOfSlotFromCalldata,
            initState, Solm.EVM.storageLoad, State.lookupAccount] using
            ammBalanceOfBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
        exact (ammX_balanceOf (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody
            (by rw [← hword]) hAccounts
            (returnEquiv_of_encode (by
              simpa [uint256, uint256Int] using
                (uint256ReturnEncoding (ammBalanceOfWord σ_evm I))))
      · have hdec := ammDecode_balanceOf_none_noncanon (I := I)
          hsz36 hbig hcanon
        have hnc : UInt256.eq (ammBalanceOfOwnerWord I)
            (UInt256.land (ammBalanceOfOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ammBalanceOfX_noncanon (g := Sat256.ofUInt256 g)
          hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ammDecode_balanceOf_none_huge (I := I) hbigge
      exact (ammBalanceOfX_hugearg (g := Sat256.ofUInt256 g)
        hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := ammDecode_balanceOf_none_short (I := I) hsz4 hshort
    exact (ammBalanceOfX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm
