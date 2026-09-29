import Benchmarks.ActAmm4.MintArithmeticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintEvalToken0 {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "token0" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage token0Ref) =
        .ok (.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
            solcAddrMask))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := token0Ref) (er := ({ base := "token0", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask).toNat))
    hnone
    (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by simpa [addrLoc] using storageLocLoad_address_offset0 evm ⟨3⟩)

theorem amm4MintEvalToken0_initState {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store} (hnone : locals.get? "token0" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage token0Ref) =
        .ok (.address (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))) := by
  simpa [amm4MintToken0Word, solcSlotWord, initState, Solm.EVM.storageLoad]
    using (amm4MintEvalToken0 (evm := initState cA gh bl σ σ₀ g A I) hnone)

theorem amm4MintEvalToken1 {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "token1" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage token1Ref) =
        .ok (.address (AccountAddress.ofUInt256
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := token1Ref) (er := ({ base := "token1", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨4⟩)
    (value := .address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask).toNat))
    hnone
    (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by simpa [addrLoc] using storageLocLoad_address_offset0 evm ⟨4⟩)

theorem amm4MintEvalBalanceArgs {evm : EVM.State} {locals : Store} :
    evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind, bind, pure]

theorem amm4MintEvalSupply {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "totalSupply" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := totalSupplyRef)
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨0⟩)
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))
    hnone
    (by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa using amm4StorageLocLoad_uint256 evm ⟨0⟩)

theorem amm4MintEvalReserve0 {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "reserve0" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage reserve0Ref) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat))
    hnone
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa using amm4StorageLocLoad_uint256 evm ⟨5⟩)

theorem amm4MintEvalReserve1 {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "reserve1" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage reserve1Ref) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨6⟩)
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))
    hnone
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa using amm4StorageLocLoad_uint256 evm ⟨6⟩)

theorem amm4MintEvalSupplyGuard_true {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "totalSupply" = none)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.storage totalSupplyRef) (.intLit 0)) = .ok (.bool true) := by
  have hs := amm4MintEvalSupply (evm := evm) hnone
  have hn : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
    intro hz
    exact hnonzero (uint256_toNat_eq_zero hz)
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hs, hn]

theorem amm4MintEvalSupplyGuard_false {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "totalSupply" = none)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.storage totalSupplyRef) (.intLit 0)) = .ok (.bool false) := by
  have hs := amm4MintEvalSupply (evm := evm) hnone
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hs, hzero]

theorem amm4MintSourceZeroSupply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hguard := amm4MintEvalSupplyGuard_false (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore]) hzero
  have hblock : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem amm4MintSourceToken0CallFailed (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (false, evm', out) false) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hguard := amm4MintEvalSupplyGuard_true (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore]) hnonzero
  have hreceiver := amm4MintEvalToken0 (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm) (locals := amm4MintStore I)
  have hblock : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem amm4MintDecodeBalance_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "balanceOf" o = none := by
  have hlen : o.toList.length = o.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((o.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hdec :
      ABI.decodeReturnValueWithMode? DecodeMode.modern uint256 o = none := by
    unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue? ABI.decodeReturnValues?
    have hguard : ¬ (2 : Nat) ^ 255 ≤ o.toList.length := by rw [hlen]; omega
    simp only [hguard, and_false, ↓reduceIte]
    rw [abiTupleHeadSize_scalarWords_eq (types := [uint256]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [uint256]) (bytes := o.toList) (cursor := 0)
      (total := 32 * [uint256].length) (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    rw [show uint256 = abiUInt256 from rfl]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.modern)
      (bytes := o.toList) (start := 0) htake0n]
    rfl
  simp [config, externalABI, decodeReturn?, hdec]

theorem amm4MintDecodeBalance_ok {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < 2 ^ 255) :
    config.externalABI.decode? "balanceOf" o =
      some [.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))] := by
  have hlen : o.toList.length = o.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((o.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := o)
  have hdec : ABI.decodeReturnValueWithMode? DecodeMode.modern uint256 o =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue? ABI.decodeReturnValues?
    have hguard : ¬ (2 : Nat) ^ 255 ≤ o.toList.length := by rw [hlen]; omega
    simp only [hguard, and_false, ↓reduceIte]
    rw [abiTupleHeadSize_scalarWords_eq (types := [uint256]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [uint256]) (bytes := o.toList) (cursor := 0)
      (total := 32 * [uint256].length) (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    rw [show uint256 = abiUInt256 from rfl]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.modern)
      (bytes := o.toList) (start := 0) htake0]
    simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]
  simp [config, externalABI, decodeReturn?, hdec]

def amm4MintAfterBalance0Store (I : ExecutionEnv) (out : ByteArray) : Store :=
  (amm4MintStore I).insert "balance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

theorem amm4MintSourceToken0CallOk (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm', out) false) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0"])
      (.ok { contract := contract, locals := amm4MintAfterBalance0Store I out } evm') := by
  have hguard := amm4MintEvalSupplyGuard_true (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore]) hnonzero
  have hreceiver := amm4MintEvalToken0 (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm) (locals := amm4MintStore I)
  have hdec := amm4MintDecodeBalance_ok hlo (by omega : out.size < 2 ^ 255)
  simp only [nonpayable, tokenBalance, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  simpa [amm4MintAfterBalance0Store, collapseReturns] using
    (ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
      ExecBlock.nil)

theorem amm4MintSourceToken0DecodeShort (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hshort : out.size < 32)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm', out) false) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hguard := amm4MintEvalSupplyGuard_true (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore]) hnonzero
  have hreceiver := amm4MintEvalToken0 (evm := evm)
    (locals := amm4MintStore I) (by simp [amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm) (locals := amm4MintStore I)
  have hdec := amm4MintDecodeBalance_short hshort
  have hblock : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem amm4MintSourceToken1CallFailed (evm evm1 evm2 : EVM.State)
    (I : ExecutionEnv) (o1 o2 : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hlo : 32 ≤ o1.size) (hbound : o1.size < 2 ^ 138)
    (hcall0 : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm1, o1) false)
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (false, evm2, o2) false) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hprefix := amm4MintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo hbound hcall0
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
    (by simp [amm4MintAfterBalance0Store, amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterBalance0Store I o1 }
      evm1 (tokenBalance (.storage token1Ref) "balance1" ::
        mintTransition.body.drop 4) .reverted := by
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall1)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, List.drop,
      List.cons_append, List.nil_append] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintSourceToken1DecodeShort (evm evm1 evm2 : EVM.State)
    (I : ExecutionEnv) (o1 o2 : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hlo : 32 ≤ o1.size) (hbound : o1.size < 2 ^ 138)
    (hshort : o2.size < 32)
    (hcall0 : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm1, o1) false)
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, o2) false) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hprefix := amm4MintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo hbound hcall0
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
    (by simp [amm4MintAfterBalance0Store, amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
  have hdec := amm4MintDecodeBalance_short hshort
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterBalance0Store I o1 }
      evm1 (tokenBalance (.storage token1Ref) "balance1" ::
        mintTransition.body.drop 4) .reverted := by
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall1 hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, List.drop,
      List.cons_append, List.nil_append] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def amm4MintAfterBalance1Store (I : ExecutionEnv) (o1 o2 : ByteArray) : Store :=
  (amm4MintAfterBalance0Store I o1).insert "balance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32))))

theorem amm4MintSourceToken1CallOk (evm evm1 evm2 : EVM.State)
    (I : ExecutionEnv) (o1 o2 : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (hcall0 : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm1, o1) false)
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, o2) false) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 } evm2) := by
  have hprefix := amm4MintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo1 hbound1 hcall0
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
    (by simp [amm4MintAfterBalance0Store, amm4MintStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4MintAfterBalance0Store I o1)
  have hdec := amm4MintDecodeBalance_ok hlo2 (by omega : o2.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterBalance0Store I o1 }
      evm1 [tokenBalance (.storage token1Ref) "balance1"]
      (.ok { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 } evm2) := by
    simpa [amm4MintAfterBalance1Store, collapseReturns, tokenBalance] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver (by simp [evalExpr?, pure]) hargs hcall1 hdec)
        ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem amm4MintEvalBalance0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} :
    evalExpr? config { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
  have hget : (amm4MintAfterBalance1Store I o1 o2).get? "balance0" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
    unfold amm4MintAfterBalance1Store
    rw [store_get_ne (amm4MintAfterBalance0Store I o1) (k := "balance1")
      (a := "balance0") _ (by decide)]
    simp [amm4MintAfterBalance0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem amm4MintEvalBalance1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} :
    evalExpr? config { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
  simp [amm4MintAfterBalance1Store, evalExpr?, EvalResult.ofOption]

theorem amm4MintEvalAmount0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray}
    (hlo : 32 ≤ o1.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (o1.extract 0 32)) :
    evalExpr? config { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm
      (checkedSub (.var "balance0") (.storage reserve0Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat))) := by
  exact amm4EvalCheckedSub_ok amm4MintEvalBalance0
    (amm4MintEvalReserve0 (by simp [amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hle
    (fromByteArrayBigEndian_extract0_32_lt hlo)

theorem amm4MintEvalAmount0_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray}
    (hunder : fromByteArrayBigEndian (o1.extract 0 32) <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm
      (checkedSub (.var "balance0") (.storage reserve0Ref)) = .revert := by
  exact amm4EvalCheckedSub_revert amm4MintEvalBalance0
    (amm4MintEvalReserve0 (by simp [amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hunder

def amm4MintAfterAmount0Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 : UInt256) : Store :=
  (amm4MintAfterBalance1Store I o1 o2).insert "amount0"
    (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat)))

theorem amm4MintSourceAmount0Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 } evm2))
    (hlo : 32 ≤ o1.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (o1.extract 0 32)) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := (amm4MintAfterAmount0Store I o1 o2
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have heval := amm4MintEvalAmount0 (I := I) (o1 := o1) (o2 := o2) hlo hle
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm2 [.letDecl "amount0" (some uint256)
        (checkedSub (.var "balance0") (.storage reserve0Ref))]
      (.ok { contract := contract, locals := (amm4MintAfterAmount0Store I o1 o2
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simpa [amm4MintAfterAmount0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem amm4MintSourceAmount0Underflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 } evm2))
    (hunder : fromByteArrayBigEndian (o1.extract 0 32) <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalAmount0_revert (I := I) (o1 := o1) (o2 := o2) hunder
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterBalance1Store I o1 o2 }
      evm2 (mintTransition.body.drop 4) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintEvalAmount1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 : UInt256}
    (hlo : 32 ≤ o2.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (o2.extract 0 32)) :
    evalExpr? config { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm
      (checkedSub (.var "balance1") (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (o2.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))) := by
  have hget : (amm4MintAfterAmount0Store I o1 o2 r0).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    unfold amm4MintAfterAmount0Store
    rw [store_get_ne (amm4MintAfterBalance1Store I o1 o2) (k := "amount0")
      (a := "balance1") _ (by decide)]
    simp [amm4MintAfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  have hbal : evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    simp [evalExpr?, hget, EvalResult.ofOption]
  exact amm4EvalCheckedSub_ok hbal
    (amm4MintEvalReserve1 (by simp [amm4MintAfterAmount0Store,
      amm4MintAfterBalance1Store, amm4MintAfterBalance0Store, amm4MintStore]))
    hle (fromByteArrayBigEndian_extract0_32_lt hlo)

theorem amm4MintEvalAmount1_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 : UInt256}
    (hunder : fromByteArrayBigEndian (o2.extract 0 32) <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm
      (checkedSub (.var "balance1") (.storage reserve1Ref)) = .revert := by
  have hget : (amm4MintAfterAmount0Store I o1 o2 r0).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    unfold amm4MintAfterAmount0Store
    rw [store_get_ne (amm4MintAfterBalance1Store I o1 o2) (k := "amount0")
      (a := "balance1") _ (by decide)]
    simp [amm4MintAfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  have hbal : evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    simp [evalExpr?, hget, EvalResult.ofOption]
  exact amm4EvalCheckedSub_revert hbal
    (amm4MintEvalReserve1 (by simp [amm4MintAfterAmount0Store,
      amm4MintAfterBalance1Store, amm4MintAfterBalance0Store, amm4MintStore])) hunder

def amm4MintAfterAmount1Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 : UInt256) : Store :=
  (amm4MintAfterAmount0Store I o1 o2 r0).insert "amount1"
    (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat)))

theorem amm4MintSourceAmount1Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 } evm2))
    (hlo : 32 ≤ o2.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (o2.extract 0 32)) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals :=
        (amm4MintAfterAmount1Store I o1 o2 r0
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have heval := amm4MintEvalAmount1 (I := I) (o1 := o1) (o2 := o2) (r0 := r0)
    hlo hle
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm2 [.letDecl "amount1" (some uint256)
        (checkedSub (.var "balance1") (.storage reserve1Ref))]
      (.ok { contract := contract, locals :=
        (amm4MintAfterAmount1Store I o1 o2 r0
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simpa [amm4MintAfterAmount1Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem amm4MintSourceAmount1Underflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 } evm2))
    (hunder : fromByteArrayBigEndian (o2.extract 0 32) <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalAmount1_revert (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) hunder
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterAmount0Store I o1 o2 r0 }
      evm2 (mintTransition.body.drop 5) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintEvalAmount0Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm (.var "amount0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat))) := by
  have hget : (amm4MintAfterAmount1Store I o1 o2 r0 r1).get? "amount0" =
      some (.int (Int.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat))) := by
    unfold amm4MintAfterAmount1Store
    rw [store_get_ne (amm4MintAfterAmount0Store I o1 o2 r0) (k := "amount1")
      (a := "amount0") _ (by decide)]
    simp [amm4MintAfterAmount0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem amm4MintEvalAmount1Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm (.var "amount1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
  simp [amm4MintAfterAmount1Store, evalExpr?, EvalResult.ofOption]

theorem amm4MintEvalLiq0Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hfit : (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm (checkedMul (.var "amount0") (.storage totalSupplyRef)) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))) := by
  exact amm4EvalCheckedMul_ok amm4MintEvalAmount0Local
    (amm4MintEvalSupply (by simp [amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hfit

theorem amm4MintEvalLiq0Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm (checkedMul (.var "amount0") (.storage totalSupplyRef)) = .revert := by
  exact amm4EvalCheckedMul_revert amm4MintEvalAmount0Local
    (amm4MintEvalSupply (by simp [amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hover

def amm4MintAfterLiq0NumeratorStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply : UInt256) : Store :=
  (amm4MintAfterAmount1Store I o1 o2 r0 r1).insert "liq0Numerator"
    (.int (Int.ofNat
      ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat)))

theorem amm4MintSourceLiq0NumeratorOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 } evm2))
    (hfit : (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))])
      (.ok { contract := contract, locals := (amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
  have heval := amm4MintEvalLiq0Numerator (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) (r1 := r1) hfit
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm2 [.letDecl "liq0Numerator" (some uint256)
        (checkedMul (.var "amount0") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := (amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
    simpa [amm4MintAfterLiq0NumeratorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem amm4MintSourceLiq0NumeratorOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 } evm2))
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalLiq0Numerator_revert (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) (r1 := r1) hover
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterAmount1Store I o1 o2 r0 r1 }
      evm2 (mintTransition.body.drop 6) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintEvalLiq0NumeratorLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply : UInt256} :
    evalExpr? config { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm (.var "liq0Numerator") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat))) := by
  simp [amm4MintAfterLiq0NumeratorStore, evalExpr?, EvalResult.ofOption]

theorem amm4MintEvalReserve0AfterLiq0Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply : UInt256} :
    evalExpr? config { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  apply amm4MintEvalReserve0
  simp [amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
    amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
    amm4MintAfterBalance0Store, amm4MintStore]

def amm4MintAfterLiq0Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 : UInt256) : Store :=
  (amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply).insert "liq0"
    (.int (Int.ofNat (((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      supply.toNat) / reserve0.toNat)))

theorem amm4MintSourceLiq0Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))])
      (.ok { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply } evm2))
    (hnonzero : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))] ++
        checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref))
      (.ok { contract := contract, locals := (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have hnum := amm4MintEvalLiq0NumeratorLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  have hden := amm4MintEvalReserve0AfterLiq0Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  have hguard := amm4EvalNatNeZero_true hden hnonzero
  have hdiv := amm4EvalNatDiv_ok hnum hden hnonzero
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm2 (checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref))
      (.ok { contract := contract, locals := (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [amm4MintAfterLiq0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [List.append_assoc] using (execBlock_append hprefix htail)

theorem amm4MintSourceLiq0ReserveZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))])
      (.ok { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply } evm2))
    (hzero : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hden := amm4MintEvalReserve0AfterLiq0Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  rw [hzero] at hden
  have hguard := amm4EvalNatNeZero_false hden
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm2 (mintTransition.body.drop 7) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintEvalAmount1AfterLiq0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256} :
    evalExpr? config { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (.var "amount1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
  have hget : (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).get? "amount1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
    unfold amm4MintAfterLiq0Store amm4MintAfterLiq0NumeratorStore
    rw [store_get_ne _ (k := "liq0") (a := "amount1") _ (by decide)]
    rw [store_get_ne _ (k := "liq0Numerator") (a := "amount1") _ (by decide)]
    simp [amm4MintAfterAmount1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem amm4MintEvalLiq1Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hfit : (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    evalExpr? config { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (checkedMul (.var "amount1") (.storage totalSupplyRef)) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))) := by
  exact amm4EvalCheckedMul_ok amm4MintEvalAmount1AfterLiq0
    (amm4MintEvalSupply (by simp [amm4MintAfterLiq0Store,
      amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hfit

theorem amm4MintEvalLiq1Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (checkedMul (.var "amount1") (.storage totalSupplyRef)) = .revert := by
  exact amm4EvalCheckedMul_revert amm4MintEvalAmount1AfterLiq0
    (amm4MintEvalSupply (by simp [amm4MintAfterLiq0Store,
      amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore])) hover

def amm4MintAfterLiq1NumeratorStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 : UInt256) : Store :=
  (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).insert "liq1Numerator"
    (.int (Int.ofNat
      ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat)))

theorem amm4MintSourceLiq1NumeratorOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))] ++
        checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref))
      (.ok { contract := contract, locals :=
        (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0) } evm2))
    (hfit : (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))] ++
        checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref) ++
        [.letDecl "liq1Numerator" (some uint256)
          (checkedMul (.var "amount1") (.storage totalSupplyRef))])
      (.ok { contract := contract, locals := (amm4MintAfterLiq1NumeratorStore I o1 o2
        r0 r1 supply reserve0 (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
  have heval := amm4MintEvalLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) hfit
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 [.letDecl "liq1Numerator" (some uint256)
        (checkedMul (.var "amount1") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := (amm4MintAfterLiq1NumeratorStore I o1 o2
        r0 r1 supply reserve0 (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
    change ExecBlock config
      { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 [.letDecl "liq1Numerator" (some uint256)
        (checkedMul (.var "amount1") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := ((amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).insert "liq1Numerator"
          (.int (Int.ofNat
            ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
              (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat)))) } evm2)
    exact amm4LetDeclOne heval
  simpa only [List.append_assoc] using (execBlock_append hprefix htail)

theorem amm4MintSourceLiq1NumeratorOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref)),
         .letDecl "liq0Numerator" (some uint256)
           (checkedMul (.var "amount0") (.storage totalSupplyRef))] ++
        checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref))
      (.ok { contract := contract, locals :=
        (amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0) } evm2))
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalLiq1Numerator_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) hover
  have htail : ExecBlock config
      { contract := contract, locals := amm4MintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 (mintTransition.body.drop 9) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4MintEvalLiq1NumeratorLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm (.var "liq1Numerator") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat))) := by
  simp [amm4MintAfterLiq1NumeratorStore, evalExpr?, EvalResult.ofOption]

theorem amm4MintEvalReserve1AfterLiq1Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply amm4MintEvalReserve1
  simp [amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
    amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
    amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
    amm4MintAfterBalance0Store, amm4MintStore]

def amm4MintAfterLiq1Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) : Store :=
  (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1).insert "liq1"
    (.int (Int.ofNat (((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      supply1.toNat) / reserve1.toNat)))

def amm4MintSourcePrefixLiq1Numerator : List Stmt :=
  nonpayable ++
    [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
     tokenBalance (.storage token0Ref) "balance0",
     tokenBalance (.storage token1Ref) "balance1",
     .letDecl "amount0" (some uint256)
       (checkedSub (.var "balance0") (.storage reserve0Ref)),
     .letDecl "amount1" (some uint256)
       (checkedSub (.var "balance1") (.storage reserve1Ref)),
     .letDecl "liq0Numerator" (some uint256)
       (checkedMul (.var "amount0") (.storage totalSupplyRef))] ++
    checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref) ++
    [.letDecl "liq1Numerator" (some uint256)
      (checkedMul (.var "amount1") (.storage totalSupplyRef))]

theorem amm4MintSourceLiq1Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixLiq1Numerator
      (.ok { contract := contract, locals :=
        (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) } evm2))
    (hnonzero : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixLiq1Numerator ++
        checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref))
      (.ok { contract := contract, locals := (amm4MintAfterLiq1Store I o1 o2
        r0 r1 supply reserve0 supply1
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have hnum := amm4MintEvalLiq1NumeratorLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  have hden := amm4MintEvalReserve1AfterLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  have hguard := amm4EvalNatNeZero_true hden hnonzero
  have hdiv := amm4EvalNatDiv_ok hnum hden hnonzero
  have htail : ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm2 (checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref))
      (.ok { contract := contract, locals := (amm4MintAfterLiq1Store I o1 o2
        r0 r1 supply reserve0 supply1
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa only [amm4MintAfterLiq1Store] using
      (amm4LetDeclOne (ty := some uint256) (name := "liq1") hdiv)
  exact execBlock_append hprefix htail

theorem amm4MintSourceLiq1ReserveZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixLiq1Numerator
      (.ok { contract := contract, locals :=
        (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) } evm2))
    (hzero : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have hden := amm4MintEvalReserve1AfterLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  rw [hzero] at hden
  have hguard := amm4EvalNatNeZero_false hden
  have htail : ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm2 (mintTransition.body.drop 10) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [amm4MintSourcePrefixLiq1Numerator, mintTransition, nonpayable,
      tokenBalance, checkedDivInto, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody


end Benchmarks.ActAmm4
