import Benchmarks.ActAmm.MintArithmeticTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammMintEvalToken0 {evm : EVM.State} {locals : Store}
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

theorem ammMintEvalToken0_initState {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store} (hnone : locals.get? "token0" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage token0Ref) =
        .ok (.address (AccountAddress.ofUInt256 (ammMintToken0Word σ I))) := by
  simpa [ammMintToken0Word, solcSlotWord, initState, Solm.EVM.storageLoad]
    using (ammMintEvalToken0 (evm := initState cA gh bl σ σ₀ g A I) hnone)

theorem ammMintEvalToken1 {evm : EVM.State} {locals : Store}
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

theorem ammMintEvalBalanceArgs {evm : EVM.State} {locals : Store} :
    evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind, bind, pure]

theorem ammMintEvalSupply {evm : EVM.State} {locals : Store}
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
    (by simpa using ammStorageLocLoad_uint256 evm ⟨0⟩)

theorem ammMintEvalReserve0 {evm : EVM.State} {locals : Store}
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
    (by simpa using ammStorageLocLoad_uint256 evm ⟨5⟩)

theorem ammMintEvalReserve1 {evm : EVM.State} {locals : Store}
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
    (by simpa using ammStorageLocLoad_uint256 evm ⟨6⟩)

theorem ammMintEvalSupplyGuard_true {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "totalSupply" = none)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.storage totalSupplyRef) (.intLit 0)) = .ok (.bool true) := by
  have hs := ammMintEvalSupply (evm := evm) hnone
  have hn : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
    intro hz
    exact hnonzero (uint256_toNat_eq_zero hz)
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hs, hn]

theorem ammMintEvalSupplyGuard_false {evm : EVM.State} {locals : Store}
    (hnone : locals.get? "totalSupply" = none)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.storage totalSupplyRef) (.intLit 0)) = .ok (.bool false) := by
  have hs := ammMintEvalSupply (evm := evm) hnone
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hs, hzero]

theorem ammMintSourceZeroSupply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hguard := ammMintEvalSupplyGuard_false (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore]) hzero
  have hblock : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammMintSourceToken0CallFailed (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (false, evm', out) false) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hguard := ammMintEvalSupplyGuard_true (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore]) hnonzero
  have hreceiver := ammMintEvalToken0 (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm) (locals := ammMintStore I)
  have hblock : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammMintDecodeBalance_short {o : ByteArray} (hshort : o.size < 32) :
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

theorem ammMintDecodeBalance_ok {o : ByteArray}
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

def ammMintAfterBalance0Store (I : ExecutionEnv) (out : ByteArray) : Store :=
  (ammMintStore I).insert "balance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

theorem ammMintSourceToken0CallOk (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm', out) false) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0"])
      (.ok { contract := contract, locals := ammMintAfterBalance0Store I out } evm') := by
  have hguard := ammMintEvalSupplyGuard_true (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore]) hnonzero
  have hreceiver := ammMintEvalToken0 (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm) (locals := ammMintStore I)
  have hdec := ammMintDecodeBalance_ok hlo (by omega : out.size < 2 ^ 255)
  simp only [nonpayable, tokenBalance, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  simpa [ammMintAfterBalance0Store, collapseReturns] using
    (ExecBlock.consNormal
      (ExecStmt.externalCallSuccess hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
      ExecBlock.nil)

theorem ammMintSourceToken0DecodeShort (evm evm' : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hshort : out.size < 32)
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask)).val) "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm', out) false) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hguard := ammMintEvalSupplyGuard_true (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore]) hnonzero
  have hreceiver := ammMintEvalToken0 (evm := evm)
    (locals := ammMintStore I) (by simp [ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm) (locals := ammMintStore I)
  have hdec := ammMintDecodeBalance_short hshort
  have hblock : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammMintSourceToken1CallFailed (evm evm1 evm2 : EVM.State)
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
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hprefix := ammMintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo hbound hcall0
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
    (by simp [ammMintAfterBalance0Store, ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterBalance0Store I o1 }
      evm1 (tokenBalance (.storage token1Ref) "balance1" ::
        mintTransition.body.drop 4) .reverted := by
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall1)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, List.drop,
      List.cons_append, List.nil_append] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintSourceToken1DecodeShort (evm evm1 evm2 : EVM.State)
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
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hprefix := ammMintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo hbound hcall0
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
    (by simp [ammMintAfterBalance0Store, ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
  have hdec := ammMintDecodeBalance_short hshort
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterBalance0Store I o1 }
      evm1 (tokenBalance (.storage token1Ref) "balance1" ::
        mintTransition.body.drop 4) .reverted := by
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall1 hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, List.drop,
      List.cons_append, List.nil_append] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammMintAfterBalance1Store (I : ExecutionEnv) (o1 o2 : ByteArray) : Store :=
  (ammMintAfterBalance0Store I o1).insert "balance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32))))

theorem ammMintSourceToken1CallOk (evm evm1 evm2 : EVM.State)
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
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 } evm2) := by
  have hprefix := ammMintSourceToken0CallOk evm evm1 I o1 hwv hnonzero hlo1 hbound1 hcall0
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
    (by simp [ammMintAfterBalance0Store, ammMintStore])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammMintAfterBalance0Store I o1)
  have hdec := ammMintDecodeBalance_ok hlo2 (by omega : o2.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterBalance0Store I o1 }
      evm1 [tokenBalance (.storage token1Ref) "balance1"]
      (.ok { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 } evm2) := by
    simpa [ammMintAfterBalance1Store, collapseReturns, tokenBalance] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver (by simp [evalExpr?, pure]) hargs hcall1 hdec)
        ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem ammMintEvalBalance0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} :
    evalExpr? config { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
  have hget : (ammMintAfterBalance1Store I o1 o2).get? "balance0" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
    unfold ammMintAfterBalance1Store
    rw [store_get_ne (ammMintAfterBalance0Store I o1) (k := "balance1")
      (a := "balance0") _ (by decide)]
    simp [ammMintAfterBalance0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammMintEvalBalance1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} :
    evalExpr? config { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
  simp [ammMintAfterBalance1Store, evalExpr?, EvalResult.ofOption]

theorem ammMintEvalAmount0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray}
    (hlo : 32 ≤ o1.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (o1.extract 0 32)) :
    evalExpr? config { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm
      (checkedSub (.var "balance0") (.storage reserve0Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat))) := by
  exact ammEvalCheckedSub_ok ammMintEvalBalance0
    (ammMintEvalReserve0 (by simp [ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hle
    (fromByteArrayBigEndian_extract0_32_lt hlo)

theorem ammMintEvalAmount0_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray}
    (hunder : fromByteArrayBigEndian (o1.extract 0 32) <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm
      (checkedSub (.var "balance0") (.storage reserve0Ref)) = .revert := by
  exact ammEvalCheckedSub_revert ammMintEvalBalance0
    (ammMintEvalReserve0 (by simp [ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hunder

def ammMintAfterAmount0Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 : UInt256) : Store :=
  (ammMintAfterBalance1Store I o1 o2).insert "amount0"
    (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat)))

theorem ammMintSourceAmount0Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 } evm2))
    (hlo : 32 ≤ o1.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (o1.extract 0 32)) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := (ammMintAfterAmount0Store I o1 o2
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have heval := ammMintEvalAmount0 (I := I) (o1 := o1) (o2 := o2) hlo hle
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm2 [.letDecl "amount0" (some uint256)
        (checkedSub (.var "balance0") (.storage reserve0Ref))]
      (.ok { contract := contract, locals := (ammMintAfterAmount0Store I o1 o2
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simpa [ammMintAfterAmount0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem ammMintSourceAmount0Underflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1"])
      (.ok { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 } evm2))
    (hunder : fromByteArrayBigEndian (o1.extract 0 32) <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalAmount0_revert (I := I) (o1 := o1) (o2 := o2) hunder
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterBalance1Store I o1 o2 }
      evm2 (mintTransition.body.drop 4) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintEvalAmount1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 : UInt256}
    (hlo : 32 ≤ o2.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (o2.extract 0 32)) :
    evalExpr? config { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm
      (checkedSub (.var "balance1") (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (o2.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))) := by
  have hget : (ammMintAfterAmount0Store I o1 o2 r0).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    unfold ammMintAfterAmount0Store
    rw [store_get_ne (ammMintAfterBalance1Store I o1 o2) (k := "amount0")
      (a := "balance1") _ (by decide)]
    simp [ammMintAfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  have hbal : evalExpr? config
      { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    simp [evalExpr?, hget, EvalResult.ofOption]
  exact ammEvalCheckedSub_ok hbal
    (ammMintEvalReserve1 (by simp [ammMintAfterAmount0Store,
      ammMintAfterBalance1Store, ammMintAfterBalance0Store, ammMintStore]))
    hle (fromByteArrayBigEndian_extract0_32_lt hlo)

theorem ammMintEvalAmount1_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 : UInt256}
    (hunder : fromByteArrayBigEndian (o2.extract 0 32) <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm
      (checkedSub (.var "balance1") (.storage reserve1Ref)) = .revert := by
  have hget : (ammMintAfterAmount0Store I o1 o2 r0).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    unfold ammMintAfterAmount0Store
    rw [store_get_ne (ammMintAfterBalance1Store I o1 o2) (k := "amount0")
      (a := "balance1") _ (by decide)]
    simp [ammMintAfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  have hbal : evalExpr? config
      { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
    simp [evalExpr?, hget, EvalResult.ofOption]
  exact ammEvalCheckedSub_revert hbal
    (ammMintEvalReserve1 (by simp [ammMintAfterAmount0Store,
      ammMintAfterBalance1Store, ammMintAfterBalance0Store, ammMintStore])) hunder

def ammMintAfterAmount1Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 : UInt256) : Store :=
  (ammMintAfterAmount0Store I o1 o2 r0).insert "amount1"
    (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat)))

theorem ammMintSourceAmount1Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 } evm2))
    (hlo : 32 ≤ o2.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (o2.extract 0 32)) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals :=
        (ammMintAfterAmount1Store I o1 o2 r0
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have heval := ammMintEvalAmount1 (I := I) (o1 := o1) (o2 := o2) (r0 := r0)
    hlo hle
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm2 [.letDecl "amount1" (some uint256)
        (checkedSub (.var "balance1") (.storage reserve1Ref))]
      (.ok { contract := contract, locals :=
        (ammMintAfterAmount1Store I o1 o2 r0
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simpa [ammMintAfterAmount1Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem ammMintSourceAmount1Underflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 } evm2))
    (hunder : fromByteArrayBigEndian (o2.extract 0 32) <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalAmount1_revert (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) hunder
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterAmount0Store I o1 o2 r0 }
      evm2 (mintTransition.body.drop 5) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintEvalAmount0Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm (.var "amount0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat))) := by
  have hget : (ammMintAfterAmount1Store I o1 o2 r0 r1).get? "amount0" =
      some (.int (Int.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat))) := by
    unfold ammMintAfterAmount1Store
    rw [store_get_ne (ammMintAfterAmount0Store I o1 o2 r0) (k := "amount1")
      (a := "amount0") _ (by decide)]
    simp [ammMintAfterAmount0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammMintEvalAmount1Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm (.var "amount1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
  simp [ammMintAfterAmount1Store, evalExpr?, EvalResult.ofOption]

theorem ammMintEvalLiq0Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hfit : (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm (checkedMul (.var "amount0") (.storage totalSupplyRef)) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))) := by
  exact ammEvalCheckedMul_ok ammMintEvalAmount0Local
    (ammMintEvalSupply (by simp [ammMintAfterAmount1Store,
      ammMintAfterAmount0Store, ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hfit

theorem ammMintEvalLiq0Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm (checkedMul (.var "amount0") (.storage totalSupplyRef)) = .revert := by
  exact ammEvalCheckedMul_revert ammMintEvalAmount0Local
    (ammMintEvalSupply (by simp [ammMintAfterAmount1Store,
      ammMintAfterAmount0Store, ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hover

def ammMintAfterLiq0NumeratorStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply : UInt256) : Store :=
  (ammMintAfterAmount1Store I o1 o2 r0 r1).insert "liq0Numerator"
    (.int (Int.ofNat
      ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat)))

theorem ammMintSourceLiq0NumeratorOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 } evm2))
    (hfit : (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
      (.ok { contract := contract, locals := (ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
  have heval := ammMintEvalLiq0Numerator (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) (r1 := r1) hfit
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm2 [.letDecl "liq0Numerator" (some uint256)
        (checkedMul (.var "amount0") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := (ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
    simpa [ammMintAfterLiq0NumeratorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have hblock := execBlock_append hprefix htail
  simpa [nonpayable, List.cons_append, List.nil_append] using hblock

theorem ammMintSourceLiq0NumeratorOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         tokenBalance (.storage token0Ref) "balance0",
         tokenBalance (.storage token1Ref) "balance1",
         .letDecl "amount0" (some uint256)
           (checkedSub (.var "balance0") (.storage reserve0Ref)),
         .letDecl "amount1" (some uint256)
           (checkedSub (.var "balance1") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 } evm2))
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalLiq0Numerator_revert (I := I) (o1 := o1) (o2 := o2)
    (r0 := r0) (r1 := r1) hover
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterAmount1Store I o1 o2 r0 r1 }
      evm2 (mintTransition.body.drop 6) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintEvalLiq0NumeratorLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply : UInt256} :
    evalExpr? config { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm (.var "liq0Numerator") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat))) := by
  simp [ammMintAfterLiq0NumeratorStore, evalExpr?, EvalResult.ofOption]

theorem ammMintEvalReserve0AfterLiq0Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply : UInt256} :
    evalExpr? config { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  apply ammMintEvalReserve0
  simp [ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
    ammMintAfterAmount0Store, ammMintAfterBalance1Store,
    ammMintAfterBalance0Store, ammMintStore]

def ammMintAfterLiq0Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 : UInt256) : Store :=
  (ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply).insert "liq0"
    (.int (Int.ofNat (((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) *
      supply.toNat) / reserve0.toNat)))

theorem ammMintSourceLiq0Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
      (.ok { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply } evm2))
    (hnonzero : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
      (.ok { contract := contract, locals := (ammMintAfterLiq0Store I o1 o2 r0 r1 supply
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have hnum := ammMintEvalLiq0NumeratorLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  have hden := ammMintEvalReserve0AfterLiq0Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  have hguard := ammEvalNatNeZero_true hden hnonzero
  have hdiv := ammEvalNatDiv_ok hnum hden hnonzero
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm2 (checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref))
      (.ok { contract := contract, locals := (ammMintAfterLiq0Store I o1 o2 r0 r1 supply
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [ammMintAfterLiq0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [List.append_assoc] using (execBlock_append hprefix htail)

theorem ammMintSourceLiq0ReserveZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
      (.ok { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply } evm2))
    (hzero : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hden := ammMintEvalReserve0AfterLiq0Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1) (supply := supply)
  rw [hzero] at hden
  have hguard := ammEvalNatNeZero_false hden
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterLiq0NumeratorStore I o1 o2 r0 r1 supply }
      evm2 (mintTransition.body.drop 7) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintEvalAmount1AfterLiq0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256} :
    evalExpr? config { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (.var "amount1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
  have hget : (ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).get? "amount1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat))) := by
    unfold ammMintAfterLiq0Store ammMintAfterLiq0NumeratorStore
    rw [store_get_ne _ (k := "liq0") (a := "amount1") _ (by decide)]
    rw [store_get_ne _ (k := "liq0Numerator") (a := "amount1") _ (by decide)]
    simp [ammMintAfterAmount1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammMintEvalLiq1Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hfit : (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    evalExpr? config { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (checkedMul (.var "amount1") (.storage totalSupplyRef)) =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat))) := by
  exact ammEvalCheckedMul_ok ammMintEvalAmount1AfterLiq0
    (ammMintEvalSupply (by simp [ammMintAfterLiq0Store,
      ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
      ammMintAfterAmount0Store, ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hfit

theorem ammMintEvalLiq1Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm (checkedMul (.var "amount1") (.storage totalSupplyRef)) = .revert := by
  exact ammEvalCheckedMul_revert ammMintEvalAmount1AfterLiq0
    (ammMintEvalSupply (by simp [ammMintAfterLiq0Store,
      ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
      ammMintAfterAmount0Store, ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore])) hover

def ammMintAfterLiq1NumeratorStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 : UInt256) : Store :=
  (ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).insert "liq1Numerator"
    (.int (Int.ofNat
      ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat)))

theorem ammMintSourceLiq1NumeratorOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
        (ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0) } evm2))
    (hfit : (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
      (.ok { contract := contract, locals := (ammMintAfterLiq1NumeratorStore I o1 o2
        r0 r1 supply reserve0 (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
  have heval := ammMintEvalLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) hfit
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 [.letDecl "liq1Numerator" (some uint256)
        (checkedMul (.var "amount1") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := (ammMintAfterLiq1NumeratorStore I o1 o2
        r0 r1 supply reserve0 (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩)) } evm2) := by
    change ExecBlock config
      { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 [.letDecl "liq1Numerator" (some uint256)
        (checkedMul (.var "amount1") (.storage totalSupplyRef))]
      (.ok { contract := contract, locals := ((ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0).insert "liq1Numerator"
          (.int (Int.ofNat
            ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
              (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat)))) } evm2)
    exact ammLetDeclOne heval
  simpa only [List.append_assoc] using (execBlock_append hprefix htail)

theorem ammMintSourceLiq1NumeratorOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray} {r0 r1 supply reserve0 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
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
        (ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0) } evm2))
    (hover : UInt256.size ≤
      (fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalLiq1Numerator_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) hover
  have htail : ExecBlock config
      { contract := contract, locals := ammMintAfterLiq0Store I o1 o2 r0 r1 supply reserve0 }
      evm2 (mintTransition.body.drop 9) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammMintEvalLiq1NumeratorLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm (.var "liq1Numerator") =
      .ok (.int (Int.ofNat
        ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat))) := by
  simp [ammMintAfterLiq1NumeratorStore, evalExpr?, EvalResult.ofOption]

theorem ammMintEvalReserve1AfterLiq1Numerator {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply ammMintEvalReserve1
  simp [ammMintAfterLiq1NumeratorStore, ammMintAfterLiq0Store,
    ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
    ammMintAfterAmount0Store, ammMintAfterBalance1Store,
    ammMintAfterBalance0Store, ammMintStore]

def ammMintAfterLiq1Store (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) : Store :=
  (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1).insert "liq1"
    (.int (Int.ofNat (((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) *
      supply1.toNat) / reserve1.toNat)))

def ammMintSourcePrefixLiq1Numerator : List Stmt :=
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

theorem ammMintSourceLiq1Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixLiq1Numerator
      (.ok { contract := contract, locals :=
        (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) } evm2))
    (hnonzero : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (ammMintSourcePrefixLiq1Numerator ++
        checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref))
      (.ok { contract := contract, locals := (ammMintAfterLiq1Store I o1 o2
        r0 r1 supply reserve0 supply1
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have hnum := ammMintEvalLiq1NumeratorLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  have hden := ammMintEvalReserve1AfterLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  have hguard := ammEvalNatNeZero_true hden hnonzero
  have hdiv := ammEvalNatDiv_ok hnum hden hnonzero
  have htail : ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm2 (checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref))
      (.ok { contract := contract, locals := (ammMintAfterLiq1Store I o1 o2
        r0 r1 supply reserve0 supply1
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa only [ammMintAfterLiq1Store] using
      (ammLetDeclOne (ty := some uint256) (name := "liq1") hdiv)
  exact execBlock_append hprefix htail

theorem ammMintSourceLiq1ReserveZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 : UInt256}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixLiq1Numerator
      (.ok { contract := contract, locals :=
        (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) } evm2))
    (hzero : Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have hden := ammMintEvalReserve1AfterLiq1Numerator (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0) (supply1 := supply1)
  rw [hzero] at hden
  have hguard := ammEvalNatNeZero_false hden
  have htail : ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1NumeratorStore I o1 o2 r0 r1 supply reserve0 supply1) }
      evm2 (mintTransition.body.drop 10) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [ammMintSourcePrefixLiq1Numerator, mintTransition, nonpayable,
      tokenBalance, checkedDivInto, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody


end Benchmarks.ActAmm
