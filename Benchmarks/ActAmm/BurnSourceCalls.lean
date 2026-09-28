import Benchmarks.ActAmm.BurnSourceSender
import Benchmarks.ActAmm.BurnTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammStorageStoreContext (evm : EVM.State) (addr : AccountAddress)
    (slot value : UInt256) :
    (Solm.EVM.storageStore evm addr slot value).σ₀ = evm.σ₀ ∧
    (Solm.EVM.storageStore evm addr slot value).genesisBlockHeader =
      evm.genesisBlockHeader ∧
    (Solm.EVM.storageStore evm addr slot value).blocks = evm.blocks ∧
    (Solm.EVM.storageStore evm addr slot value).substate = evm.substate := by
  unfold Solm.EVM.storageStore
  cases h : evm.lookupAccount addr <;>
    simp [h, Option.option, State.setAccount]

theorem ammBurnPostDebitContext (evm : EVM.State) (I : ExecutionEnv) :
    (ammBurnAfterSender (ammBurnAfterSupply evm I) I).σ₀ = evm.σ₀ ∧
    (ammBurnAfterSender (ammBurnAfterSupply evm I) I).genesisBlockHeader =
      evm.genesisBlockHeader ∧
    (ammBurnAfterSender (ammBurnAfterSupply evm I) I).blocks = evm.blocks ∧
    (ammBurnAfterSender (ammBurnAfterSupply evm I) I).substate = evm.substate := by
  let evm3 := ammBurnAfterSupply evm I
  have h3 := ammStorageStoreContext evm evm.executionEnv.codeOwner ⟨0⟩
    (ammBurnSupplyWord evm I)
  have h4 := ammStorageStoreContext evm3 evm3.executionEnv.codeOwner
    (ammTransferSenderSlot I) (ammBurnSenderDebitWord evm3 I)
  exact ⟨h4.1.trans h3.1,
    h4.2.1.trans h3.2.1,
    h4.2.2.1.trans h3.2.2.1,
    h4.2.2.2.trans h3.2.2.2⟩

def ammBurnSourcePrefixSender : List Stmt :=
  ammBurnSourcePrefixSupply ++
    [.assign .storage (balanceOfRef sender)
      (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity"))]

theorem ammBurnEvalTransfer0Args (evm evm4 : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm4 [(.var "amount0"), (.var "to")] =
        .ok [.int (Int.ofNat (ammBurnAmount0Value evm I)),
          .address (AccountAddress.ofUInt256 (ammBurnToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, ammBurnAfterAmount1Store,
    ammBurnAfterNum1Store, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore,
    EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

theorem ammBurnAfterAmount1Store_token0_none (evm : EVM.State)
    (I : ExecutionEnv) :
    (ammBurnAfterAmount1Store evm I).get? "token0" = none := by
  simp [ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
    ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnDecodeTransfer_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "transfer" o = none := by
  have hlen : o.toList.length = o.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((o.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hdec :
      ABI.decodeReturnValueWithMode? DecodeMode.modern boolTy o = none := by
    unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
      ABI.decodeReturnValues?
    have hguard : ¬ (2 : Nat) ^ 255 ≤ o.toList.length := by
      rw [hlen]
      omega
    simp only [hguard, and_false, ↓reduceIte]
    rw [abiTupleHeadSize_scalarWords_eq (types := [boolTy]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [boolTy]) (bytes := o.toList) (cursor := 0)
      (total := 32 * [boolTy].length) (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern boolTy o.toList 0 =
          none := by
      simp only [decodeScalarWordWithMode?, readWord?, readBytes?,
        decodeABIWord?, bind, Option.bind]
      rw [if_neg htake0n]
    rw [hscalar]
    rfl
  simp [config, externalABI, decodeReturn?, hdec]

theorem ammBurnDecodeTransfer_word {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < 2 ^ 255) :
    config.externalABI.decode? "transfer" o =
      (let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
       if v = ⟨0⟩ then some [.bool false]
       else if v = ⟨1⟩ then some [.bool true]
       else none) := by
  have hlen : o.toList.length = o.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((o.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := o)
  have hdec : ABI.decodeReturnValueWithMode? DecodeMode.modern boolTy o =
      (let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
       if v = ⟨0⟩ then some (.bool false)
       else if v = ⟨1⟩ then some (.bool true)
       else none) := by
    unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
      ABI.decodeReturnValues?
    have hguard : ¬ (2 : Nat) ^ 255 ≤ o.toList.length := by
      rw [hlen]
      omega
    simp only [hguard, and_false, ↓reduceIte]
    rw [abiTupleHeadSize_scalarWords_eq (types := [boolTy]) (by decide)]
    simp only [bind, Option.bind]
    rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.modern)
      (types := [boolTy]) (bytes := o.toList) (cursor := 0)
      (total := 32 * [boolTy].length) (by decide) (by simp)]
    simp only [decodeScalarWordsWithMode?]
    have hscalar :
        decodeScalarWordWithMode? DecodeMode.modern boolTy o.toList 0 =
          (let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
           if v = ⟨0⟩ then some (.bool false, 32)
           else if v = ⟨1⟩ then some (.bool true, 32)
           else none) := by
      simp only [decodeScalarWordWithMode?, readWord?, readBytes?,
        decodeABIWord?, bind, Option.bind]
      rw [if_pos htake0]
      let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
      have hv0 : ((v.val : Nat) = 0) ↔ v = ⟨0⟩ := by
        constructor
        · intro h
          apply u256_inj
          simpa [UInt256.toNat] using h
        · intro h
          rw [h]
          decide
      have hv1 : ((v.val : Nat) = 1) ↔ v = ⟨1⟩ := by
        constructor
        · intro h
          apply u256_inj
          simpa [UInt256.toNat] using h
        · intro h
          rw [h]
          decide
      simp only [boolTy, List.drop_zero, hword]
      dsimp only [v] at hv0 hv1
      simp only [hv0, hv1]
      split_ifs <;> simp_all [bind, Option.bind]
    rw [hscalar]
    let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
    by_cases hzero : v = ⟨0⟩
    · simp [v, hzero, bind, Option.bind]
    · by_cases hone : v = ⟨1⟩
      · simp [v, hzero, hone, bind, Option.bind, UInt256.size]
      · simp [v, hzero, hone, bind, Option.bind, UInt256.size]
  rw [show config.externalABI.decode? "transfer" o =
      (ABI.decodeReturnValueWithMode? DecodeMode.modern boolTy o).map
        (fun v => [v]) by rfl, hdec]
  let v := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  by_cases hzero : v = ⟨0⟩
  · simp [v, hzero]
  · by_cases hone : v = ⟨1⟩
    · simp [v, hzero, hone, UInt256.size]
    · simp [v, hzero, hone, UInt256.size]

theorem ammBurnSourceToken0CallFailed {evm evm4 evm5 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixSender
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm4))
    (hcall : typedCallViaEVM config evm4
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm4
          evm4.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount0Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (false, evm5, out) true) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm4)
    (locals := ammBurnAfterAmount1Store evm I)
    (ammBurnAfterAmount1Store_token0_none evm I)
  have hargs := ammBurnEvalTransfer0Args evm evm4 I
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm4 (burnTransition.body.drop 10) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammBurnSourceToken0DepthRevert {evm evm4 : EVM.State}
    (I : ExecutionEnv) (q0 : UInt256)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixSender
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm4))
    (hdepth : evm4.executionEnv.depth = 1024)
    (hq0 : q0.toNat = ammBurnAmount0Value evm I)
    (hto : (ammBurnToWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  let tgt : EVM.Address :=
    EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evm4
        evm4.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val
  have hcall : typedCallViaEVM config evm4 tgt "transfer" 0
      [.int (Int.ofNat (ammBurnAmount0Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (false,
        { evm4 with substate := (evm4.addAccessedAccount tgt).substate },
        ByteArray.empty) true := by
    apply callNotMade_depthLimit
      (calldata := (ammBurnToken0CalldataMem I q0).readWithPadding 128 68)
    · rw [← hq0]
      exact ammBurnToken0CalldataMem_encode I q0 q0.val.isLt hto
    · exact hdepth
  exact ammBurnSourceToken0CallFailed I ByteArray.empty hprefix hcall

theorem ammBurnSourceToken0DecodeRevert {evm evm4 evm5 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixSender
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm4))
    (hcall : typedCallViaEVM config evm4
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm4
          evm4.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount0Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (true, evm5, out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm4)
    (locals := ammBurnAfterAmount1Store evm I)
    (ammBurnAfterAmount1Store_token0_none evm I)
  have hargs := ammBurnEvalTransfer0Args evm evm4 I
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm4 (burnTransition.body.drop 10) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnAfterTransfer0Store (evm : EVM.State) (I : ExecutionEnv)
    (b : Bool) : Store :=
  (ammBurnAfterAmount1Store evm I).insert "transfer0Ok" (.bool b)

theorem ammBurnSourceToken0CallOk {evm evm4 evm5 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixSender
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm4))
    (hcall : typedCallViaEVM config evm4
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm4
          evm4.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount0Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (true, evm5, out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool b]) :
    ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSender ++
        [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
          "transfer0Ok"])
      (.ok { contract := contract, locals := ammBurnAfterTransfer0Store evm I b } evm5) := by
  have hreceiver := ammMintEvalToken0 (evm := evm4)
    (locals := ammBurnAfterAmount1Store evm I)
    (ammBurnAfterAmount1Store_token0_none evm I)
  have hargs := ammBurnEvalTransfer0Args evm evm4 I
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm4 [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
        "transfer0Ok"]
      (.ok { contract := contract, locals := ammBurnAfterTransfer0Store evm I b } evm5) := by
    simp only [tokenTransfer]
    simpa [ammBurnAfterTransfer0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammBurnAfterTransfer0Store_token1_none (evm : EVM.State)
    (I : ExecutionEnv) (b : Bool) :
    (ammBurnAfterTransfer0Store evm I b).get? "token1" = none := by
  simp [ammBurnAfterTransfer0Store, ammBurnAfterAmount1Store,
    ammBurnAfterNum1Store, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnEvalTransfer1Args (evm evm5 : EVM.State)
    (I : ExecutionEnv) (b : Bool) :
    evalExprs? config
      { contract := contract, locals := ammBurnAfterTransfer0Store evm I b }
      evm5 [(.var "amount1"), (.var "to")] =
        .ok [.int (Int.ofNat (ammBurnAmount1Value evm I)),
          .address (AccountAddress.ofUInt256 (ammBurnToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, ammBurnAfterTransfer0Store,
    ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
    ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore,
    EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

theorem ammBurnSourceToken1CallFailed {evm evm5 evm6 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSender ++
        [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
          "transfer0Ok"])
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer0Store evm I b0 } evm5))
    (hcall : typedCallViaEVM config evm5
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm5
          evm5.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount1Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (false, evm6, out1) true) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm5)
    (locals := ammBurnAfterTransfer0Store evm I b0)
    (ammBurnAfterTransfer0Store_token1_none evm I b0)
  have hargs := ammBurnEvalTransfer1Args evm evm5 I b0
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterTransfer0Store evm I b0 }
      evm5 (burnTransition.body.drop 11) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammBurnSourceToken1DecodeRevert {evm evm5 evm6 : EVM.State}
    (I : ExecutionEnv) (out1 : ByteArray) (b0 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSender ++
        [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
          "transfer0Ok"])
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer0Store evm I b0 } evm5))
    (hcall : typedCallViaEVM config evm5
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm5
          evm5.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount1Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (true, evm6, out1) true)
    (hdec : config.externalABI.decode? "transfer" out1 = none) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm5)
    (locals := ammBurnAfterTransfer0Store evm I b0)
    (ammBurnAfterTransfer0Store_token1_none evm I b0)
  have hargs := ammBurnEvalTransfer1Args evm evm5 I b0
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterTransfer0Store evm I b0 }
      evm5 (burnTransition.body.drop 11) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnAfterTransfer1Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) : Store :=
  (ammBurnAfterTransfer0Store evm I b0).insert "transfer1Ok" (.bool b1)

theorem ammBurnSourceToken1CallOk {evm evm5 evm6 : EVM.State}
    (I : ExecutionEnv) (out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSender ++
        [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
          "transfer0Ok"])
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer0Store evm I b0 } evm5))
    (hcall : typedCallViaEVM config evm5
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm5
          evm5.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammBurnAmount1Value evm I)),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
      (true, evm6, out1) true)
    (hdec : config.externalABI.decode? "transfer" out1 =
      some [.bool b1]) :
    ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSender ++
        [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
          "transfer0Ok",
         tokenTransfer (.storage token1Ref) (.var "amount1") (.var "to")
          "transfer1Ok"])
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 } evm6) := by
  have hreceiver := ammMintEvalToken1 (evm := evm5)
    (locals := ammBurnAfterTransfer0Store evm I b0)
    (ammBurnAfterTransfer0Store_token1_none evm I b0)
  have hargs := ammBurnEvalTransfer1Args evm evm5 I b0
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterTransfer0Store evm I b0 }
      evm5 [tokenTransfer (.storage token1Ref) (.var "amount1") (.var "to")
        "transfer1Ok"]
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 } evm6) := by
    simp only [tokenTransfer]
    simpa [ammBurnAfterTransfer1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  simpa [List.append_assoc] using execBlock_append hprefix htail

end Benchmarks.ActAmm
