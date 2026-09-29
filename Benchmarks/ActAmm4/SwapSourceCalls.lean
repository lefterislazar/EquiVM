import Benchmarks.ActAmm4.SwapSourceGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapEvalTransfer0Args {evm : EVM.State} {I : ExecutionEnv} :
    evalExprs? config
      { contract := contract, locals := amm4SwapStore I }
      evm [(.var "amount0Out"), (.var "to")] =
        .ok [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
          .address (AccountAddress.ofUInt256 (amm4SwapToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, amm4SwapStore,
    EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

def amm4SwapAfterTransfer0Store (I : ExecutionEnv) (b0 : Bool) : Store :=
  (amm4SwapStore I).insert "transfer0Ok" (.bool b0)

def amm4SwapSourcePrefixTransfer0 : List Stmt :=
  amm4SwapSourcePrefixRecipient ++
    [tokenTransfer (.storage token0Ref) (.var "amount0Out")
      (.var "to") "transfer0Ok"]

theorem amm4SwapSourceTransfer0CallOk
    {evm evm1 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b0 : Bool)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out =
      some [.bool b0]) :
    ExecBlock config { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer0
      (.ok { contract := contract, locals := amm4SwapAfterTransfer0Store I b0 }
        evm1) := by
  have hprefix := amm4SwapSourceRecipientOk evm I
    hwv hpos hliq0 hliq1 h0 h1
  have hreceiver := amm4SwapEvalToken0 (evm := evm) (I := I)
  have hargs := amm4SwapEvalTransfer0Args (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm [tokenTransfer (.storage token0Ref) (.var "amount0Out")
        (.var "to") "transfer0Ok"]
      (.ok { contract := contract, locals := amm4SwapAfterTransfer0Store I b0 }
        evm1) := by
    simp only [tokenTransfer]
    simpa [amm4SwapAfterTransfer0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SwapEvalTransfer1Args {evm : EVM.State} {I : ExecutionEnv}
    {b0 : Bool} :
    evalExprs? config
      { contract := contract, locals := amm4SwapAfterTransfer0Store I b0 }
      evm [(.var "amount1Out"), (.var "to")] =
        .ok [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
          .address (AccountAddress.ofUInt256 (amm4SwapToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, amm4SwapAfterTransfer0Store,
    amm4SwapStore, EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

def amm4SwapAfterTransfer1Store (I : ExecutionEnv) (b0 b1 : Bool) : Store :=
  (amm4SwapAfterTransfer0Store I b0).insert "transfer1Ok" (.bool b1)

def amm4SwapSourcePrefixTransfer1 : List Stmt :=
  amm4SwapSourcePrefixTransfer0 ++
    [tokenTransfer (.storage token1Ref) (.var "amount1Out")
      (.var "to") "transfer1Ok"]

theorem amm4SwapSourceTransfer1CallOk
    {evm evm1 evm2 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer0
      (.ok { contract := contract, locals := amm4SwapAfterTransfer0Store I b0 }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm2, out) true)
    (hdec : config.externalABI.decode? "transfer" out =
      some [.bool b1]) :
    ExecBlock config { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2) := by
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4SwapAfterTransfer0Store I b0)
    (by simp [amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4SwapEvalTransfer1Args (evm := evm1) (I := I) (b0 := b0)
  have htail : ExecBlock config
      { contract := contract, locals := amm4SwapAfterTransfer0Store I b0 }
      evm1 [tokenTransfer (.storage token1Ref) (.var "amount1Out")
        (.var "to") "transfer1Ok"]
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2) := by
    simp only [tokenTransfer]
    simpa [amm4SwapAfterTransfer1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
