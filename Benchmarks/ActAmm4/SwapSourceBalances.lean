import Benchmarks.ActAmm4.SwapSourceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapAfterBalance0Store (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 : ByteArray) : Store :=
  (amm4SwapAfterTransfer1Store I b0 b1).insert "balance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (out0.extract 0 32))))

def amm4SwapSourcePrefixBalance0 : List Stmt :=
  amm4SwapSourcePrefixTransfer1 ++
    [tokenBalance (.storage token0Ref) "balance0"]

theorem amm4SwapSourceBalance0CallOk
    {evm evm2 evm3 : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2))
    (hcall : typedCallViaEVM config evm2
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm2
          evm2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm2.executionEnv.codeOwner]
      (true, evm3, out0) false)
    (hlo : 32 ≤ out0.size) (hbound : out0.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance0
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3) := by
  have hreceiver := amm4MintEvalToken0 (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
    (by simp [amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : out0.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract,
        locals := amm4SwapAfterTransfer1Store I b0 b1 }
      evm2 [tokenBalance (.storage token0Ref) "balance0"]
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3) := by
    simp only [tokenBalance]
    simpa [amm4SwapAfterBalance0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

def amm4SwapAfterBalance1Store (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) : Store :=
  (amm4SwapAfterBalance0Store I b0 b1 out0).insert "balance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32))))

def amm4SwapSourcePrefixBalance1 : List Stmt :=
  amm4SwapSourcePrefixBalance0 ++
    [tokenBalance (.storage token1Ref) "balance1"]

theorem amm4SwapSourceBalance1CallOk
    {evm evm3 evm4 : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance0
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3))
    (hcall : typedCallViaEVM config evm3
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm3
          evm3.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm3.executionEnv.codeOwner]
      (true, evm4, out1) false)
    (hlo : 32 ≤ out1.size) (hbound : out1.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance1
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 } evm4) := by
  have hreceiver := amm4MintEvalToken1 (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
    (by simp [amm4SwapAfterBalance0Store, amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : out1.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract,
        locals := amm4SwapAfterBalance0Store I b0 b1 out0 }
      evm3 [tokenBalance (.storage token1Ref) "balance1"]
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 } evm4) := by
    simp only [tokenBalance]
    simpa [amm4SwapAfterBalance1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
