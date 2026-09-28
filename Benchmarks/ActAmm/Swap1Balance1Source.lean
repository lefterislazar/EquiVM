import Benchmarks.ActAmm.Swap1Balance1Call
import Benchmarks.ActAmm.Swap1Balance0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1SourceBalance1CallFailed
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (false, evm2, out) false) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
    (by simp [ammSwap1AfterBalance0Store, ammSwap1AfterTransferStore,
      ammSwap1Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
      evm1 (swap1Transition.body.drop 6) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixBalance0,
      ammSwap1SourcePrefixTransfer,
      ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap1SourceBalance1DecodeRevert
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
    (by simp [ammSwap1AfterBalance0Store, ammSwap1AfterTransferStore,
      ammSwap1Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
      evm1 (swap1Transition.body.drop 6) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixBalance0,
      ammSwap1SourcePrefixTransfer,
      ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap1AfterBalance1Store
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray) : Store :=
  (ammSwap1AfterBalance0Store I b ret).insert "balance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

def ammSwap1SourcePrefixBalance1 : List Stmt :=
  ammSwap1SourcePrefixBalance0 ++
    [tokenBalance (.storage token1Ref) "balance1"]

theorem ammSwap1SourceBalance1CallOk
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
        evm1))
    (houtLo : 32 ≤ out.size) (houtBound : out.size < 2 ^ 138)
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, out) false) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2) := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
    (by simp [ammSwap1AfterBalance0Store, ammSwap1AfterTransferStore,
      ammSwap1Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap1AfterBalance0Store I b ret)
  have hdec := ammMintDecodeBalance_ok houtLo
    (by omega : out.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1AfterBalance0Store I b ret }
      evm1 [tokenBalance (.storage token1Ref) "balance1"]
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2) := by
    simp only [tokenBalance]
    simpa [ammSwap1AfterBalance1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
