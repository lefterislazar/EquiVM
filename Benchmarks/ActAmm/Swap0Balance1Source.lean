import Benchmarks.ActAmm.Swap0Balance1Call
import Benchmarks.ActAmm.Swap0Balance0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0SourceBalance1CallFailed
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (false, evm2, out) false) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
    (by simp [ammSwap0AfterBalance0Store, ammSwap0AfterTransferStore,
      ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
      evm1 (swap0Transition.body.drop 6) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixBalance0,
      ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap0SourceBalance1DecodeRevert
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
    (by simp [ammSwap0AfterBalance0Store, ammSwap0AfterTransferStore,
      ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
      evm1 (swap0Transition.body.drop 6) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixBalance0,
      ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap0AfterBalance1Store
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray) : Store :=
  (ammSwap0AfterBalance0Store I b ret).insert "balance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

def ammSwap0SourcePrefixBalance1 : List Stmt :=
  ammSwap0SourcePrefixBalance0 ++
    [tokenBalance (.storage token1Ref) "balance1"]

theorem ammSwap0SourceBalance1CallOk
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
        evm1))
    (houtLo : 32 ≤ out.size) (houtBound : out.size < 2 ^ 138)
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, out) false) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2) := by
  have hreceiver := ammMintEvalToken1 (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
    (by simp [ammSwap0AfterBalance0Store, ammSwap0AfterTransferStore,
      ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterBalance0Store I b ret)
  have hdec := ammMintDecodeBalance_ok houtLo
    (by omega : out.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
      evm1 [tokenBalance (.storage token1Ref) "balance1"]
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2) := by
    simp only [tokenBalance]
    simpa [ammSwap0AfterBalance1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
