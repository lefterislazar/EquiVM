import Benchmarks.ActAmm.Swap0Balance0Call
import Benchmarks.ActAmm.Swap0SourceCall
import Benchmarks.ActAmm.MintSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0SourceBalance0CallFailed
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (false, evm2, out) false) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
    (by simp [ammSwap0AfterTransferStore, ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterTransferStore I b }
      evm1 (swap0Transition.body.drop 5) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap0SourceBalance0DecodeRevert
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
    (by simp [ammSwap0AfterTransferStore, ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterTransferStore I b }
      evm1 (swap0Transition.body.drop 5) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap0AfterBalance0Store
    (I : ExecutionEnv) (b : Bool) (ret : ByteArray) : Store :=
  (ammSwap0AfterTransferStore I b).insert "balance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32))))

def ammSwap0SourcePrefixBalance0 : List Stmt :=
  ammSwap0SourcePrefixTransfer ++
    [tokenBalance (.storage token0Ref) "balance0"]

theorem ammSwap0SourceBalance0CallOk
    {evm evm1 evm2 : EVM.State}
    (I : ExecutionEnv) (b : Bool) (ret : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        evm1))
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm1.executionEnv.codeOwner]
      (true, evm2, ret) false) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance0
      (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
        evm2) := by
  have hreceiver := ammMintEvalToken0 (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
    (by simp [ammSwap0AfterTransferStore, ammSwap0Store])
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammSwap0AfterTransferStore I b)
  have hdec := ammMintDecodeBalance_ok hretLo
    (by omega : ret.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterTransferStore I b }
      evm1 [tokenBalance (.storage token0Ref) "balance0"]
      (.ok { contract := contract, locals := ammSwap0AfterBalance0Store I b ret }
        evm2) := by
    simp only [tokenBalance]
    simpa [ammSwap0AfterBalance0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
