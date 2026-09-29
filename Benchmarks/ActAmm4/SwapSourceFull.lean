import Benchmarks.ActAmm4.SwapSourceSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

theorem amm4SwapSourceSuccessFromCalls
    (evm evm1 evm2 evm3 evm4 : EVM.State)
    (I : ExecutionEnv) (ret0 ret1 out0 out1 : ByteArray)
    (b0 b1 : Bool)
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
    (hcall0 : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm1, ret0) true)
    (hdec0 : config.externalABI.decode? "transfer" ret0 = some [.bool b0])
    (hcall1 : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm2, ret1) true)
    (hdec1 : config.externalABI.decode? "transfer" ret1 = some [.bool b1])
    (hcallBalance0 : typedCallViaEVM config evm2
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm2
          evm2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm2.executionEnv.codeOwner]
      (true, evm3, out0) false)
    (hcallBalance1 : typedCallViaEVM config evm3
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm3
          evm3.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm3.executionEnv.codeOwner]
      (true, evm4, out1) false)
    (hlo0 : 32 ≤ out0.size) (hbound0 : out0.size < 2 ^ 138)
    (hlo1 : 32 ≤ out1.size) (hbound1 : out1.size < 2 ^ 138)
    (hle0 : (amm4SwapAmount0Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat)
    (hle1 : (amm4SwapAmount1Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat)
    (hinput : 0 < amm4SwapInput0Nat evm4 I out0 ∨
      0 < amm4SwapInput1Nat evm4 I out1)
    (hfitNew : amm4SwapNewProductNat out0 out1 < UInt256.size)
    (hfitOld : amm4SwapOldProductNat evm4 < UInt256.size)
    (hk : amm4SwapOldProductNat evm4 ≤
      amm4SwapNewProductNat out0 out1) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body
      (.returned { contract := contract, locals :=
        (amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1
          (amm4SwapInput0Nat evm4 I out0)
          (amm4SwapInput1Nat evm4 I out1)) }
        (amm4SwapAfterReserve1 (amm4SwapAfterReserve0 evm4 out0) out1)
        none) := by
  have hp0 := amm4SwapSourceTransfer0CallOk I ret0 b0 hwv
    hpos hliq0 hliq1 h0 h1 hcall0 hdec0
  have hp1 := amm4SwapSourceTransfer1CallOk I ret1 b0 b1
    hp0 hcall1 hdec1
  have hp2 := amm4SwapSourceBalance0CallOk I b0 b1 out0
    hp1 hcallBalance0 hlo0 hbound0
  have hp3 := amm4SwapSourceBalance1CallOk I b0 b1 out0 out1
    hp2 hcallBalance1 hlo1 hbound1
  exact amm4SwapSourceSuccessFromBalances I b0 b1 out0 out1
    hp3 hlo0 hlo1 hle0 hle1 hinput hfitNew hfitOld hk

end Benchmarks.ActAmm4
