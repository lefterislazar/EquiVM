import Benchmarks.ActAmm4.SwapSourceStores

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapInput0Nat (evm4 : EVM.State) (I : ExecutionEnv)
    (out0 : ByteArray) : Nat :=
  if (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
      (amm4SwapAmount0Word I).toNat <
      fromByteArrayBigEndian (out0.extract 0 32)
  then amm4SwapAmount0InPosNat evm4 I out0 else 0

def amm4SwapInput1Nat (evm4 : EVM.State) (I : ExecutionEnv)
    (out1 : ByteArray) : Nat :=
  if (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
      (amm4SwapAmount1Word I).toNat <
      fromByteArrayBigEndian (out1.extract 0 32)
  then amm4SwapAmount1InPosNat evm4 I out1 else 0

theorem amm4SwapSourceAmount0InCases
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 } evm4))
    (hlo : 32 ≤ out0.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount0In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1
          (amm4SwapInput0Nat evm4 I out0)) } evm4) := by
  by_cases hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat <
      fromByteArrayBigEndian (out0.extract 0 32)
  · simpa [amm4SwapInput0Nat, hgt] using
      amm4SwapSourceAmount0InPositive I b0 b1 out0 out1
        hprefix hlo hgt
  · have hle : fromByteArrayBigEndian (out0.extract 0 32) ≤
        (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
          (amm4SwapAmount0Word I).toNat := by omega
    simpa [amm4SwapInput0Nat, hgt] using
      amm4SwapSourceAmount0InZero I b0 b1 out0 out1 hprefix hle

theorem amm4SwapSourceAmount1InCases
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve1
      (.ok { contract := contract, locals :=
        (amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1
          (amm4SwapInput0Nat evm4 I out0)) } evm4))
    (hlo : 32 ≤ out1.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1
          (amm4SwapInput0Nat evm4 I out0)
          (amm4SwapInput1Nat evm4 I out1)) } evm4) := by
  by_cases hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat <
      fromByteArrayBigEndian (out1.extract 0 32)
  · simpa [amm4SwapInput1Nat, hgt] using
      amm4SwapSourceAmount1InPositive I b0 b1 out0 out1
        (amm4SwapInput0Nat evm4 I out0) hprefix hlo hgt
  · have hle : fromByteArrayBigEndian (out1.extract 0 32) ≤
        (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
          (amm4SwapAmount1Word I).toNat := by omega
    simpa [amm4SwapInput1Nat, hgt] using
      amm4SwapSourceAmount1InZero I b0 b1 out0 out1
        (amm4SwapInput0Nat evm4 I out0) hprefix hle

theorem amm4SwapSourceSuccessFromBalances
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance1
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 } evm4))
    (hlo0 : 32 ≤ out0.size) (hlo1 : 32 ≤ out1.size)
    (hle0 : (amm4SwapAmount0Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat)
    (hle1 : (amm4SwapAmount1Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat)
    (hpos : 0 < amm4SwapInput0Nat evm4 I out0 ∨
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
  have hres0 := amm4SwapSourceReserve0Ok I b0 b1 out0 out1
    hprefix hle0
  have hin0 := amm4SwapSourceAmount0InCases I b0 b1 out0 out1
    hres0 hlo0
  have hres1 := amm4SwapSourceReserve1Ok I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0) hin0 hle1
  have hin1 := amm4SwapSourceAmount1InCases I b0 b1 out0 out1
    hres1 hlo1
  have hguard := amm4SwapSourceInputGuardOk I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hin1 hpos
  have hnew := amm4SwapSourceNewProductOk I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hguard hfitNew
  have hold := amm4SwapSourceOldProductOk I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hnew hfitOld
  have hkguard := amm4SwapSourceKGuardOk I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hold hk
  have hstored := amm4SwapSourceReserve0Stored I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hkguard hlo0
  exact amm4SwapSourceSuccess I b0 b1 out0 out1
    (amm4SwapInput0Nat evm4 I out0)
    (amm4SwapInput1Nat evm4 I out1) hstored hlo1

end Benchmarks.ActAmm4
