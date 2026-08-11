import Examples.Precompiles.Modexp.MultiLimbClzPrefixes

/-! # Composed exact execution of the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def clzPreFinal (x : UInt256) : StageResult :=
  through2 x

def clzResult (x : UInt256) : StageResult :=
  through1 x

theorem clzPreFinal_n_le (x : UInt256) : (clzPreFinal x).n ≤ 254 := by
  simpa only [clzPreFinal] using through2_n_le x

/-- Execute the complete deployed `_clz` helper for an arbitrary input word. -/
theorem clzExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩
      (x :: ret :: tail) mem aw rdata acc k C) :
    let result := clzResult x
    RDx runtimeBytecode ee g s0 ret (UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  simpa only [clzResult] using through1Exact hret hdepth h

end Modexp.MultiLimbClz
